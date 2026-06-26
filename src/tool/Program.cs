// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using MechUvl.Tool.Syntax;
using BuildEnvironment = UVL__BuildEnvironment;
using CheckErrors = UVL__Errors;
using LevelInference = UVL__LevelInference;
using ModelsBasicChecks = UVL__ModelsBasicChecks;
using ModelsTypingChecks = UVL__ModelsTypingChecks;
using UvlSyntax = UVL__Syntax;
using TypeInference = UVL__TypeInference;
using ModelPath = ExtLib.Option._Ioption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>;
using ReferenceParts = Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>;
using Variant = UVL__Variant;

namespace MechUvl.Tool;

internal enum CheckPhase
{
    Core,
    Levels,
    Typing,
    All,
}

internal enum LevelsInferScope
{
    Root,
    All,
}

internal enum LevelsInferFormat
{
    Summary,
    Includes,
}

internal static class Program
{
    private delegate bool SemanticCommandOptionHandler(
        string[] args,
        ref int index,
        string option,
        out string? errorMessage);

    private static string SemanticVariantUsage { get; } =
        "[--attribute-intro declared-only|local|local-scoped|global] " +
        "[--typed-feature-as-bool | --no-typed-feature-as-bool] " +
        "[--undef-constraint-as-true | --undef-constraint-as-false] " +
        "[--short-circuit | --no-short-circuit]";

    private static int Main(string[] args)
    {
        DafnyExternalHost.Register();

        if (args.Length == 0)
        {
            PrintUsage();
            return 0;
        }

        return args[0] switch
        {
            "check" => RunCheck(args),
            "fmt" => RunFormat(args),
            "levels" => RunLevels(args),
            "parse" => RunParse(args),
            "preprocess" => RunPreprocess(args),
            "version" or "--version" => PrintVersionAndExit(),
            "help" or "--help" or "-h" => PrintHelpAndExit(),
            _ => UnknownCommand(args[0]),
        };
    }

    private static int UnknownCommand(string command)
    {
        Console.Error.WriteLine($"error: unknown command '{command}'.");
        PrintUsage();
        return 1;
    }

    private static int PrintHelpAndExit()
    {
        PrintUsage();
        return 0;
    }

    private static int PrintVersionAndExit()
    {
        Console.WriteLine(GetVersion());
        return 0;
    }

    private static void PrintUsage()
    {
        Console.WriteLine("mech-uvl tool");
        Console.WriteLine();
        Console.WriteLine("Usage:");
        Console.WriteLine($"  mech-uvl check [--phase core|levels|typing|all] [--show-inferred-types] {SemanticVariantUsage} <root.uvl>");
        Console.WriteLine($"  mech-uvl levels infer [--scope root|all] [--format summary|includes] {SemanticVariantUsage} <root.uvl>");
        Console.WriteLine("  mech-uvl preprocess <file>...");
        Console.WriteLine("  mech-uvl parse <file>...");
        Console.WriteLine("  mech-uvl fmt [--indent-size <N> | --indent-style tabs] <file>...");
        Console.WriteLine("  mech-uvl --version");
    }

    private static string GetVersion()
    {
        var assembly = Assembly.GetExecutingAssembly();
        return assembly.GetCustomAttribute<AssemblyInformationalVersionAttribute>()?.InformationalVersion
            ?? assembly.GetName().Version?.ToString()
            ?? "unknown";
    }

    private static int RunPreprocess(string[] args)
    {
        if (!TryGetInputPaths(args, out var paths))
        {
            return 1;
        }

        var first = true;
        foreach (var path in paths)
        {
            try
            {
                var normalized = UvlPreprocessor.NormalizeFile(path);
                if (!first)
                {
                    Console.WriteLine();
                }

                Console.WriteLine($"== {path} ==");
                Console.WriteLine(normalized);
                first = false;
            }
            catch (Exception exception)
            {
                Console.Error.WriteLine($"error: {path}: {exception.Message}");
                return 1;
            }
        }

        return 0;
    }

    private static int RunParse(string[] args)
    {
        if (!TryGetInputPaths(args, out var paths))
        {
            return 1;
        }

        var first = true;
        foreach (var path in paths)
        {
            try
            {
                var tree = UvlParser.ParseFileAsString(path);
                if (!first)
                {
                    Console.WriteLine();
                }

                Console.WriteLine($"== {path} ==");
                Console.WriteLine(tree);
                first = false;
            }
            catch (Exception exception)
            {
                Console.Error.WriteLine($"error: {path}: {exception.Message}");
                return 1;
            }
        }

        return 0;
    }

    private static int RunCheck(string[] args)
    {
        if (!TryGetCheckArguments(args, out var phase, out var showInferredTypes, out var variant, out var rootPath, out var errorMessage))
        {
            Console.Error.WriteLine($"error: {errorMessage}");
            Console.Error.WriteLine($"usage: mech-uvl check [--phase core|levels|typing|all] [--show-inferred-types] {SemanticVariantUsage} <root.uvl>");
            return 1;
        }

        var buildResult = BuildEnvironment.__default.Build(ToDafnyString(rootPath));
        if (buildResult.is_BuildFailure)
        {
            Console.Error.WriteLine($"error: {FormatBuildError(buildResult.dtor_error)}");
            return 1;
        }

        var models = buildResult.dtor_env;
        var coreError = ModelsBasicChecks.__default.FirstCoreCheckError(models, variant);
        if (coreError.is_Some)
        {
            Console.Error.WriteLine($"error: {FormatCoreCheckError(coreError.dtor_value)}");
            return 1;
        }

        if (phase is CheckPhase.Levels or CheckPhase.All)
        {
            var levelError = ModelsBasicChecks.__default.FirstLevelCheckError(models);
            if (levelError.is_Some)
            {
                Console.Error.WriteLine($"error: {FormatLevelCheckError(levelError.dtor_value)}");
                return 1;
            }
        }

        if (phase is CheckPhase.Typing or CheckPhase.All)
        {
            var typingError = ModelsTypingChecks.__default.FirstTypingError(models, variant);
            if (typingError.is_Some)
            {
                Console.Error.WriteLine($"error: {FormatTypingError(typingError.dtor_value)}");
                return 1;
            }
        }

        Console.WriteLine("ok");
        if (showInferredTypes)
        {
            PrintInferredTypes(models, variant);
        }

        return 0;
    }

    private static int RunLevels(string[] args)
    {
        if (args.Length < 2)
        {
            Console.Error.WriteLine("error: missing levels subcommand.");
            Console.Error.WriteLine($"usage: mech-uvl levels infer [--scope root|all] [--format summary|includes] {SemanticVariantUsage} <root.uvl>");
            return 1;
        }

        return args[1] switch
        {
            "infer" => RunLevelsInfer(args),
            _ => UnknownLevelsCommand(args[1]),
        };
    }

    private static int UnknownLevelsCommand(string subcommand)
    {
        Console.Error.WriteLine($"error: unknown levels subcommand '{subcommand}'.");
        Console.Error.WriteLine($"usage: mech-uvl levels infer [--scope root|all] [--format summary|includes] {SemanticVariantUsage} <root.uvl>");
        return 1;
    }

    private static int RunLevelsInfer(string[] args)
    {
        if (!TryGetLevelsInferArguments(args, out var scope, out var format, out var variant, out var rootPath, out var errorMessage))
        {
            Console.Error.WriteLine($"error: {errorMessage}");
            Console.Error.WriteLine($"usage: mech-uvl levels infer [--scope root|all] [--format summary|includes] {SemanticVariantUsage} <root.uvl>");
            return 1;
        }

        var buildResult = BuildEnvironment.__default.Build(ToDafnyString(rootPath));
        if (buildResult.is_BuildFailure)
        {
            Console.Error.WriteLine($"error: {FormatBuildError(buildResult.dtor_error)}");
            return 1;
        }

        var inferenceScope = scope switch
        {
            LevelsInferScope.Root => LevelInference.LevelInferenceScope.create_Root(),
            LevelsInferScope.All => LevelInference.LevelInferenceScope.create_All(),
            _ => throw new InvalidOperationException($"unsupported inference scope: {scope}"),
        };

        var inferredModels = LevelInference.__default.InferLevelsForModels(buildResult.dtor_env, variant, inferenceScope);
        switch (format)
        {
            case LevelsInferFormat.Summary:
                PrintInferredLevelSummary(inferredModels);
                break;
            case LevelsInferFormat.Includes:
                PrintInferredLevelIncludes(inferredModels);
                break;
            default:
                throw new InvalidOperationException($"unsupported output format: {format}");
        }

        return 0;
    }

    private static int RunFormat(string[] args)
    {
        if (!TryGetFormatArguments(args, out var options, out var paths))
        {
            return 1;
        }

        var first = true;
        foreach (var path in paths)
        {
            try
            {
                var model = UvlParser.ParseFile(path);
                var prettyPrinted = UvlPrettyPrinter.Format(model, options);
                if (!first)
                {
                    Console.WriteLine();
                }

                Console.WriteLine($"== {path} ==");
                Console.WriteLine(prettyPrinted);
                first = false;
            }
            catch (Exception exception)
            {
                Console.Error.WriteLine($"error: {path}: {exception.Message}");
                return 1;
            }
        }

        return 0;
    }

    private static void PrintInferredLevelSummary(Dafny.IMap<ModelPath, UvlSyntax._IFeatureModel> models)
    {
        foreach (var current in SortedModelPaths(models))
        {
            var model = Dafny.Map<ModelPath, UvlSyntax._IFeatureModel>.Select(models, current);
            Console.WriteLine($"{FormatModelPath(current)}: {FormatLanguageLevels(model.dtor_includes)}");
        }
    }

    private static void PrintInferredLevelIncludes(Dafny.IMap<ModelPath, UvlSyntax._IFeatureModel> models)
    {
        var first = true;
        foreach (var current in SortedModelPaths(models))
        {
            var model = Dafny.Map<ModelPath, UvlSyntax._IFeatureModel>.Select(models, current);
            if (!first)
            {
                Console.WriteLine();
            }

            Console.WriteLine($"== {FormatModelPath(current)} ==");
            Console.WriteLine("include");
            foreach (var include in model.dtor_includes)
            {
                Console.WriteLine($"  {FormatLanguageLevel(include)}");
            }

            first = false;
        }
    }

    private static void PrintInferredTypes(Dafny.IMap<ModelPath, UvlSyntax._IFeatureModel> models, Variant._ISemVariant variant)
    {
        var printedAny = false;
        foreach (var current in SortedModelPaths(models))
        {
            var inferredTypes = TypeInference.__default.InferIntroTypesInModels(models, current, variant);
            if (!inferredTypes.is_Some)
            {
                throw new InvalidOperationException($"introduced-attribute inference unexpectedly failed for '{FormatModelPath(current)}' after a successful typing check.");
            }

            var introTypes = inferredTypes.dtor_value;
            if (!introTypes.Keys.Elements.Cast<ReferenceParts>().Any())
            {
                continue;
            }

            if (!printedAny)
            {
                Console.WriteLine("inferred types:");
            }

            Console.WriteLine($"{FormatModelPath(current)}:");
            foreach (var reference in SortedReferenceMapKeys(introTypes))
            {
                Console.WriteLine($"  {FormatReference(reference)}: {FormatFeatureType(Dafny.Map<ReferenceParts, UvlSyntax._IFeatureType>.Select(introTypes, reference))}");
            }

            printedAny = true;
        }

        if (!printedAny)
        {
            Console.WriteLine("inferred types: <none>");
        }
    }

    private static List<ModelPath> SortedModelPaths<TModel>(Dafny.IMap<ModelPath, TModel> models)
    {
        return models.Keys.Elements
            .Cast<ModelPath>()
            .OrderBy(path => path.is_None ? 0 : 1)
            .ThenBy(FormatModelPath, StringComparer.Ordinal)
            .ToList();
    }

    private static List<ReferenceParts> SortedReferenceMapKeys<TValue>(Dafny.IMap<ReferenceParts, TValue> map)
    {
        return map.Keys.Elements
            .Cast<ReferenceParts>()
            .OrderBy(FormatReference, StringComparer.Ordinal)
            .ToList();
    }

    private static bool TryGetFormatArguments(string[] args, out FormattingOptions options, out IReadOnlyList<string> paths)
    {
        options = FormattingOptions.Default;
        if (args.Length < 2)
        {
            Console.Error.WriteLine("error: missing input file.");
            PrintUsage();
            paths = Array.Empty<string>();
            return false;
        }

        var indentStyle = IndentStyle.Spaces;
        var indentSize = FormattingOptions.Default.IndentSize;
        var explicitIndentStyle = false;
        var explicitIndentSize = false;
        var resolved = new List<string>(args.Length - 1);

        for (var i = 1; i < args.Length; i++)
        {
            switch (args[i])
            {
                case "--indent-style":
                    if (i + 1 >= args.Length)
                    {
                        Console.Error.WriteLine("error: missing value for '--indent-style'.");
                        paths = Array.Empty<string>();
                        return false;
                    }

                    var styleValue = args[++i];
                    if (string.Equals(styleValue, "tabs", StringComparison.OrdinalIgnoreCase))
                    {
                        indentStyle = IndentStyle.Tabs;
                    }
                    else if (string.Equals(styleValue, "spaces", StringComparison.OrdinalIgnoreCase))
                    {
                        indentStyle = IndentStyle.Spaces;
                    }
                    else
                    {
                        Console.Error.WriteLine($"error: unsupported indentation style '{styleValue}'; expected 'spaces' or 'tabs'.");
                        paths = Array.Empty<string>();
                        return false;
                    }

                    explicitIndentStyle = true;
                    break;

                case "--indent-size":
                    if (i + 1 >= args.Length)
                    {
                        Console.Error.WriteLine("error: missing value for '--indent-size'.");
                        paths = Array.Empty<string>();
                        return false;
                    }

                    if (!int.TryParse(args[++i], out indentSize) || indentSize < 1)
                    {
                        Console.Error.WriteLine("error: '--indent-size' must be a positive integer.");
                        paths = Array.Empty<string>();
                        return false;
                    }

                    explicitIndentSize = true;
                    break;

                default:
                    resolved.Add(Path.GetFullPath(args[i]));
                    break;
            }
        }

        if (resolved.Count == 0)
        {
            Console.Error.WriteLine("error: missing input file.");
            PrintUsage();
            paths = Array.Empty<string>();
            return false;
        }

        if (explicitIndentStyle && indentStyle == IndentStyle.Tabs && explicitIndentSize)
        {
            Console.Error.WriteLine("error: '--indent-size' cannot be used with '--indent-style tabs'.");
            paths = Array.Empty<string>();
            return false;
        }

        if (!explicitIndentStyle && explicitIndentSize)
        {
            indentStyle = IndentStyle.Spaces;
        }

        options = new FormattingOptions(indentStyle, indentSize);
        paths = resolved;
        return true;
    }

    private static bool TryGetCheckArguments(
        string[] args,
        out CheckPhase phase,
        out bool showInferredTypes,
        out Variant._ISemVariant variant,
        out string rootPath,
        out string? errorMessage)
    {
        var requestedPhase = CheckPhase.All;
        var requestedShowInferredTypes = false;
        rootPath = string.Empty;
        var phaseSpecified = false;
        var showInferredTypesSpecified = false;

        bool HandleCheckOption(string[] tokens, ref int index, string option, out string? handlerError)
        {
            handlerError = null;
            switch (option)
            {
                case "--phase":
                    if (phaseSpecified)
                    {
                        handlerError = "option '--phase' was specified more than once.";
                        return true;
                    }

                    if (index + 1 >= tokens.Length)
                    {
                        handlerError = "missing value for '--phase'.";
                        return true;
                    }

                    var phaseValue = tokens[++index];
                    requestedPhase = phaseValue switch
                    {
                        "core" => CheckPhase.Core,
                        "levels" => CheckPhase.Levels,
                        "typing" => CheckPhase.Typing,
                        "all" => CheckPhase.All,
                        _ => requestedPhase,
                    };

                    if (phaseValue is not ("core" or "levels" or "typing" or "all"))
                    {
                        handlerError = $"unsupported value '{phaseValue}' for '--phase'; expected 'core', 'levels', 'typing', or 'all'.";
                    }
                    else
                    {
                        phaseSpecified = true;
                    }

                    return true;

                case "--show-inferred-types":
                    if (showInferredTypesSpecified)
                    {
                        handlerError = "option '--show-inferred-types' was specified more than once.";
                        return true;
                    }

                    requestedShowInferredTypes = true;
                    showInferredTypesSpecified = true;
                    return true;

                default:
                    return false;
            }
        }

        if (!TryParseSemanticCommandArguments(args, 1, HandleCheckOption, out variant, out var paths, out errorMessage))
        {
            phase = CheckPhase.All;
            showInferredTypes = false;
            return false;
        }

        phase = requestedPhase;
        showInferredTypes = requestedShowInferredTypes;
        if (showInferredTypes && phase is CheckPhase.Core or CheckPhase.Levels)
        {
            errorMessage = "'--show-inferred-types' requires '--phase typing' or '--phase all'.";
            rootPath = string.Empty;
            return false;
        }

        return TryGetSingleRootPath(paths, out rootPath, out errorMessage);
    }

    private static bool TryGetLevelsInferArguments(
        string[] args,
        out LevelsInferScope scope,
        out LevelsInferFormat format,
        out Variant._ISemVariant variant,
        out string rootPath,
        out string? errorMessage)
    {
        var requestedScope = LevelsInferScope.Root;
        var requestedFormat = LevelsInferFormat.Summary;
        rootPath = string.Empty;
        var scopeSpecified = false;
        var formatSpecified = false;

        bool HandleLevelsOption(string[] tokens, ref int index, string option, out string? handlerError)
        {
            handlerError = null;
            switch (option)
            {
                case "--scope":
                    if (scopeSpecified)
                    {
                        handlerError = "option '--scope' was specified more than once.";
                        return true;
                    }

                    if (index + 1 >= tokens.Length)
                    {
                        handlerError = "missing value for '--scope'.";
                        return true;
                    }

                    var scopeValue = tokens[++index];
                    if (scopeValue == "root")
                    {
                        requestedScope = LevelsInferScope.Root;
                    }
                    else if (scopeValue == "all")
                    {
                        requestedScope = LevelsInferScope.All;
                    }
                    else
                    {
                        handlerError = $"unsupported value '{scopeValue}' for '--scope'; expected 'root' or 'all'.";
                    }

                    if (handlerError is null)
                    {
                        scopeSpecified = true;
                    }

                    return true;

                case "--format":
                    if (formatSpecified)
                    {
                        handlerError = "option '--format' was specified more than once.";
                        return true;
                    }

                    if (index + 1 >= tokens.Length)
                    {
                        handlerError = "missing value for '--format'.";
                        return true;
                    }

                    var formatValue = tokens[++index];
                    if (formatValue == "summary")
                    {
                        requestedFormat = LevelsInferFormat.Summary;
                    }
                    else if (formatValue == "includes")
                    {
                        requestedFormat = LevelsInferFormat.Includes;
                    }
                    else
                    {
                        handlerError = $"unsupported value '{formatValue}' for '--format'; expected 'summary' or 'includes'.";
                    }

                    if (handlerError is null)
                    {
                        formatSpecified = true;
                    }

                    return true;

                default:
                    return false;
            }
        }

        if (!TryParseSemanticCommandArguments(args, 2, HandleLevelsOption, out variant, out var paths, out errorMessage))
        {
            scope = LevelsInferScope.Root;
            format = LevelsInferFormat.Summary;
            return false;
        }

        scope = requestedScope;
        format = requestedFormat;
        return TryGetSingleRootPath(paths, out rootPath, out errorMessage);
    }

    private static bool TryParseSemanticCommandArguments(
        string[] args,
        int startIndex,
        SemanticCommandOptionHandler handleCommandOption,
        out Variant._ISemVariant variant,
        out IReadOnlyList<string> paths,
        out string? errorMessage)
    {
        variant = Variant.SemVariant.Default();
        paths = Array.Empty<string>();
        errorMessage = null;

        Variant._IAttrIntro attrIntro = Variant.AttrIntro.create_DeclaredOnly();
        var attributeIntroSpecified = false;
        bool? typedFeatureAsBool = null;
        bool? undefConstraintAs = null;
        bool? shortCircuit = null;
        var resolved = new List<string>(Math.Max(0, args.Length - startIndex));

        for (var i = startIndex; i < args.Length; i++)
        {
            var option = args[i];
            switch (option)
            {
                case "--attribute-intro":
                    if (attributeIntroSpecified)
                    {
                        errorMessage = "option '--attribute-intro' was specified more than once.";
                        return false;
                    }

                    if (i + 1 >= args.Length)
                    {
                        errorMessage = "missing value for '--attribute-intro'.";
                        return false;
                    }

                    var attributeIntroValue = args[++i];
                    switch (attributeIntroValue)
                    {
                        case "declared-only":
                            attrIntro = Variant.AttrIntro.create_DeclaredOnly();
                            break;
                        case "local":
                            attrIntro = Variant.AttrIntro.create_LocalIntro(false);
                            break;
                        case "local-scoped":
                            attrIntro = Variant.AttrIntro.create_LocalIntro(true);
                            break;
                        case "global":
                            attrIntro = Variant.AttrIntro.create_GlobalIntro();
                            break;
                        default:
                            errorMessage =
                                $"unsupported value '{attributeIntroValue}' for '--attribute-intro'; " +
                                "expected 'declared-only', 'local', 'local-scoped', or 'global'.";
                            return false;
                    }

                    attributeIntroSpecified = true;
                    break;

                case "--typed-feature-as-bool":
                    if (typedFeatureAsBool.HasValue)
                    {
                        errorMessage = "typed-feature-as-bool was specified more than once.";
                        return false;
                    }

                    typedFeatureAsBool = true;
                    break;

                case "--no-typed-feature-as-bool":
                    if (typedFeatureAsBool.HasValue)
                    {
                        errorMessage = "typed-feature-as-bool was specified more than once.";
                        return false;
                    }

                    typedFeatureAsBool = false;
                    break;

                case "--undef-constraint-as-true":
                    if (undefConstraintAs.HasValue)
                    {
                        errorMessage = "undef-constraint-as was specified more than once.";
                        return false;
                    }

                    undefConstraintAs = true;
                    break;

                case "--undef-constraint-as-false":
                    if (undefConstraintAs.HasValue)
                    {
                        errorMessage = "undef-constraint-as was specified more than once.";
                        return false;
                    }

                    undefConstraintAs = false;
                    break;

                case "--short-circuit":
                    if (shortCircuit.HasValue)
                    {
                        errorMessage = "short-circuit was specified more than once.";
                        return false;
                    }

                    shortCircuit = true;
                    break;

                case "--no-short-circuit":
                    if (shortCircuit.HasValue)
                    {
                        errorMessage = "short-circuit was specified more than once.";
                        return false;
                    }

                    shortCircuit = false;
                    break;

                default:
                    if (handleCommandOption(args, ref i, option, out errorMessage))
                    {
                        if (errorMessage is not null)
                        {
                            return false;
                        }

                        break;
                    }

                    if (option.StartsWith("--", StringComparison.Ordinal))
                    {
                        errorMessage = $"unknown option '{option}'.";
                        return false;
                    }

                    resolved.Add(Path.GetFullPath(option));
                    break;
            }
        }

        if (resolved.Count == 0)
        {
            errorMessage = "missing input file.";
            return false;
        }

        variant = Variant.SemVariant.create_SemVariant(
            attrIntro,
            typedFeatureAsBool ?? false,
            undefConstraintAs ?? true,
            shortCircuit ?? false);

        if (!Variant.__default.WF__SemVariant(variant))
        {
            errorMessage =
                "invalid semantic variant: " +
                "'--undef-constraint-as-false' together with '--short-circuit' requires '--typed-feature-as-bool'.";
            variant = Variant.SemVariant.Default();
            return false;
        }

        paths = resolved;
        return true;
    }

    private static bool TryGetSingleRootPath(
        IReadOnlyList<string> paths,
        out string rootPath,
        out string? errorMessage)
    {
        if (paths.Count != 1)
        {
            rootPath = string.Empty;
            errorMessage = "expected exactly one root model file.";
            return false;
        }

        rootPath = paths[0];
        errorMessage = null;
        return true;
    }

    private static bool TryGetInputPaths(string[] args, out IReadOnlyList<string> paths)
    {
        if (args.Length < 2)
        {
            Console.Error.WriteLine("error: missing input file.");
            PrintUsage();
            paths = Array.Empty<string>();
            return false;
        }

        var resolved = new List<string>(args.Length - 1);
        for (var i = 1; i < args.Length; i++)
        {
            resolved.Add(Path.GetFullPath(args[i]));
        }

        paths = resolved;
        return true;
    }

    private static Dafny.ISequence<Dafny.Rune> ToDafnyString(string value)
    {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(value);
    }

    private static ModelPath RootModelPath()
    {
        return ExtLib.Option.option<ReferenceParts>.create_None();
    }

    private static string FormatBuildError(BuildEnvironment._IBuildError error)
    {
        if (error.is_RootParseFailed)
        {
            return "could not parse the root model";
        }

        if (error.is_ImportedModelParseFailed)
        {
            return $"could not parse imported model '{FormatModelPath(error.dtor_child)}' referenced as '{FormatReference(error.dtor_importPath)}' from '{FormatModelPath(error.dtor_parent)}'";
        }

        if (error.is_ImportCycle)
        {
            return $"import cycle involving '{FormatModelPath(error.dtor_path)}'";
        }

        return $"visible import path collision at '{FormatModelPath(error.dtor_path)}'";
    }

    private static string FormatCoreCheckError(CheckErrors._ICoreCheckError error)
    {
        var current = FormatModelPath(error.dtor_current);
        if (error.is_LocalModelWFError)
        {
            return $"{current}: {FormatLocalWFError(error.dtor_error)}";
        }

        if (error.is_InvalidFeatureTreeUse)
        {
            return $"{current}: invalid feature-tree use of '{FormatReference(error.dtor_reference)}'";
        }

        if (error.is_InvalidReferenceUse)
        {
            return $"{current}: invalid reference use of '{FormatReference(error.dtor_reference)}'";
        }

        return $"{current}: invalid aggregate use '{error.dtor_aggregate}'";
    }

    private static string FormatLocalWFError(CheckErrors._ILocalWFError error)
    {
        if (error.is_MissingRootFeature)
        {
            return "missing root feature";
        }

        if (error.is_InvalidCardinality)
        {
            return $"invalid cardinality {FormatCardinality(error.dtor_cardinality)}";
        }

        if (error.is_InvalidRecordAttribute)
        {
            return $"invalid record attribute '{FromDafnyString(error.dtor_attribute.dtor_key)}'";
        }

        if (error.is_DuplicateFeatureIdentifier)
        {
            return $"duplicate feature identifier '{FormatReference(error.dtor_reference)}'";
        }

        if (error.is_DuplicateAttributeName)
        {
            return $"duplicate attribute name '{FromDafnyString(error.dtor_key)}' on '{FormatReference(error.dtor_owner)}'";
        }

        if (error.is_DuplicateImportAlias)
        {
            return $"duplicate import alias '{FormatReference(error.dtor_qualifier)}'";
        }

        return $"import qualifiers '{FormatReference(error.dtor_left)}' and '{FormatReference(error.dtor_right)}' are not prefix-free";
    }

    private static string FormatCardinality(UvlSyntax._ICardinality cardinality)
    {
        return cardinality.dtor_upper switch
        {
            UvlSyntax.UpperBound_UnboundedUpper => $"[{cardinality.dtor_lower}..*]",
            UvlSyntax.UpperBound_FiniteUpper finite when finite.dtor_value == cardinality.dtor_lower =>
                $"[{cardinality.dtor_lower}]",
            UvlSyntax.UpperBound_FiniteUpper finite =>
                $"[{cardinality.dtor_lower}..{finite.dtor_value}]",
            _ => throw new InvalidOperationException($"unsupported upper bound: {cardinality.dtor_upper}"),
        };
    }

    private static string FormatLevelCheckError(CheckErrors._ILevelCheckError error)
    {
        var current = FormatModelPath(error.dtor_current);
        if (error.is_InvalidLevelDeclaration)
        {
            return $"{current}: invalid level declaration '{FormatLanguageLevel(error.dtor_level)}'";
        }

        if (error.is_InsufficientMajorLevel)
        {
            return $"{current}: insufficient major level; required {FormatMajorLevel(error.dtor_required)}, declared {FormatMajorLevel(error.dtor_declared)}";
        }

        return $"{current}: missing minor levels {FormatMinorLevels(error.dtor_missing)}";
    }

    private static string FormatTypingError(CheckErrors._ITypingError error)
    {
        var current = FormatModelPath(error.dtor_current);
        if (error.is_IllTypedModel)
        {
            return $"{current}: model is ill-typed";
        }

        if (error.is_IntroTypeInferenceContradiction)
        {
            return $"{current}: introduced-attribute type inference is contradictory ({FormatFeatureTypeDomains(error.dtor_domains)})";
        }

        return $"{current}: introduced-attribute type inference is underconstrained ({FormatFeatureTypeDomains(error.dtor_domains)})";
    }

    private static string FormatModelPath(ModelPath path)
    {
        return path.is_None ? "<root>" : FormatReference(path.dtor_value);
    }

    private static string FormatReference(ReferenceParts reference)
    {
        return string.Join(".", reference.Select(FromDafnyString));
    }

    private static string FormatFeatureTypeDomains(Dafny.IMap<ReferenceParts, Dafny.ISet<UvlSyntax._IFeatureType>> domains)
    {
        return string.Join(
            ", ",
            SortedReferenceMapKeys(domains)
                .Select(reference =>
                    $"{FormatReference(reference)} -> {FormatFeatureTypeDomain(Dafny.Map<ReferenceParts, Dafny.ISet<UvlSyntax._IFeatureType>>.Select(domains, reference))}"));
    }

    private static string FormatFeatureTypeDomain(Dafny.ISet<UvlSyntax._IFeatureType> domain)
    {
        return $"{{{string.Join(
            ", ",
            domain.Elements
                .Cast<UvlSyntax._IFeatureType>()
                .Select(FormatFeatureType)
                .OrderBy(name => name, StringComparer.Ordinal))}}}";
    }

    private static string FormatFeatureType(UvlSyntax._IFeatureType featureType)
    {
        return featureType switch
        {
            UvlSyntax.FeatureType_FTBoolean => "Boolean",
            UvlSyntax.FeatureType_FTInteger => "Integer",
            UvlSyntax.FeatureType_FTReal => "Real",
            UvlSyntax.FeatureType_FTString => "String",
            _ => throw new InvalidOperationException($"unsupported feature type: {featureType}"),
        };
    }

    private static string FormatLanguageLevels(Dafny.ISequence<UvlSyntax._ILanguageLevel> levels)
    {
        return levels.Any()
            ? string.Join(", ", levels.Select(FormatLanguageLevel))
            : "<none>";
    }

    private static string FormatLanguageLevel(UvlSyntax._ILanguageLevel level)
    {
        if (level.dtor_minor.is_None)
        {
            return FormatMajorLevel(level.dtor_major);
        }

        return $"{FormatMajorLevel(level.dtor_major)}.{FormatMinorLevelSelection(level.dtor_minor.dtor_value)}";
    }

    private static string FormatMajorLevel(UvlSyntax._IMajorLevel majorLevel)
    {
        return majorLevel switch
        {
            UvlSyntax.MajorLevel_BooleanLevel => "Boolean",
            UvlSyntax.MajorLevel_ArithmeticLevel => "Arithmetic",
            UvlSyntax.MajorLevel_TypeLevel => "Type",
            _ => throw new InvalidOperationException($"unsupported major level: {majorLevel}"),
        };
    }

    private static string FormatMinorLevelSelection(UvlSyntax._IMinorLevelSelection minorSelection)
    {
        return minorSelection switch
        {
            UvlSyntax.MinorLevelSelection_AnyMinorLevel => "*",
            _ => FormatMinorLevel(minorSelection.dtor_level),
        };
    }

    private static string FormatMinorLevels(Dafny.ISet<UvlSyntax._IMinorLevel> minorLevels)
    {
        return string.Join(
            ", ",
            minorLevels.Elements
                .Cast<UvlSyntax._IMinorLevel>()
                .Select(FormatMinorLevel)
                .OrderBy(name => name, StringComparer.Ordinal));
    }

    private static string FormatMinorLevel(UvlSyntax._IMinorLevel minorLevel)
    {
        return minorLevel switch
        {
            UvlSyntax.MinorLevel_GroupCardinalityLevel => "group-cardinality",
            UvlSyntax.MinorLevel_FeatureCardinalityLevel => "feature-cardinality",
            UvlSyntax.MinorLevel_AggregateFunctionLevel => "aggregate-function",
            UvlSyntax.MinorLevel_StringConstraintsLevel => "string-constraints",
            _ => throw new InvalidOperationException($"unsupported minor level: {minorLevel}"),
        };
    }

    private static string FromDafnyString(Dafny.ISequence<Dafny.Rune> value)
    {
        return value.ToVerbatimString(false);
    }
}
