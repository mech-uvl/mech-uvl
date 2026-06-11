// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

using Antlr4.Runtime;
using GeneratedUvlLexer = MechUvl.Tool.Generated.UVLLexer;
using GeneratedUvlParser = MechUvl.Tool.Generated.UVLParser;
using UvlSyntax = UVL__Syntax;

namespace MechUvl.Tool.Syntax;

internal static class UvlParser
{
    public static UvlSyntax._IFeatureModel ParseFile(string path)
    {
        var normalized = UvlPreprocessor.NormalizeFile(path);
        return UvlAstVisitor.Build(ParseNormalizedText(normalized).Tree);
    }

    public static string ParseFileAsString(string path)
    {
        return ParseFile(path).ToString() ?? string.Empty;
    }

    private static (GeneratedUvlParser Parser, GeneratedUvlParser.FeatureModelContext Tree)
        ParseNormalizedText(string normalizedText)
    {
        var input = new AntlrInputStream(normalizedText);
        var lexer = new GeneratedUvlLexer(input);
        lexer.RemoveErrorListeners();
        lexer.AddErrorListener(new UvlSyntaxErrorListener());

        var tokenStream = new CommonTokenStream(lexer);
        var parser = new GeneratedUvlParser(tokenStream);
        parser.RemoveErrorListeners();
        parser.AddErrorListener(new UvlSyntaxErrorListener());

        var tree = parser.featureModel();
        return (parser, tree);
    }
}
