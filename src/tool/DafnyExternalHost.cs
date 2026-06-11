// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

using System;
using System.IO;
using System.Linq;
using MechUvl.Tool.Syntax;

namespace MechUvl.Tool;

internal static class DafnyExternalHost
{
    public static void Register()
    {
        UvlExternal.ParseImpl = Parse;
    }

    private static ExtLib.Option._Ioption<UVL__Syntax._IFeatureModel> Parse(
        Dafny.ISequence<Dafny.Rune> rootPath,
        ExtLib.Option._Ioption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> path)
    {
        try
        {
            var rootModelPath = FromDafnyString(rootPath);
            var targetPath = ResolvePath(rootModelPath, path);

            if (!File.Exists(targetPath))
            {
                return ExtLib.Option.option<UVL__Syntax._IFeatureModel>.create_None();
            }

            var model = UvlParser.ParseFile(targetPath);
            return ExtLib.Option.option<UVL__Syntax._IFeatureModel>.create_Some(model);
        }
        catch
        {
            return ExtLib.Option.option<UVL__Syntax._IFeatureModel>.create_None();
        }
    }

    private static string ResolvePath(
        string rootModelPath,
        ExtLib.Option._Ioption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> path)
    {
        if (path.is_None)
        {
            return rootModelPath;
        }

        var rootDirectory = Path.GetDirectoryName(rootModelPath) ?? string.Empty;
        var reference = path.dtor_value.Select(FromDafnyString).ToArray();
        var relativePath = Path.Combine(reference) + ".uvl";
        return Path.Combine(rootDirectory, relativePath);
    }

    private static string FromDafnyString(Dafny.ISequence<Dafny.Rune> value)
    {
        return value.ToVerbatimString(false);
    }
}
