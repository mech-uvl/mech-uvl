// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

using System;

internal static class DafnyExternalStub
{
    internal static ExtLib.Option._Ioption<TModel> UnregisteredParse<TModel>(
        Dafny.ISequence<Dafny.Rune> rootPath,
        ExtLib.Option._Ioption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> path)
    {
        throw new InvalidOperationException(
            "UvlExternal.Parse has not been registered by the host.");
    }
}

public static class UvlExternal
{
    public static Func<
        Dafny.ISequence<Dafny.Rune>,
        ExtLib.Option._Ioption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>>,
        ExtLib.Option._Ioption<UVL__Syntax._IFeatureModel>> ParseImpl { private get; set; } =
        DafnyExternalStub.UnregisteredParse<UVL__Syntax._IFeatureModel>;

    public static ExtLib.Option._Ioption<UVL__Syntax._IFeatureModel> Parse(
        Dafny.ISequence<Dafny.Rune> rootPath,
        ExtLib.Option._Ioption<Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>> path)
    {
        return ParseImpl(rootPath, path);
    }
}
