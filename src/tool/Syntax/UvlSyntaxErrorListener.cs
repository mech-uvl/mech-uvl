// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

using System;
using System.IO;
using Antlr4.Runtime;

namespace MechUvl.Tool.Syntax;

internal sealed class UvlSyntaxErrorListener : IAntlrErrorListener<int>, IAntlrErrorListener<IToken>
{
    public void SyntaxError(
        TextWriter output,
        IRecognizer recognizer,
        int offendingSymbol,
        int line,
        int charPositionInLine,
        string msg,
        RecognitionException exception)
    {
        ThrowSyntaxError(line, charPositionInLine, msg);
    }

    public void SyntaxError(
        TextWriter output,
        IRecognizer recognizer,
        IToken offendingSymbol,
        int line,
        int charPositionInLine,
        string msg,
        RecognitionException exception)
    {
        ThrowSyntaxError(line, charPositionInLine, msg);
    }

    private static void ThrowSyntaxError(int line, int charPositionInLine, string msg)
    {
        throw new InvalidOperationException($"syntax error at {line}:{charPositionInLine + 1}: {msg}");
    }
}
