// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

namespace MechUvl.Tool.Syntax;

internal static class UvlPreprocessor
{
    public static string NormalizeFile(string path)
    {
        var source = File.ReadAllText(path);
        return NormalizeText(source, path);
    }

    public static string NormalizeText(string text, string sourceName = "<memory>")
    {
        if (text.Contains("<INDENT>", StringComparison.Ordinal) ||
            text.Contains("<DEDENT>", StringComparison.Ordinal))
        {
            return text;
        }

        var normalizedText = text.Replace("\r\n", "\n", StringComparison.Ordinal)
            .Replace('\r', '\n');
        var withoutComments = StripComments(normalizedText, sourceName);
        var lines = withoutComments.Split('\n');

        var indentationStack = new List<int> { 0 };
        var output = new List<string>(lines.Length);

        for (var lineIndex = 0; lineIndex < lines.Length; lineIndex++)
        {
            var rawLine = lines[lineIndex];
            var prefixLength = CountIndentPrefixLength(rawLine);
            var prefix = rawLine[..prefixLength];
            var stripped = rawLine[prefixLength..];

            if (stripped.Length == 0)
            {
                continue;
            }

            var indentation = GetIndentationCount(prefix);
            var logicalMarkers = new StringBuilder();
            var currentIndentation = indentationStack[^1];

            if (indentation > currentIndentation)
            {
                indentationStack.Add(indentation);
                logicalMarkers.Append("<INDENT>");
            }
            else
            {
                while (indentation < indentationStack[^1])
                {
                    indentationStack.RemoveAt(indentationStack.Count - 1);
                    logicalMarkers.Append("<DEDENT>");
                }

                if (indentation != indentationStack[^1])
                {
                    throw new InvalidOperationException(
                        $"{sourceName}:{lineIndex + 1}: inconsistent indentation; got {indentation} spaces, expected one of [{string.Join(", ", indentationStack)}]");
                }
            }

            output.Add($"{logicalMarkers}{stripped}");
        }

        if (indentationStack.Count > 1)
        {
            output.Add(string.Concat(Repeat("<DEDENT>", indentationStack.Count - 1)));
        }

        return string.Join('\n', output);
    }

    private static string StripComments(string text, string sourceName)
    {
        var output = new StringBuilder(text.Length);
        var inSingleQuotedString = false;
        var inDoubleQuotedIdentifier = false;
        var inLineComment = false;
        var inBlockComment = false;

        for (var index = 0; index < text.Length; index++)
        {
            var character = text[index];
            var next = index + 1 < text.Length ? text[index + 1] : '\0';

            if (inLineComment)
            {
                if (character == '\n')
                {
                    output.Append(character);
                    inLineComment = false;
                }

                continue;
            }

            if (inBlockComment)
            {
                if (character == '\n')
                {
                    output.Append(character);
                    continue;
                }

                if (character == '*' && next == '/')
                {
                    inBlockComment = false;
                    index++;
                }

                continue;
            }

            if (inSingleQuotedString)
            {
                output.Append(character);
                if (character == '\'')
                {
                    inSingleQuotedString = false;
                }

                continue;
            }

            if (inDoubleQuotedIdentifier)
            {
                output.Append(character);
                if (character == '"')
                {
                    inDoubleQuotedIdentifier = false;
                }

                continue;
            }

            if (character == '\'')
            {
                inSingleQuotedString = true;
                output.Append(character);
                continue;
            }

            if (character == '"')
            {
                inDoubleQuotedIdentifier = true;
                output.Append(character);
                continue;
            }

            if (character == '/' && next == '/')
            {
                inLineComment = true;
                index++;
                continue;
            }

            if (character == '/' && next == '*')
            {
                inBlockComment = true;
                index++;
                continue;
            }

            output.Append(character);
        }

        if (inBlockComment)
        {
            throw new InvalidOperationException($"{sourceName}: unclosed block comment");
        }

        return output.ToString();
    }

    private static int CountIndentPrefixLength(string line)
    {
        var index = 0;
        while (index < line.Length && (line[index] == ' ' || line[index] == '\t'))
        {
            index++;
        }

        return index;
    }

    private static int GetIndentationCount(string spaces)
    {
        var count = 0;
        foreach (var character in spaces)
        {
            if (character == '\t')
            {
                count += 8 - (count % 8);
            }
            else
            {
                count++;
            }
        }

        return count;
    }

    private static IEnumerable<string> Repeat(string value, int count)
    {
        for (var i = 0; i < count; i++)
        {
            yield return value;
        }
    }
}
