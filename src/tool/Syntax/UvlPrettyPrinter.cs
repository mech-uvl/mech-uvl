// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Text;
using UvlSyntax = UVL__Syntax;
using ReferenceParts = Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>;

namespace MechUvl.Tool.Syntax;

internal enum IndentStyle
{
    Spaces,
    Tabs,
}

internal readonly record struct FormattingOptions(IndentStyle IndentStyle, int IndentSize)
{
    public static FormattingOptions Default { get; } = new(IndentStyle.Spaces, 2);
}

internal static class UvlPrettyPrinter
{
    private static readonly HashSet<string> ReservedIdentifiers = new(StringComparer.Ordinal)
    {
        "include",
        "features",
        "imports",
        "namespace",
        "as",
        "constraint",
        "constraints",
        "cardinality",
        "String",
        "Boolean",
        "Integer",
        "RealType",
        "len",
        "sum",
        "avg",
        "floor",
        "ceil",
        "Type",
        "Arithmetic",
        "group-cardinality",
        "feature-cardinality",
        "aggregate-function",
        "string-constraints",
        "or",
        "alternative",
        "optional",
        "mandatory",
        "true",
        "false",
    };

    public static string Format(UvlSyntax._IFeatureModel model, FormattingOptions options)
    {
        var builder = new StringBuilder();
        var wroteSection = false;

        if (model.dtor_namespace.is_Some)
        {
            builder.Append("namespace ");
            builder.Append(FormatReference(model.dtor_namespace.dtor_value));
            builder.AppendLine();
            wroteSection = true;
        }

        if (model.dtor_includes.Any())
        {
            AppendSectionSeparator(builder, wroteSection);
            builder.AppendLine("include");
            foreach (var include in model.dtor_includes)
            {
                AppendIndentedLine(builder, options, 1, FormatLanguageLevel(include));
            }

            wroteSection = true;
        }

        if (model.dtor_imports.Any())
        {
            AppendSectionSeparator(builder, wroteSection);
            builder.AppendLine("imports");
            foreach (var importDecl in model.dtor_imports)
            {
                AppendIndentedLine(builder, options, 1, FormatImportDecl(importDecl));
            }

            wroteSection = true;
        }

        if (model.dtor_rootFeature.is_Some)
        {
            AppendSectionSeparator(builder, wroteSection);
            builder.AppendLine("features");
            AppendFeature(builder, options, model.dtor_rootFeature.dtor_value, 1);
            wroteSection = true;
        }

        if (model.dtor_constraints.Any())
        {
            AppendSectionSeparator(builder, wroteSection);
            builder.AppendLine("constraints");
            foreach (var constraint in model.dtor_constraints)
            {
                AppendIndentedLine(builder, options, 1, FormatConstraint(constraint));
            }
        }

        return builder.ToString().TrimEnd('\r', '\n');
    }

    public static string Format(UvlSyntax._IFeatureModel model)
    {
        return Format(model, FormattingOptions.Default);
    }

    private static void AppendSectionSeparator(StringBuilder builder, bool wroteSection)
    {
        if (wroteSection)
        {
            builder.AppendLine();
        }
    }

    private static void AppendFeature(StringBuilder builder, FormattingOptions options, UvlSyntax._IFeature feature, int indentLevel)
    {
        var line = new StringBuilder();
        if (feature.dtor_featureType.is_Some)
        {
            line.Append(FormatFeatureType(feature.dtor_featureType.dtor_value));
            line.Append(' ');
        }

        line.Append(FormatReference(feature.dtor_name));

        if (feature.dtor_cardinality.is_Some)
        {
            line.Append(" cardinality ");
            line.Append(FormatCardinality(feature.dtor_cardinality.dtor_value));
        }

        if (feature.dtor_attributes.Any())
        {
            line.Append(' ');
            line.Append(FormatAttributes(feature.dtor_attributes));
        }

        AppendIndentedLine(builder, options, indentLevel, line.ToString());

        foreach (var group in feature.dtor_groups)
        {
            AppendGroup(builder, options, group, indentLevel + 1);
        }
    }

    private static void AppendGroup(StringBuilder builder, FormattingOptions options, UvlSyntax._IGroup group, int indentLevel)
    {
        AppendIndentedLine(builder, options, indentLevel, FormatGroupKind(group.dtor_kind));
        foreach (var feature in group.dtor_features)
        {
            AppendFeature(builder, options, feature, indentLevel + 1);
        }
    }

    private static void AppendIndentedLine(StringBuilder builder, FormattingOptions options, int indentLevel, string text)
    {
        AppendIndent(builder, options, indentLevel);
        builder.Append(text);
        builder.AppendLine();
    }

    private static void AppendIndent(StringBuilder builder, FormattingOptions options, int indentLevel)
    {
        if (indentLevel <= 0)
        {
            return;
        }

        switch (options.IndentStyle)
        {
            case IndentStyle.Spaces:
                builder.Append(' ', indentLevel * options.IndentSize);
                break;
            case IndentStyle.Tabs:
                builder.Append('\t', indentLevel);
                break;
            default:
                throw new InvalidOperationException($"unsupported indentation style: {options.IndentStyle}");
        }
    }

    private static string FormatLanguageLevel(UvlSyntax._ILanguageLevel languageLevel)
    {
        var text = new StringBuilder(FormatMajorLevel(languageLevel.dtor_major));
        if (languageLevel.dtor_minor.is_Some)
        {
            text.Append('.');
            text.Append(FormatMinorLevelSelection(languageLevel.dtor_minor.dtor_value));
        }

        return text.ToString();
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

    private static string FormatMinorLevelSelection(UvlSyntax._IMinorLevelSelection minorLevelSelection)
    {
        return minorLevelSelection switch
        {
            UvlSyntax.MinorLevelSelection_AnyMinorLevel => "*",
            UvlSyntax.MinorLevelSelection_ExactMinorLevel exact => FormatMinorLevel(exact.dtor_level),
            _ => throw new InvalidOperationException($"unsupported minor level selection: {minorLevelSelection}"),
        };
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

    private static string FormatImportDecl(UvlSyntax._IImportDecl importDecl)
    {
        if (importDecl.dtor_alias.is_None)
        {
            return FormatReference(importDecl.dtor_importPath);
        }

        return $"{FormatReference(importDecl.dtor_importPath)} as {FormatReference(importDecl.dtor_alias.dtor_value)}";
    }

    private static string FormatFeatureType(UvlSyntax._IFeatureType featureType)
    {
        return featureType switch
        {
            UvlSyntax.FeatureType_FTString => "String",
            UvlSyntax.FeatureType_FTInteger => "Integer",
            UvlSyntax.FeatureType_FTBoolean => "Boolean",
            UvlSyntax.FeatureType_FTReal => "RealType",
            _ => throw new InvalidOperationException($"unsupported feature type: {featureType}"),
        };
    }

    private static string FormatGroupKind(UvlSyntax._IGroupKind groupKind)
    {
        return groupKind switch
        {
            UvlSyntax.GroupKind_OrGroup => "or",
            UvlSyntax.GroupKind_AlternativeGroup => "alternative",
            UvlSyntax.GroupKind_OptionalGroup => "optional",
            UvlSyntax.GroupKind_MandatoryGroup => "mandatory",
            UvlSyntax.GroupKind_CardinalityGroup cardinalityGroup => FormatCardinality(cardinalityGroup.dtor_cardinality),
            _ => throw new InvalidOperationException($"unsupported group kind: {groupKind}"),
        };
    }

    private static string FormatCardinality(UvlSyntax._ICardinality cardinality)
    {
        return cardinality.dtor_upper switch
        {
            UvlSyntax.UpperBound_UnboundedUpper => $"[{FormatInteger(cardinality.dtor_lower)}..*]",
            UvlSyntax.UpperBound_FiniteUpper finite when finite.dtor_value == cardinality.dtor_lower =>
                $"[{FormatInteger(cardinality.dtor_lower)}]",
            UvlSyntax.UpperBound_FiniteUpper finite =>
                $"[{FormatInteger(cardinality.dtor_lower)}..{FormatInteger(finite.dtor_value)}]",
            _ => throw new InvalidOperationException($"unsupported upper bound: {cardinality.dtor_upper}"),
        };
    }

    private static string FormatAttributes(Dafny.ISequence<UvlSyntax._IAttribute> attributes)
    {
        return $"{{{string.Join(", ", attributes.Select(FormatAttribute))}}}";
    }

    private static string FormatNestedAttributes(Dafny.ISequence<UvlSyntax._IAttributeDef> attributes)
    {
        return $"{{{string.Join(", ", attributes.Select(FormatAttributeDef))}}}";
    }

    private static string FormatAttribute(UvlSyntax._IAttribute attribute)
    {
        return attribute switch
        {
            UvlSyntax.Attribute_AValue valueAttribute =>
                FormatAttributeDef(valueAttribute.dtor_attribute),
            UvlSyntax.Attribute_ASingleConstraint single =>
                $"constraint {FormatConstraint(single.dtor_constraint)}",
            UvlSyntax.Attribute_AListConstraints list =>
                $"constraints [{string.Join(", ", list.dtor_constraints.Select(constraint => FormatConstraint(constraint)))}]",
            _ => throw new InvalidOperationException($"unsupported attribute: {attribute}"),
        };
    }

    private static string FormatAttributeDef(UvlSyntax._IAttributeDef attribute)
    {
        return attribute.dtor_value switch
        {
            ExtLib.Option.option_Some<UvlSyntax._IAttributeValue> some =>
                $"{FormatIdentifier(attribute.dtor_key)} {FormatValue(some.dtor_value)}",
            ExtLib.Option.option_None<UvlSyntax._IAttributeValue> =>
                FormatIdentifier(attribute.dtor_key),
            _ => throw new InvalidOperationException($"unsupported attribute value option: {attribute.dtor_value}"),
        };
    }

    private static string FormatValue(UvlSyntax._IAttributeValue value)
    {
        return value switch
        {
            UvlSyntax.AttributeValue_VBool booleanValue => booleanValue.dtor_value ? "true" : "false",
            UvlSyntax.AttributeValue_VInt intValue => FormatInteger(intValue.dtor_intValue),
            UvlSyntax.AttributeValue_VFloat floatValue => FormatReal(floatValue.dtor_realValue),
            UvlSyntax.AttributeValue_VString stringValue => FormatString(FromDafnyString(stringValue.dtor_stringValue)),
            UvlSyntax.AttributeValue_VRecord attributeSet => FormatNestedAttributes(attributeSet.dtor_attributes),
            UvlSyntax.AttributeValue_VVector vector => $"[{string.Join(", ", vector.dtor_elements.Select(FormatValue))}]",
            _ => throw new InvalidOperationException($"unsupported value: {value}"),
        };
    }

    private static string FormatConstraint(UvlSyntax._IConstraint constraint, int parentPrecedence = -1, bool isRightChild = false)
    {
        string rendered;
        int precedence;

        switch (constraint)
        {
            case UvlSyntax.Constraint_CRef literal:
                rendered = FormatReference(literal.dtor_reference);
                precedence = 4;
                break;
            case UvlSyntax.Constraint_CEquation equationConstraint:
                rendered = FormatEquation(equationConstraint.dtor_equation);
                precedence = 4;
                break;
            case UvlSyntax.Constraint_CNot notConstraint:
                precedence = 3;
                rendered = "!" + FormatConstraint(notConstraint.dtor_inner, precedence, false);
                break;
            case UvlSyntax.Constraint_CBinop binaryConstraint:
                precedence = ConstraintPrecedence(binaryConstraint.dtor_op);
                rendered =
                    $"{FormatConstraint(binaryConstraint.dtor_left, precedence, false)} " +
                    $"{FormatConstraintOperator(binaryConstraint.dtor_op)} " +
                    $"{FormatConstraint(binaryConstraint.dtor_right, precedence, true)}";
                break;
            default:
                throw new InvalidOperationException($"unsupported constraint: {constraint}");
        }

        if (precedence < parentPrecedence || (isRightChild && precedence == parentPrecedence && constraint is UvlSyntax.Constraint_CBinop))
        {
            return $"({rendered})";
        }

        return rendered;
    }

    private static int ConstraintPrecedence(UvlSyntax._IConstraintOp op)
    {
        return op switch
        {
            UvlSyntax.ConstraintOp_And => 2,
            UvlSyntax.ConstraintOp_Or => 1,
            UvlSyntax.ConstraintOp_Imply => 0,
            UvlSyntax.ConstraintOp_Equiv => -1,
            _ => throw new InvalidOperationException($"unsupported constraint operator: {op}"),
        };
    }

    private static string FormatConstraintOperator(UvlSyntax._IConstraintOp op)
    {
        return op switch
        {
            UvlSyntax.ConstraintOp_And => "&",
            UvlSyntax.ConstraintOp_Or => "|",
            UvlSyntax.ConstraintOp_Imply => "=>",
            UvlSyntax.ConstraintOp_Equiv => "<=>",
            _ => throw new InvalidOperationException($"unsupported constraint operator: {op}"),
        };
    }

    private static string FormatEquation(UvlSyntax._IEquation equation)
    {
        return
            $"{FormatExpression(equation.dtor_left)} " +
            $"{FormatComparisonOperator(equation.dtor_op)} " +
            $"{FormatExpression(equation.dtor_right)}";
    }

    private static string FormatComparisonOperator(UvlSyntax._IComparisonOp op)
    {
        return op switch
        {
            UvlSyntax.ComparisonOp_Eq => "==",
            UvlSyntax.ComparisonOp_Lt => "<",
            UvlSyntax.ComparisonOp_Gt => ">",
            UvlSyntax.ComparisonOp_Le => "<=",
            UvlSyntax.ComparisonOp_Ge => ">=",
            UvlSyntax.ComparisonOp_Neq => "!=",
            _ => throw new InvalidOperationException($"unsupported comparison operator: {op}"),
        };
    }

    private static string FormatExpression(UvlSyntax._IExpression expression, int parentPrecedence = -1, bool isRightChild = false)
    {
        string rendered;
        int precedence;

        switch (expression)
        {
            case UvlSyntax.Expression_EInt integerLiteral:
                rendered = FormatInteger(integerLiteral.dtor_intValue);
                precedence = 2;
                break;
            case UvlSyntax.Expression_EFloat Float:
                rendered = FormatReal(Float.dtor_realValue);
                precedence = 2;
                break;
            case UvlSyntax.Expression_EString String:
                rendered = FormatString(FromDafnyString(String.dtor_strinValue));
                precedence = 2;
                break;
            case UvlSyntax.Expression_ERef referenceExpression:
                rendered = FormatReference(referenceExpression.dtor_reference);
                precedence = 2;
                break;
            case UvlSyntax.Expression_EAggr aggregateExpression:
                rendered = FormatAggregateFunction(aggregateExpression.dtor_aggregate);
                precedence = 2;
                break;
            case UvlSyntax.Expression_EBinop binaryExpression:
                precedence = ArithmeticPrecedence(binaryExpression.dtor_op);
                rendered =
                    $"{FormatExpression(binaryExpression.dtor_left, precedence, false)} " +
                    $"{FormatArithmeticOperator(binaryExpression.dtor_op)} " +
                    $"{FormatExpression(binaryExpression.dtor_right, precedence, true)}";
                break;
            default:
                throw new InvalidOperationException($"unsupported expression: {expression}");
        }

        if (precedence < parentPrecedence || (isRightChild && precedence == parentPrecedence && expression is UvlSyntax.Expression_EBinop))
        {
            return $"({rendered})";
        }

        return rendered;
    }

    private static int ArithmeticPrecedence(UvlSyntax._IArithmeticOp op)
    {
        return op switch
        {
            UvlSyntax.ArithmeticOp_Mul => 1,
            UvlSyntax.ArithmeticOp_Div => 1,
            UvlSyntax.ArithmeticOp_Add => 0,
            UvlSyntax.ArithmeticOp_Sub => 0,
            _ => throw new InvalidOperationException($"unsupported arithmetic operator: {op}"),
        };
    }

    private static string FormatArithmeticOperator(UvlSyntax._IArithmeticOp op)
    {
        return op switch
        {
            UvlSyntax.ArithmeticOp_Add => "+",
            UvlSyntax.ArithmeticOp_Sub => "-",
            UvlSyntax.ArithmeticOp_Mul => "*",
            UvlSyntax.ArithmeticOp_Div => "/",
            _ => throw new InvalidOperationException($"unsupported arithmetic operator: {op}"),
        };
    }

    private static string FormatAggregateFunction(UvlSyntax._IAggregateFunction aggregateFunction)
    {
        return aggregateFunction switch
        {
            UvlSyntax.AggregateFunction_Sum sum => FormatScopedAggregate("sum", sum.dtor_scope, sum.dtor_target),
            UvlSyntax.AggregateFunction_Avg avg => FormatScopedAggregate("avg", avg.dtor_scope, avg.dtor_target),
            UvlSyntax.AggregateFunction_Len len => $"len({FormatReference(len.dtor_target)})",
            UvlSyntax.AggregateFunction_Floor floor => $"floor({FormatReference(floor.dtor_target)})",
            UvlSyntax.AggregateFunction_Ceil  ceil => $"ceil({FormatReference(ceil.dtor_target)})",
            _ => throw new InvalidOperationException($"unsupported aggregate function: {aggregateFunction}"),
        };
    }

    private static string FormatScopedAggregate(string name, ExtLib.Option._Ioption<ReferenceParts> scope, ReferenceParts target)
    {
        if (scope.is_Some)
        {
            return $"{name}({FormatReference(target)}, {FormatReference(scope.dtor_value)})";
        }

        return $"{name}({FormatReference(target)})";
    }

    private static string FormatReference(ReferenceParts reference)
    {
        return string.Join(".", reference.Select(part => FormatIdentifier(FromDafnyString(part))));
    }

    private static string FormatIdentifier(Dafny.ISequence<Dafny.Rune> identifier)
    {
        return FormatIdentifier(FromDafnyString(identifier));
    }

    private static string FormatIdentifier(string identifier)
    {
        if (CanUseStrictIdentifier(identifier))
        {
            return identifier;
        }

        if (identifier.Contains('.', StringComparison.Ordinal) ||
            identifier.Contains('"', StringComparison.Ordinal) ||
            identifier.Contains('\r') ||
            identifier.Contains('\n'))
        {
            throw new InvalidOperationException($"identifier cannot be rendered in UVL concrete syntax: {identifier}");
        }

        return $"\"{identifier}\"";
    }

    private static bool CanUseStrictIdentifier(string identifier)
    {
        if (identifier.Length == 0 || ReservedIdentifiers.Contains(identifier))
        {
            return false;
        }

        if (!IsStrictIdentifierHead(identifier[0]))
        {
            return false;
        }

        for (var index = 1; index < identifier.Length; index++)
        {
            if (!IsStrictIdentifierTail(identifier[index]))
            {
                return false;
            }
        }

        return true;
    }

    private static bool IsStrictIdentifierHead(char character)
    {
        return character is >= 'a' and <= 'z' or >= 'A' and <= 'Z';
    }

    private static bool IsStrictIdentifierTail(char character)
    {
        return IsStrictIdentifierHead(character)
            || character is >= '0' and <= '9'
            || character is '_' or '#' or '§' or '%' or '?' or '\\' or '\'' or 'ä' or 'ü' or 'ö' or 'ß' or ';';
    }

    private static string FormatString(string value)
    {
        if (value.Contains('\'') || value.Contains('\r') || value.Contains('\n'))
        {
            throw new InvalidOperationException($"string literal cannot be rendered in UVL concrete syntax: {value}");
        }

        return $"'{value}'";
    }

    private static string FormatInteger(BigInteger value)
    {
        return value.ToString(CultureInfo.InvariantCulture);
    }

    private static string FormatReal(Dafny.BigRational value)
    {
        if (value.num.IsZero || value.den.IsOne)
        {
            return $"{value.num.ToString(CultureInfo.InvariantCulture)}.0";
        }

        if (!Dafny.BigRational.DividesAPowerOf10(value.den, out var factor, out var log10))
        {
            throw new InvalidOperationException($"real literal is not representable as a finite decimal: {value}");
        }

        var scaledNumerator = value.num * factor;
        var digits = BigInteger.Abs(scaledNumerator).ToString(CultureInfo.InvariantCulture);
        var sign = scaledNumerator.Sign < 0 ? "-" : string.Empty;

        if (log10 < digits.Length)
        {
            var split = digits.Length - log10;
            return $"{sign}{digits[..split]}.{digits[split..]}";
        }

        return $"{sign}0.{new string('0', log10 - digits.Length)}{digits}";
    }

    private static string FromDafnyString(Dafny.ISequence<Dafny.Rune> value)
    {
        return value.ToVerbatimString(false);
    }
}
