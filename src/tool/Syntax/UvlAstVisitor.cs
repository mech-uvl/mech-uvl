// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

using System;
using System.Globalization;
using System.Linq;
using System.Numerics;
using Antlr4.Runtime;
using GeneratedUvlParser = MechUvl.Tool.Generated.UVLParser;
using GeneratedUvlParserBaseVisitor = MechUvl.Tool.Generated.UVLParserBaseVisitor<object?>;
using UvlSyntax = UVL__Syntax;
using ReferenceParts = Dafny.ISequence<Dafny.ISequence<Dafny.Rune>>;

namespace MechUvl.Tool.Syntax;

internal sealed class UvlAstVisitor : GeneratedUvlParserBaseVisitor
{
    public static UvlSyntax._IFeatureModel Build(GeneratedUvlParser.FeatureModelContext context)
    {
        var visitor = new UvlAstVisitor();
        return Expect<UvlSyntax._IFeatureModel>(visitor.Visit(context), context);
    }

    public override object VisitFeatureModel(GeneratedUvlParser.FeatureModelContext context)
    {
        var namespaceValue = context.@namespace() is null
            ? None<ReferenceParts>()
            : Some(Expect<ReferenceParts>(Visit(context.@namespace()), context.@namespace()));
        var includes = context.includes() is null
            ? Empty<UvlSyntax._ILanguageLevel>()
            : Expect<Dafny.ISequence<UvlSyntax._ILanguageLevel>>(Visit(context.includes()), context.includes());
        var imports = context.imports() is null
            ? Empty<UvlSyntax._IImportDecl>()
            : Expect<Dafny.ISequence<UvlSyntax._IImportDecl>>(Visit(context.imports()), context.imports());
        var rootFeature = context.features() is null
            ? None<UvlSyntax._IFeature>()
            : Some(Expect<UvlSyntax._IFeature>(Visit(context.features()), context.features()));
        var constraints = context.constraints() is null
            ? Empty<UvlSyntax._IConstraint>()
            : Expect<Dafny.ISequence<UvlSyntax._IConstraint>>(Visit(context.constraints()), context.constraints());

        return UvlSyntax.FeatureModel.create_MkFeatureModel(namespaceValue, includes, imports, rootFeature, constraints);
    }

    public override object VisitIncludes(GeneratedUvlParser.IncludesContext context)
    {
        return Sequence(context.includeLine().Select(line => Expect<UvlSyntax._ILanguageLevel>(Visit(line), line)));
    }

    public override object VisitIncludeLine(GeneratedUvlParser.IncludeLineContext context)
    {
        return Expect<UvlSyntax._ILanguageLevel>(Visit(context.languageLevel()), context.languageLevel());
    }

    public override object VisitNamespace(GeneratedUvlParser.NamespaceContext context)
    {
        return Expect<ReferenceParts>(Visit(context.reference()), context.reference());
    }

    public override object VisitImports(GeneratedUvlParser.ImportsContext context)
    {
        return Sequence(context.importLine().Select(line => Expect<UvlSyntax._IImportDecl>(Visit(line), line)));
    }

    public override object VisitImportLine(GeneratedUvlParser.ImportLineContext context)
    {
        var namespaceValue = Expect<ReferenceParts>(Visit(context.ns), context.ns);
        var alias = context.alias is null
            ? None<ReferenceParts>()
            : Some(Expect<ReferenceParts>(Visit(context.alias), context.alias));

        return UvlSyntax.ImportDecl.create_MkImportDecl(namespaceValue, alias);
    }

    public override object VisitFeatures(GeneratedUvlParser.FeaturesContext context)
    {
        return Expect<UvlSyntax._IFeature>(Visit(context.feature()), context.feature());
    }

    public override object VisitOrGroup(GeneratedUvlParser.OrGroupContext context)
    {
        return UvlSyntax.Group.create_MkGroup(
            UvlSyntax.GroupKind.create_OrGroup(),
            Expect<Dafny.ISequence<UvlSyntax._IFeature>>(Visit(context.groupSpec()), context.groupSpec()));
    }

    public override object VisitAlternativeGroup(GeneratedUvlParser.AlternativeGroupContext context)
    {
        return UvlSyntax.Group.create_MkGroup(
            UvlSyntax.GroupKind.create_AlternativeGroup(),
            Expect<Dafny.ISequence<UvlSyntax._IFeature>>(Visit(context.groupSpec()), context.groupSpec()));
    }

    public override object VisitOptionalGroup(GeneratedUvlParser.OptionalGroupContext context)
    {
        return UvlSyntax.Group.create_MkGroup(
            UvlSyntax.GroupKind.create_OptionalGroup(),
            Expect<Dafny.ISequence<UvlSyntax._IFeature>>(Visit(context.groupSpec()), context.groupSpec()));
    }

    public override object VisitMandatoryGroup(GeneratedUvlParser.MandatoryGroupContext context)
    {
        return UvlSyntax.Group.create_MkGroup(
            UvlSyntax.GroupKind.create_MandatoryGroup(),
            Expect<Dafny.ISequence<UvlSyntax._IFeature>>(Visit(context.groupSpec()), context.groupSpec()));
    }

    public override object VisitCardinalityGroup(GeneratedUvlParser.CardinalityGroupContext context)
    {
        return UvlSyntax.Group.create_MkGroup(
            UvlSyntax.GroupKind.create_CardinalityGroup(ParseCardinality(context.CARDINALITY().GetText(), context)),
            Expect<Dafny.ISequence<UvlSyntax._IFeature>>(Visit(context.groupSpec()), context.groupSpec()));
    }

    public override object VisitGroupSpec(GeneratedUvlParser.GroupSpecContext context)
    {
        return Sequence(context.feature().Select(feature => Expect<UvlSyntax._IFeature>(Visit(feature), feature)));
    }

    public override object VisitFeature(GeneratedUvlParser.FeatureContext context)
    {
        var featureType = context.featureType() is null
            ? None<UvlSyntax._IFeatureType>()
            : Some(Expect<UvlSyntax._IFeatureType>(Visit(context.featureType()), context.featureType()));
        var name = Expect<ReferenceParts>(Visit(context.reference()), context.reference());
        var cardinality = context.featureCardinality() is null
            ? None<UvlSyntax._ICardinality>()
            : Some(Expect<UvlSyntax._ICardinality>(Visit(context.featureCardinality()), context.featureCardinality()));
        var attributes = context.attributes() is null
            ? Empty<UvlSyntax._IAttribute>()
            : Expect<Dafny.ISequence<UvlSyntax._IAttribute>>(Visit(context.attributes()), context.attributes());
        var groups = Sequence(context.group().Select(group => Expect<UvlSyntax._IGroup>(Visit(group), group)));

        return UvlSyntax.Feature.create_MkFeature(featureType, name, cardinality, attributes, groups);
    }

    public override object VisitFeatureCardinality(GeneratedUvlParser.FeatureCardinalityContext context)
    {
        return ParseCardinality(context.CARDINALITY().GetText(), context);
    }

    public override object VisitAttributes(GeneratedUvlParser.AttributesContext context)
    {
        return Sequence(context.attribute().Select(attribute => Expect<UvlSyntax._IAttribute>(Visit(attribute), attribute)));
    }

    public override object VisitAttribute(GeneratedUvlParser.AttributeContext context)
    {
        if (context.valueAttribute() is not null)
        {
            return Expect<UvlSyntax._IAttribute>(Visit(context.valueAttribute()), context.valueAttribute());
        }

        return Expect<UvlSyntax._IAttribute>(Visit(context.constraintAttribute()), context.constraintAttribute());
    }

    public override object VisitValueAttribute(GeneratedUvlParser.ValueAttributeContext context)
    {
        return UvlSyntax.Attribute.create_AValue(BuildAttributeDef(context));
    }

    public override object VisitKey(GeneratedUvlParser.KeyContext context)
    {
        return Expect<Dafny.ISequence<Dafny.Rune>>(Visit(context.id()), context.id());
    }

    public override object VisitValue(GeneratedUvlParser.ValueContext context)
    {
        if (context.BOOLEAN() is not null)
        {
            return UvlSyntax.AttributeValue.create_VBool(ParseBoolean(context.BOOLEAN().GetText(), context));
        }

        if (context.FLOAT() is not null)
        {
            return UvlSyntax.AttributeValue.create_VFloat(ParseReal(context.FLOAT().GetText(), context));
        }

        if (context.INTEGER() is not null)
        {
            return UvlSyntax.AttributeValue.create_VInt(ParseInteger(context.INTEGER().GetText(), context));
        }

        if (context.STRING() is not null)
        {
            return UvlSyntax.AttributeValue.create_VString(ToDafnyString(UnquoteSingleQuoted(context.STRING().GetText())));
        }

        if (context.attributes() is not null)
        {
            return UvlSyntax.AttributeValue.create_VRecord(
                BuildNestedAttributeDefs(context.attributes()));
        }

        return UvlSyntax.AttributeValue.create_VVector(
            Expect<Dafny.ISequence<UvlSyntax._IAttributeValue>>(Visit(context.vector()), context.vector()));
    }

    public override object VisitVector(GeneratedUvlParser.VectorContext context)
    {
        return Sequence(context.value().Select(value => Expect<UvlSyntax._IAttributeValue>(Visit(value), value)));
    }

    public override object VisitSingleConstraintAttribute(GeneratedUvlParser.SingleConstraintAttributeContext context)
    {
        return UvlSyntax.Attribute.create_ASingleConstraint(
            Expect<UvlSyntax._IConstraint>(Visit(context.constraint()), context.constraint()));
    }

    public override object VisitListConstraintAttribute(GeneratedUvlParser.ListConstraintAttributeContext context)
    {
        return UvlSyntax.Attribute.create_AListConstraints(
            Expect<Dafny.ISequence<UvlSyntax._IConstraint>>(Visit(context.constraintList()), context.constraintList()));
    }

    public override object VisitConstraintList(GeneratedUvlParser.ConstraintListContext context)
    {
        return Sequence(context.constraint().Select(constraint => Expect<UvlSyntax._IConstraint>(Visit(constraint), constraint)));
    }

    public override object VisitConstraints(GeneratedUvlParser.ConstraintsContext context)
    {
        return Sequence(context.constraintLine().Select(line => Expect<UvlSyntax._IConstraint>(Visit(line), line)));
    }

    public override object VisitConstraintLine(GeneratedUvlParser.ConstraintLineContext context)
    {
        return Expect<UvlSyntax._IConstraint>(Visit(context.constraint()), context.constraint());
    }

    public override object VisitEquationConstraint(GeneratedUvlParser.EquationConstraintContext context)
    {
        return UvlSyntax.Constraint.create_CEquation(
            Expect<UvlSyntax._IEquation>(Visit(context.equation()), context.equation()));
    }

    public override object VisitLiteralConstraint(GeneratedUvlParser.LiteralConstraintContext context)
    {
        return UvlSyntax.Constraint.create_CRef(
            Expect<ReferenceParts>(Visit(context.reference()), context.reference()));
    }

    public override object VisitParenthesisConstraint(GeneratedUvlParser.ParenthesisConstraintContext context)
    {
        return Expect<UvlSyntax._IConstraint>(Visit(context.constraint()), context.constraint());
    }

    public override object VisitNotConstraint(GeneratedUvlParser.NotConstraintContext context)
    {
        return UvlSyntax.Constraint.create_CNot(
            Expect<UvlSyntax._IConstraint>(Visit(context.constraint()), context.constraint()));
    }

    public override object VisitAndConstraint(GeneratedUvlParser.AndConstraintContext context)
    {
        return UvlSyntax.Constraint.create_CBinop(
            Expect<UvlSyntax._IConstraint>(Visit(context.constraint(0)), context.constraint(0)),
            UvlSyntax.ConstraintOp.create_And(),
            Expect<UvlSyntax._IConstraint>(Visit(context.constraint(1)), context.constraint(1)));
    }

    public override object VisitOrConstraint(GeneratedUvlParser.OrConstraintContext context)
    {
        return UvlSyntax.Constraint.create_CBinop(
            Expect<UvlSyntax._IConstraint>(Visit(context.constraint(0)), context.constraint(0)),
            UvlSyntax.ConstraintOp.create_Or(),
            Expect<UvlSyntax._IConstraint>(Visit(context.constraint(1)), context.constraint(1)));
    }

    public override object VisitImplicationConstraint(GeneratedUvlParser.ImplicationConstraintContext context)
    {
        return UvlSyntax.Constraint.create_CBinop(
            Expect<UvlSyntax._IConstraint>(Visit(context.constraint(0)), context.constraint(0)),
            UvlSyntax.ConstraintOp.create_Imply(),
            Expect<UvlSyntax._IConstraint>(Visit(context.constraint(1)), context.constraint(1)));
    }

    public override object VisitEquivalenceConstraint(GeneratedUvlParser.EquivalenceConstraintContext context)
    {
        return UvlSyntax.Constraint.create_CBinop(
            Expect<UvlSyntax._IConstraint>(Visit(context.constraint(0)), context.constraint(0)),
            UvlSyntax.ConstraintOp.create_Equiv(),
            Expect<UvlSyntax._IConstraint>(Visit(context.constraint(1)), context.constraint(1)));
    }

    public override object VisitEqualEquation(GeneratedUvlParser.EqualEquationContext context)
    {
        return BuildEquation(context.expression(0), UvlSyntax.ComparisonOp.create_Eq(), context.expression(1));
    }

    public override object VisitLowerEquation(GeneratedUvlParser.LowerEquationContext context)
    {
        return BuildEquation(context.expression(0), UvlSyntax.ComparisonOp.create_Lt(), context.expression(1));
    }

    public override object VisitGreaterEquation(GeneratedUvlParser.GreaterEquationContext context)
    {
        return BuildEquation(context.expression(0), UvlSyntax.ComparisonOp.create_Gt(), context.expression(1));
    }

    public override object VisitLowerEqualsEquation(GeneratedUvlParser.LowerEqualsEquationContext context)
    {
        return BuildEquation(context.expression(0), UvlSyntax.ComparisonOp.create_Le(), context.expression(1));
    }

    public override object VisitGreaterEqualsEquation(GeneratedUvlParser.GreaterEqualsEquationContext context)
    {
        return BuildEquation(context.expression(0), UvlSyntax.ComparisonOp.create_Ge(), context.expression(1));
    }

    public override object VisitNotEqualsEquation(GeneratedUvlParser.NotEqualsEquationContext context)
    {
        return BuildEquation(context.expression(0), UvlSyntax.ComparisonOp.create_Neq(), context.expression(1));
    }

    public override object VisitExpression(GeneratedUvlParser.ExpressionContext context)
    {
        return Expect<UvlSyntax._IExpression>(Visit(context.additiveExpression()), context.additiveExpression());
    }

    public override object VisitAddExpression(GeneratedUvlParser.AddExpressionContext context)
    {
        return UvlSyntax.Expression.create_EBinop(
            Expect<UvlSyntax._IExpression>(Visit(context.additiveExpression()), context.additiveExpression()),
            UvlSyntax.ArithmeticOp.create_Add(),
            Expect<UvlSyntax._IExpression>(Visit(context.multiplicativeExpression()), context.multiplicativeExpression()));
    }

    public override object VisitSubExpression(GeneratedUvlParser.SubExpressionContext context)
    {
        return UvlSyntax.Expression.create_EBinop(
            Expect<UvlSyntax._IExpression>(Visit(context.additiveExpression()), context.additiveExpression()),
            UvlSyntax.ArithmeticOp.create_Sub(),
            Expect<UvlSyntax._IExpression>(Visit(context.multiplicativeExpression()), context.multiplicativeExpression()));
    }

    public override object VisitMultiplicativeExpr(GeneratedUvlParser.MultiplicativeExprContext context)
    {
        return Expect<UvlSyntax._IExpression>(Visit(context.multiplicativeExpression()), context.multiplicativeExpression());
    }

    public override object VisitPrimaryExpressionExpression(GeneratedUvlParser.PrimaryExpressionExpressionContext context)
    {
        return Expect<UvlSyntax._IExpression>(Visit(context.primaryExpression()), context.primaryExpression());
    }

    public override object VisitMulExpression(GeneratedUvlParser.MulExpressionContext context)
    {
        return UvlSyntax.Expression.create_EBinop(
            Expect<UvlSyntax._IExpression>(Visit(context.multiplicativeExpression()), context.multiplicativeExpression()),
            UvlSyntax.ArithmeticOp.create_Mul(),
            Expect<UvlSyntax._IExpression>(Visit(context.primaryExpression()), context.primaryExpression()));
    }

    public override object VisitDivExpression(GeneratedUvlParser.DivExpressionContext context)
    {
        return UvlSyntax.Expression.create_EBinop(
            Expect<UvlSyntax._IExpression>(Visit(context.multiplicativeExpression()), context.multiplicativeExpression()),
            UvlSyntax.ArithmeticOp.create_Div(),
            Expect<UvlSyntax._IExpression>(Visit(context.primaryExpression()), context.primaryExpression()));
    }

    public override object VisitFloatLiteralExpression(GeneratedUvlParser.FloatLiteralExpressionContext context)
    {
        return UvlSyntax.Expression.create_EFloat(ParseReal(context.FLOAT().GetText(), context));
    }

    public override object VisitIntegerLiteralExpression(GeneratedUvlParser.IntegerLiteralExpressionContext context)
    {
        return UvlSyntax.Expression.create_EInt(ParseInteger(context.INTEGER().GetText(), context));
    }

    public override object VisitStringLiteralExpression(GeneratedUvlParser.StringLiteralExpressionContext context)
    {
        return UvlSyntax.Expression.create_EString(ToDafnyString(UnquoteSingleQuoted(context.STRING().GetText())));
    }

    public override object VisitAggregateFunctionExpression(GeneratedUvlParser.AggregateFunctionExpressionContext context)
    {
        return UvlSyntax.Expression.create_EAggr(
            Expect<UvlSyntax._IAggregateFunction>(Visit(context.aggregateFunction()), context.aggregateFunction()));
    }

    public override object VisitLiteralExpression(GeneratedUvlParser.LiteralExpressionContext context)
    {
        return UvlSyntax.Expression.create_ERef(
            Expect<ReferenceParts>(Visit(context.reference()), context.reference()));
    }

    public override object VisitBracketExpression(GeneratedUvlParser.BracketExpressionContext context)
    {
        return Expect<UvlSyntax._IExpression>(Visit(context.expression()), context.expression());
    }

    public override object VisitSumAggregateFunctionExpression(GeneratedUvlParser.SumAggregateFunctionExpressionContext context)
    {
        return Expect<UvlSyntax._IAggregateFunction>(Visit(context.sumAggregateFunction()), context.sumAggregateFunction());
    }

    public override object VisitAvgAggregateFunctionExpression(GeneratedUvlParser.AvgAggregateFunctionExpressionContext context)
    {
        return Expect<UvlSyntax._IAggregateFunction>(Visit(context.avgAggregateFunction()), context.avgAggregateFunction());
    }

    public override object VisitStringAggregateFunctionExpression(GeneratedUvlParser.StringAggregateFunctionExpressionContext context)
    {
        return Expect<UvlSyntax._IAggregateFunction>(Visit(context.stringAggregateFunction()), context.stringAggregateFunction());
    }

    public override object VisitNumericAggregateFunctionExpression(GeneratedUvlParser.NumericAggregateFunctionExpressionContext context)
    {
        return Expect<UvlSyntax._IAggregateFunction>(Visit(context.numericAggregateFunction()), context.numericAggregateFunction());
    }

    public override object VisitSumAggregateFunction(GeneratedUvlParser.SumAggregateFunctionContext context)
    {
        var (target, scope) = ParseAggregateTargetAndScope(context.reference(), context);
        return UvlSyntax.AggregateFunction.create_Sum(target, scope);
    }

    public override object VisitAvgAggregateFunction(GeneratedUvlParser.AvgAggregateFunctionContext context)
    {
        var (target, scope) = ParseAggregateTargetAndScope(context.reference(), context);
        return UvlSyntax.AggregateFunction.create_Avg(target, scope);
    }

    public override object VisitLengthAggregateFunction(GeneratedUvlParser.LengthAggregateFunctionContext context)
    {
        return UvlSyntax.AggregateFunction.create_Len(
            Expect<ReferenceParts>(Visit(context.reference()), context.reference()));
    }

    public override object VisitFloorAggregateFunction(GeneratedUvlParser.FloorAggregateFunctionContext context)
    {
        return UvlSyntax.AggregateFunction.create_Floor(
            Expect<ReferenceParts>(Visit(context.reference()), context.reference()));
    }

    public override object VisitCeilAggregateFunction(GeneratedUvlParser.CeilAggregateFunctionContext context)
    {
        return UvlSyntax.AggregateFunction.create_Ceil(
            Expect<ReferenceParts>(Visit(context.reference()), context.reference()));
    }

    public override object VisitReference(GeneratedUvlParser.ReferenceContext context)
    {
        return Sequence(context.id().Select(id => Expect<Dafny.ISequence<Dafny.Rune>>(Visit(id), id)));
    }

    public override object VisitId(GeneratedUvlParser.IdContext context)
    {
        if (context.ID_STRICT() is not null)
        {
            return ToDafnyString(context.ID_STRICT().GetText());
        }

        return ToDafnyString(UnquoteDoubleQuoted(context.ID_NOT_STRICT().GetText()));
    }

    public override object VisitFeatureType(GeneratedUvlParser.FeatureTypeContext context)
    {
        if (context.STRING_KEY() is not null)
        {
            return UvlSyntax.FeatureType.create_FTString();
        }

        if (context.INTEGER_KEY() is not null)
        {
            return UvlSyntax.FeatureType.create_FTInteger();
        }

        if (context.BOOLEAN_KEY() is not null)
        {
            return UvlSyntax.FeatureType.create_FTBoolean();
        }

        return UvlSyntax.FeatureType.create_FTReal();
    }

    public override object VisitLanguageLevel(GeneratedUvlParser.LanguageLevelContext context)
    {
        var major = Expect<UvlSyntax._IMajorLevel>(Visit(context.majorLevel()), context.majorLevel());
        var minor = context.DOT() is null
            ? None<UvlSyntax._IMinorLevelSelection>()
            : context.MUL() is not null
                ? Some<UvlSyntax._IMinorLevelSelection>(UvlSyntax.MinorLevelSelection.create_AnyMinorLevel())
                : Some<UvlSyntax._IMinorLevelSelection>(
                    UvlSyntax.MinorLevelSelection.create_ExactMinorLevel(
                        Expect<UvlSyntax._IMinorLevel>(Visit(context.minorLevel()), context.minorLevel())));

        return UvlSyntax.LanguageLevel.create_MkLanguageLevel(major, minor);
    }

    public override object VisitMajorLevel(GeneratedUvlParser.MajorLevelContext context)
    {
        if (context.BOOLEAN_KEY() is not null)
        {
            return UvlSyntax.MajorLevel.create_BooleanLevel();
        }

        if (context.ARITHMETIC_KEY() is not null)
        {
            return UvlSyntax.MajorLevel.create_ArithmeticLevel();
        }

        return UvlSyntax.MajorLevel.create_TypeLevel();
    }

    public override object VisitMinorLevel(GeneratedUvlParser.MinorLevelContext context)
    {
        if (context.GROUP_CARDINALITY_KEY() is not null)
        {
            return UvlSyntax.MinorLevel.create_GroupCardinalityLevel();
        }

        if (context.FEATURE_CARDINALITY_KEY() is not null)
        {
            return UvlSyntax.MinorLevel.create_FeatureCardinalityLevel();
        }

        if (context.AGGREGATE_KEY() is not null)
        {
            return UvlSyntax.MinorLevel.create_AggregateFunctionLevel();
        }

        return UvlSyntax.MinorLevel.create_StringConstraintsLevel();
    }

    private UvlSyntax._IEquation BuildEquation(
        GeneratedUvlParser.ExpressionContext left,
        UvlSyntax._IComparisonOp op,
        GeneratedUvlParser.ExpressionContext right)
    {
        return UvlSyntax.Equation.create_Equation(
            Expect<UvlSyntax._IExpression>(Visit(left), left),
            op,
            Expect<UvlSyntax._IExpression>(Visit(right), right));
    }

    private (ReferenceParts Target, ExtLib.Option._Ioption<ReferenceParts> Scope) ParseAggregateTargetAndScope(
        GeneratedUvlParser.ReferenceContext[] references,
        ParserRuleContext context)
    {
        if (references.Length == 1)
        {
            return (Expect<ReferenceParts>(Visit(references[0]), references[0]), None<ReferenceParts>());
        }

        if (references.Length == 2)
        {
            return (
                Expect<ReferenceParts>(Visit(references[0]), references[0]),
                Some(Expect<ReferenceParts>(Visit(references[1]), references[1])));
        }

        throw InvalidNode(context, $"expected one or two references, found {references.Length}");
    }

    private UvlSyntax._IAttributeDef BuildAttributeDef(GeneratedUvlParser.ValueAttributeContext context)
    {
        var key = Expect<Dafny.ISequence<Dafny.Rune>>(Visit(context.key()), context.key());
        var value = context.value() is null
            ? None<UvlSyntax._IAttributeValue>()
            : Some(Expect<UvlSyntax._IAttributeValue>(Visit(context.value()), context.value()));

        return UvlSyntax.AttributeDef.create_MkAttr(key, value);
    }

    private Dafny.ISequence<UvlSyntax._IAttributeDef> BuildNestedAttributeDefs(GeneratedUvlParser.AttributesContext context)
    {
        return Sequence(context.attribute().Select(attribute =>
        {
            if (attribute.valueAttribute() is not null)
            {
                return BuildAttributeDef(attribute.valueAttribute());
            }

            throw InvalidNode(
                attribute,
                "nested constraint attributes are not supported: 'constraint' and 'constraints' may appear only in top-level feature attribute lists, not inside attribute values or vectors");
        }));
    }

    private static UvlSyntax._ICardinality ParseCardinality(string text, ParserRuleContext context)
    {
        if (text.Length < 2 || text[0] != '[' || text[^1] != ']')
        {
            throw InvalidNode(context, $"invalid cardinality token '{text}'");
        }

        var body = text.Substring(1, text.Length - 2);
        var separator = body.IndexOf("..", StringComparison.Ordinal);
        if (separator < 0)
        {
            var exact = ParseNatural(body, context, "cardinality bound");
            return UvlSyntax.Cardinality.create_MkCardinality(exact, UvlSyntax.UpperBound.create_FiniteUpper(exact));
        }

        var lowerText = body.Substring(0, separator);
        var upperText = body.Substring(separator + 2);
        var lower = ParseNatural(lowerText, context, "cardinality lower bound");
        var upper = upperText == "*"
            ? UvlSyntax.UpperBound.create_UnboundedUpper()
            : UvlSyntax.UpperBound.create_FiniteUpper(ParseNatural(upperText, context, "cardinality upper bound"));

        return UvlSyntax.Cardinality.create_MkCardinality(lower, upper);
    }

    private static bool ParseBoolean(string text, ParserRuleContext context)
    {
        return text switch
        {
            "true" => true,
            "false" => false,
            _ => throw InvalidNode(context, $"invalid Boolean literal '{text}'"),
        };
    }

    private static BigInteger ParseInteger(string text, ParserRuleContext context)
    {
        if (BigInteger.TryParse(text, NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture, out var value))
        {
            return value;
        }

        throw InvalidNode(context, $"invalid integer literal '{text}'");
    }

    private static Dafny.BigRational ParseReal(string text, ParserRuleContext context)
    {
        var negative = text.StartsWith("-", StringComparison.Ordinal);
        var unsigned = negative ? text.Substring(1) : text;
        var dotIndex = unsigned.IndexOf('.', StringComparison.Ordinal);
        if (dotIndex < 0)
        {
            throw InvalidNode(context, $"invalid real literal '{text}'");
        }

        var wholeText = unsigned.Substring(0, dotIndex);
        var fractionText = unsigned.Substring(dotIndex + 1);
        if (fractionText.Length == 0)
        {
            throw InvalidNode(context, $"invalid real literal '{text}'");
        }

        var whole = wholeText.Length == 0
            ? BigInteger.Zero
            : ParseUnsignedNatural(wholeText, context, "real literal");
        var fraction = ParseUnsignedNatural(fractionText, context, "real literal");
        var denominator = BigInteger.Pow(10, fractionText.Length);
        var numerator = (whole * denominator) + fraction;
        if (negative)
        {
            numerator = -numerator;
        }

        return new Dafny.BigRational(numerator, denominator);
    }

    private static BigInteger ParseNatural(string text, ParserRuleContext context, string description)
    {
        var value = ParseInteger(text, context);
        if (value.Sign < 0)
        {
            throw InvalidNode(context, $"{description} cannot be negative: '{text}'");
        }

        return value;
    }

    private static BigInteger ParseUnsignedNatural(string text, ParserRuleContext context, string description)
    {
        if (BigInteger.TryParse(text, NumberStyles.None, CultureInfo.InvariantCulture, out var value))
        {
            return value;
        }

        throw InvalidNode(context, $"invalid {description} '{text}'");
    }

    private static string UnquoteSingleQuoted(string text)
    {
        return text.Substring(1, text.Length - 2);
    }

    private static string UnquoteDoubleQuoted(string text)
    {
        return text.Substring(1, text.Length - 2);
    }

    private static Dafny.ISequence<Dafny.Rune> ToDafnyString(string value)
    {
        return Dafny.Sequence<Dafny.Rune>.UnicodeFromString(value);
    }

    private static Dafny.ISequence<T> Sequence<T>(System.Collections.Generic.IEnumerable<T> values)
    {
        return Dafny.Sequence<T>.FromArray(values.ToArray());
    }

    private static Dafny.ISequence<T> Empty<T>()
    {
        return Dafny.Sequence<T>.Empty;
    }

    private static ExtLib.Option._Ioption<T> Some<T>(T value)
    {
        return ExtLib.Option.option<T>.create_Some(value);
    }

    private static ExtLib.Option._Ioption<T> None<T>()
    {
        return ExtLib.Option.option<T>.create_None();
    }

    private static T Expect<T>(object? value, ParserRuleContext context)
    {
        if (value is T typed)
        {
            return typed;
        }

        throw InvalidNode(
            context,
            $"expected {typeof(T).Name}, found {(value is null ? "null" : value.GetType().FullName)}");
    }

    private static InvalidOperationException InvalidNode(ParserRuleContext context, string message)
    {
        return new InvalidOperationException(
            $"{message} at line {context.Start.Line}, column {context.Start.Column}: {context.GetText()}");
    }
}
