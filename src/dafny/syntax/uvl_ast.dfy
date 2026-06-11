// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

module UVL_Syntax {
  import opened Std.Collections.Seq
  import opened ExtLib.Option
  import opened UVL_Path

  // Abstract syntax derived from UVL concrete grammar

  type IntType = int
  type RealType = real
  type StringType = string

  type Reference = Ref

  datatype MajorLevel =
    | BooleanLevel
    | ArithmeticLevel
    | TypeLevel

  datatype MinorLevel =
    | GroupCardinalityLevel
    | FeatureCardinalityLevel
    | AggregateFunctionLevel
    | StringConstraintsLevel

  datatype MinorLevelSelection =
    | ExactMinorLevel(level: MinorLevel)
    | AnyMinorLevel

  datatype LanguageLevel =
    | MkLanguageLevel(
        major: MajorLevel,
        minor: option<MinorLevelSelection>
      )

  datatype ImportDecl =
    | MkImportDecl(
        importPath: Reference,
        alias: option<Reference>
      )

  datatype FeatureType =
    | FTString
    | FTInteger
    | FTBoolean
    | FTReal

  datatype UpperBound =
    | FiniteUpper(value: nat)
    | UnboundedUpper

  datatype Cardinality =
    | MkCardinality(
        lower: nat,
        upper: UpperBound
      )

  datatype GroupKind =
    | OrGroup
    | AlternativeGroup
    | OptionalGroup
    | MandatoryGroup
    | CardinalityGroup(cardinality: Cardinality)

  // We keep the non-terminal name of the grammar, although only sum and avg
  // are really aggregate functions working on the values of the same
  // attribute in several features.
  datatype AggregateFunction =
    | Sum(target: Reference, scope: option<Reference>)
    | Avg(target: Reference, scope: option<Reference>)
    | Len(target: Reference)
    | Floor(target: Reference)
    | Ceil(target: Reference)

  datatype ArithmeticOp =
    | Add
    | Sub
    | Mul
    | Div

  datatype Expression =
    | EInt(intValue: IntType)
    | EFloat(realValue: RealType)
    | EString(strinValue: StringType)
    | ERef(reference: Reference)
    | EAggr(aggregate: AggregateFunction)
    | EBinop(left: Expression, op: ArithmeticOp, right: Expression)

  datatype ComparisonOp =
    | Eq
    | Lt
    | Gt
    | Le
    | Ge
    | Neq

  datatype Equation =
    | Equation(
        left: Expression,
        op: ComparisonOp,
        right: Expression
      )

  datatype ConstraintOp =
    | And
    | Or
    | Imply
    | Equiv

  datatype Constraint =
    | CRef(reference: Reference)
    | CEquation(equation: Equation)
    | CNot(inner: Constraint)
    | CBinop(left: Constraint, op: ConstraintOp, right: Constraint)

  datatype Attribute =
    | AValue(attribute: AttributeDef)
    | ASingleConstraint(constraint: Constraint)
    | AListConstraints(constraints: seq<Constraint>)
  datatype AttributeDef =
    | MkAttr(key: string, value: option<AttributeValue>)
  datatype AttributeValue =
    | VBool(value: bool)
    | VFloat(realValue: RealType)
    | VInt(intValue: IntType)
    | VString(stringValue: StringType)
    | VRecord(attributes: seq<AttributeDef>)
    | VVector(elements: seq<AttributeValue>)

  datatype Group =
    | MkGroup(
        kind: GroupKind,
        features: seq<Feature>
      )
  datatype Feature =
    | MkFeature(
        featureType: option<FeatureType>,
        name: Reference,
        cardinality: option<Cardinality>,
        attributes: seq<Attribute>,
        groups: seq<Group>
      )

  datatype FeatureModel =
    | MkFeatureModel(
        namespace: option<Reference>,
        includes: seq<LanguageLevel>,
        imports: seq<ImportDecl>,
        rootFeature: option<Feature>,
        constraints: seq<Constraint>
      )

}
