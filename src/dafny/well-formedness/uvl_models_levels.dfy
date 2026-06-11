// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module computes required language levels for expressions, constraints,
// attributes, features, and models in an environment. It lifts local syntax
// level requirements through imports and through typing information. It then
// compares required levels with declared levels to define model level and
// environment level level correctness.
// The frontend level inference pass reuses these definitions.

module UVL_ModelsLevels {
  import opened ExtLib.Option
  import opened UVL_Syntax
  import opened UVL_Environment
  import opened UVL_Variant
  import opened UVL_WellFormedness
  import opened Levels = UVL_Levels
  import opened UVL_ModelsImports
  import opened UVL_ModelsUses
  import opened UVL_ModelsTypeChecking

  // Level declarations remain local to one model, but imported references may
  // still affect the inferred types of expressions used in that model.
  predicate StringExprInModels(
    models: ModelEnv,
    current: ModelPath,
    expression: Expression
  ) requires current in models
  {
    ExpressionTypeInModels(expression, models, current, map[]) == Some(FTString)
  }

  function ExprLevelsInModels(
    models: ModelEnv,
    current: ModelPath,
    expression: Expression
  ): RequiredLevels
    requires current in models
    decreases expression
  {
    match expression
    case EInt(_) => MkRequiredLevels(ArithmeticLevel, {})
    case EFloat(_) => MkRequiredLevels(ArithmeticLevel, {})
    case EString(_) => MkRequiredLevels(TypeLevel, {})
    case ERef(_) => MkRequiredLevels(BooleanLevel, {})
    case EAggr(_) => MkRequiredLevels(ArithmeticLevel, {AggregateFunctionLevel})
    case EBinop(left, _, right) =>
      MergeRequiredLevels(
        MkRequiredLevels(ArithmeticLevel, {}),
        MergeRequiredLevels(
          ExprLevelsInModels(models, current, left),
          ExprLevelsInModels(models, current, right)
        )
      )
  }

  function EqLevelsInModels(
    models: ModelEnv,
    current: ModelPath,
    equation: Equation
  ): RequiredLevels
    requires current in models
  {
    var bothSides :=
      MergeRequiredLevels(
        ExprLevelsInModels(models, current, equation.left),
        ExprLevelsInModels(models, current, equation.right)
      );
    if StringExprInModels(models, current, equation.left) || StringExprInModels(models, current, equation.right) then
      MergeRequiredLevels(MkRequiredLevels(TypeLevel, {StringConstraintsLevel}), bothSides)
    else
      MergeRequiredLevels(MkRequiredLevels(ArithmeticLevel, {}), bothSides)
  }

  function ConstraintLevelsInModels(
    models: ModelEnv,
    current: ModelPath,
    constraint: Constraint
  ): RequiredLevels
    requires current in models
    decreases constraint
  {
    match constraint
    case CRef(_) => MkRequiredLevels(BooleanLevel, {})
    case CEquation(equation) => EqLevelsInModels(models, current, equation)
    case CNot(inner) => ConstraintLevelsInModels(models, current, inner)
    case CBinop(left, _, right) =>
      MergeRequiredLevels(
        ConstraintLevelsInModels(models, current, left),
        ConstraintLevelsInModels(models, current, right)
      )
  }

  function ConstraintsLevelsInModels(
    models: ModelEnv,
    current: ModelPath,
    constraints: seq<Constraint>
  ): RequiredLevels
    requires current in models
  {
    JoinRequiredLevels(
      seq(|constraints|, i =>
        if 0 <= i < |constraints| then
          ConstraintLevelsInModels(models, current, constraints[i])
        else
          MkRequiredLevels(BooleanLevel, {}))
    )
  }

  function AttributeLevelsInModels(
    models: ModelEnv,
    current: ModelPath,
    attribute: Attribute
  ): RequiredLevels
    requires current in models
  {
    match attribute
    case AValue(_) => MkRequiredLevels(BooleanLevel, {})
    case ASingleConstraint(constraint) => ConstraintLevelsInModels(models, current, constraint)
    case AListConstraints(constraints) => ConstraintsLevelsInModels(models, current, constraints)
  }

  function AttributesLevelsInModels(
    models: ModelEnv,
    current: ModelPath,
    attributes: seq<Attribute>
  ): RequiredLevels
    requires current in models
  {
    JoinRequiredLevels(
      seq(|attributes|, i =>
        if 0 <= i < |attributes| then
          AttributeLevelsInModels(models, current, attributes[i])
        else
          MkRequiredLevels(BooleanLevel, {}))
    )
  }

  function FeatureLevelsInModels(
    models: ModelEnv,
    current: ModelPath,
    feature: Feature
  ): RequiredLevels
    requires current in models
    decreases feature
  {
    MergeRequiredLevels(
      MkRequiredLevels(
        if feature.featureType.Some? then
          TypeLevel
        else if feature.cardinality.Some? then
          ArithmeticLevel
        else
          BooleanLevel,
        if feature.cardinality.Some? then {FeatureCardinalityLevel} else {}
      ),
      MergeRequiredLevels(
        AttributesLevelsInModels(models, current, feature.attributes),
        JoinRequiredLevels(
          seq(|feature.groups|, i =>
            if 0 <= i < |feature.groups| then
              var group := feature.groups[i];
              MergeRequiredLevels(
                MkRequiredLevels(BooleanLevel, if group.kind.CardinalityGroup? then {GroupCardinalityLevel} else {}),
                JoinRequiredLevels(
                  seq(|group.features|, k =>
                    if 0 <= k < |group.features| then
                      FeatureLevelsInModels(models, current, group.features[k])
                    else
                      MkRequiredLevels(BooleanLevel, {}))
                )
              )
            else
              MkRequiredLevels(BooleanLevel, {}))
        )
      )
    )
  }

  // Levels are declared per model, but the required levels are computed with
  // models-aware reference typing so imported references contribute correctly.
  function RequiredLevelsInModels(models: ModelEnv, current: ModelPath): RequiredLevels
    requires current in models
  {
    match models[current].rootFeature
    case None => ConstraintsLevelsInModels(models, current, models[current].constraints)
    case Some(root) =>
      MergeRequiredLevels(
        FeatureLevelsInModels(models, current, root),
        ConstraintsLevelsInModels(models, current, models[current].constraints)
      )
  }

  function RequiredMajorInModels(models: ModelEnv, current: ModelPath): MajorLevel
    requires current in models
  {
    RequiredLevelsInModels(models, current).major
  }

  function RequiredMinorsInModels(models: ModelEnv, current: ModelPath): set<MinorLevel>
    requires current in models
  {
    RequiredLevelsInModels(models, current).minors
  }

  predicate LevelsOKInModels(models: ModelEnv, current: ModelPath)
    requires current in models
  {
    ValidLevels(models[current].includes) &&
    Levels.Le(RequiredMajorInModels(models, current), DeclaredMajor(models[current].includes)) &&
    RequiredMinorsInModels(models, current) <= DeclaredMinors(models[current].includes)
  }

  ghost predicate LevelsOKForModels(models: ModelEnv)
  {
    forall current :: current in models ==> LevelsOKInModels(models, current)
  }

}
