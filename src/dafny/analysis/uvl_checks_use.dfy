// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module executes the logical use validity checks over expressions,
// constraints, attributes, and features. It traverses syntax trees and stops
// at the first invalid feature-tree name, reference occurrence, or aggregate
// use. The checkings rely on the executable core context for reference
// resolution and aggregate validation. A `None` result establishes the
// corresponding predicate.

module UVL_UseChecks {
  import opened Syntax = UVL_Syntax
  import opened Option = ExtLib.Option
  import opened Environment = UVL_Environment
  import opened Errors = UVL_Errors
  import opened CoreExecution = UVL_ChecksExecSupport
  import opened LocalChecks = UVL_LocalChecks
  import opened Uses = UVL_ModelsUses
  import opened Variant = UVL_Variant

  method FirstInvalidExpressionUseInModelsExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    current: ModelPath,
    variant: SemVariant,
    expression: Expression
  ) returns (error: option<CoreCheckError>)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures error.None? ==> ValidExpressionUsesInModels(models, current, variant, expression)
    decreases expression
  {
    match expression
    case EInt(_) =>
      error := None;
    case EFloat(_) =>
      error := None;
    case EString(_) =>
      error := None;
    case ERef(reference) =>
      var referenceOk := ValidReferenceOccurrenceExec(models, ctxs, current, variant, reference);
      if referenceOk {
        error := None;
      } else {
        error := Some(InvalidReferenceUse(current, reference));
      }
    case EAggr(aggregate) =>
      var aggregateOk := ValidAggregateUseExec(models, ctxs, current, variant, aggregate);
      if aggregateOk {
        error := None;
      } else {
        error := Some(InvalidAggregateUse(current, aggregate));
      }
    case EBinop(left, _, right) =>
      var leftError := FirstInvalidExpressionUseInModelsExec(models, ctxs, current, variant, left);
      if leftError.Some? {
        error := leftError;
      } else {
        error := FirstInvalidExpressionUseInModelsExec(models, ctxs, current, variant, right);
      }
  }

  method FirstInvalidConstraintUseInModelsExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    current: ModelPath,
    variant: SemVariant,
    constraint: Constraint
  ) returns (error: option<CoreCheckError>)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures error.None? ==> ValidConstraintUsesInModels(models, current, variant, constraint)
    decreases constraint
  {
    match constraint
    case CRef(reference) =>
      var referenceOk := ValidReferenceOccurrenceExec(models, ctxs, current, variant, reference);
      if referenceOk {
        error := None;
      } else {
        error := Some(InvalidReferenceUse(current, reference));
      }
    case CEquation(equation) =>
      var leftError := FirstInvalidExpressionUseInModelsExec(models, ctxs, current, variant, equation.left);
      if leftError.Some? {
        error := leftError;
      } else {
        error := FirstInvalidExpressionUseInModelsExec(models, ctxs, current, variant, equation.right);
      }
    case CNot(inner) =>
      error := FirstInvalidConstraintUseInModelsExec(models, ctxs, current, variant, inner);
    case CBinop(left, _, right) =>
      var leftError := FirstInvalidConstraintUseInModelsExec(models, ctxs, current, variant, left);
      if leftError.Some? {
        error := leftError;
      } else {
        error := FirstInvalidConstraintUseInModelsExec(models, ctxs, current, variant, right);
      }
  }

  method FirstInvalidAttributeUseInModelsExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    current: ModelPath,
    variant: SemVariant,
    attributes: seq<Attribute>
  ) returns (error: option<CoreCheckError>)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures error.None? ==> forall i :: 0 <= i < |attributes| ==> ValidAttributeUsesInModels(models, current, variant, attributes[i])
    decreases |attributes|
  {
    var i := 0;
    while i < |attributes|
      invariant 0 <= i <= |attributes|
      invariant forall j :: 0 <= j < i ==> ValidAttributeUsesInModels(models, current, variant, attributes[j])
      decreases |attributes| - i
    {
      match attributes[i]
      case AValue(_) =>
        i := i + 1;
      case ASingleConstraint(constraint) =>
        var currentError := FirstInvalidConstraintUseInModelsExec(models, ctxs, current, variant, constraint);
        if currentError.Some? {
          error := currentError;
          return;
        }
        assert ValidConstraintUsesInModels(models, current, variant, constraint);
        i := i + 1;
      case AListConstraints(constraints) =>
        var currentError := FirstInvalidConstraintSeqUseInModelsExec(models, ctxs, current, variant, constraints);
        if currentError.Some? {
          error := currentError;
          return;
        }
        assert forall j :: 0 <= j < |constraints| ==> ValidConstraintUsesInModels(models, current, variant, constraints[j]);
        i := i + 1;
    }
    error := None;
  }

  method FirstInvalidConstraintSeqUseInModelsExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    current: ModelPath,
    variant: SemVariant,
    constraints: seq<Constraint>
  ) returns (error: option<CoreCheckError>)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures error.None? ==> forall i :: 0 <= i < |constraints| ==> ValidConstraintUsesInModels(models, current, variant, constraints[i])
    decreases |constraints|
  {
    var i := 0;
    while i < |constraints|
      invariant 0 <= i <= |constraints|
      invariant forall j :: 0 <= j < i ==> ValidConstraintUsesInModels(models, current, variant, constraints[j])
      decreases |constraints| - i
    {
      var currentError := FirstInvalidConstraintUseInModelsExec(models, ctxs, current, variant, constraints[i]);
      if currentError.Some? {
        error := currentError;
        return;
      }
      assert ValidConstraintUsesInModels(models, current, variant, constraints[i]);
      i := i + 1;
    }
    error := None;
  }

  method FirstInvalidFeatureUseInModelsExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    current: ModelPath,
    variant: SemVariant,
    feature: Feature
  ) returns (error: option<CoreCheckError>)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures error.None? ==> ValidFeatureUsesInModels(models, current, variant, feature)
  {
    var featureNameOk := ValidFeatureTreeNameExec(models, ctxs, current, variant, feature.name);
    if !featureNameOk {
      error := Some(InvalidFeatureTreeUse(current, feature.name));
    } else {
      var attributeError := FirstInvalidAttributeUseInModelsExec(models, ctxs, current, variant, feature.attributes);
      if attributeError.Some? {
        error := attributeError;
      } else {
        var i := 0;
        while i < |feature.groups|
          invariant 0 <= i <= |feature.groups|
          invariant forall g, h :: 0 <= g < i && 0 <= h < |feature.groups[g].features| ==>
                                     ValidFeatureUsesInModels(models, current, variant, feature.groups[g].features[h])
          decreases |feature.groups| - i
        {
          var j := 0;
          while j < |feature.groups[i].features|
            invariant 0 <= j <= |feature.groups[i].features|
            invariant forall h :: 0 <= h < j ==>
                                    ValidFeatureUsesInModels(models, current, variant, feature.groups[i].features[h])
            decreases |feature.groups[i].features| - j
          {
            var currentError := FirstInvalidFeatureUseInModelsExec(
              models,
              ctxs,
              current,
              variant,
              feature.groups[i].features[j]
            );
            if currentError.Some? {
              error := currentError;
              return;
            }
            j := j + 1;
          }
          i := i + 1;
        }
        error := None;
      }
    }
  }

  method FirstInvalidModelUseInModelsExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    current: ModelPath,
    variant: SemVariant
  ) returns (error: option<CoreCheckError>)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures error.None? ==> ValidModelUsesInModels(models, current, variant)
  {
    match models[current].rootFeature
    case None =>
      error := FirstInvalidConstraintSeqUseInModelsExec(models, ctxs, current, variant, models[current].constraints);
    case Some(root) =>
      var featureError := FirstInvalidFeatureUseInModelsExec(models, ctxs, current, variant, root);
      if featureError.Some? {
        error := featureError;
      } else {
        error := FirstInvalidConstraintSeqUseInModelsExec(models, ctxs, current, variant, models[current].constraints);
      }
  }

}
