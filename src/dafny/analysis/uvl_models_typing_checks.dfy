// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module provides executable typing checks for models after core checking
// has succeeded. It computes declared and inferred reference types, expression
// types, and constraint well typedness. When introduced attributes occur, it
// calls the inference and solver modules and categorises failure. The public
// result is either the first typing error or a proof that the model
// environment is well typed.

module UVL_ModelsTypingChecks {
  import opened ExtLib.Option
  import opened UVL_Syntax
  import opened UVL_Environment
  import opened UVL_Variant
  import opened UVL_References
  import opened UVL_ChecksExecSupport
  import opened UVL_Errors
  import opened UVL_TypingEnvironment
  import opened UVL_ModelsTypeChecking
  import opened UVL_ModelsLevels
  import opened UVL_TypeConstraintSolver
  import opened UVL_ConstraintSites
  import opened UVL_TypeInference
  import opened UVL_ModelsBasicChecks
  import opened UVL_ModelsWF

  method DeclaredReferenceTypeExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    variant: SemVariant,
    current: ModelPath,
    reference: Reference
  ) returns (featureType: option<FeatureType>)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures featureType == DeclaredReferenceTypeInModels(models, current, reference)
  {
    var resolved := ResolveReferenceExec(models, ctxs, variant, current, reference);
    match resolved
    case None =>
      featureType := None;
    case Some(ResolvedFeature(path, target)) =>
      if path in models {
        if target in ctxs[path].semanticRefTypes {
          featureType := Some(ctxs[path].semanticRefTypes[target]);
        } else {
          featureType := None;
        }
        assert ctxs[path].semanticRefTypes == TypeEnv(models[path]);
      } else {
        featureType := None;
      }
    case Some(ResolvedAttribute(path, owner, key)) =>
      if path in models {
        var target := owner + [key];
        if target in ctxs[path].semanticRefTypes {
          featureType := Some(ctxs[path].semanticRefTypes[target]);
        } else {
          featureType := None;
        }
        assert ctxs[path].semanticRefTypes == TypeEnv(models[path]);
      } else {
        featureType := None;
      }
  }

  method ReferenceTypeExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    variant: SemVariant,
    current: ModelPath,
    reference: Reference,
    introTypes: map<Reference, FeatureType>
  ) returns (featureType: option<FeatureType>)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures featureType == ReferenceTypeInModels(models, current, reference, introTypes)
  {
    if 1 < |reference| && reference in introTypes {
      featureType := Some(introTypes[reference]);
    } else {
      featureType := DeclaredReferenceTypeExec(models, ctxs, variant, current, reference);
    }
  }

  method ExpressionTypeExec(
    expression: Expression,
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    variant: SemVariant,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>
  ) returns (featureType: option<FeatureType>)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures featureType == ExpressionTypeInModels(expression, models, current, introTypes)
    decreases expression
  {
    match expression
    case EInt(_) =>
      featureType := Some(FTInteger);
    case EFloat(_) =>
      featureType := Some(FTReal);
    case EString(_) =>
      featureType := Some(FTString);
    case ERef(reference) =>
      featureType := ReferenceTypeExec(models, ctxs, variant, current, reference, introTypes);
    case EAggr(aggregate) =>
      featureType := AggregateExpressionTypeInModels(aggregate, models, current, introTypes);
    case EBinop(left, op, right) =>
      var leftType := ExpressionTypeExec(left, models, ctxs, variant, current, introTypes);
      match leftType
      case None =>
        featureType := None;
      case Some(leftFeatureType) =>
        var rightType := ExpressionTypeExec(right, models, ctxs, variant, current, introTypes);
        match rightType
        case None =>
          featureType := None;
        case Some(rightFeatureType) =>
          featureType := ArithmeticResultType(op, leftFeatureType, rightFeatureType);
  }

  method WellTypedEquationExec(
    equation: Equation,
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    variant: SemVariant,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>
  ) returns (ok: bool)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures ok == WellTypedEquationInModels(equation, models, current, introTypes)
  {
    var leftType := ExpressionTypeExec(equation.left, models, ctxs, variant, current, introTypes);
    match leftType
    case None =>
      ok := false;
    case Some(leftFeatureType) =>
      var rightType := ExpressionTypeExec(equation.right, models, ctxs, variant, current, introTypes);
      match rightType
      case None =>
        ok := false;
      case Some(rightFeatureType) =>
        if equation.op == Eq || equation.op == Neq {
          ok :=
            leftFeatureType == rightFeatureType ||
            (NumericFeatureType(leftFeatureType) && NumericFeatureType(rightFeatureType));
        } else {
          ok :=
            (NumericFeatureType(leftFeatureType) && NumericFeatureType(rightFeatureType)) ||
            (leftFeatureType == FTString && rightFeatureType == FTString);
        }
  }

  method BoolLiteralReferenceAllowedExec(
    reference: Reference,
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    variant: SemVariant,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>
  ) returns (ok: bool)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures ok == BoolLiteralReferenceAllowedInModels(reference, models, current, introTypes, variant)
  {
    var featureType := ReferenceTypeExec(models, ctxs, variant, current, reference, introTypes);
    match featureType
    case None =>
      ok := false;
    case Some(value) =>
      ok :=
        value == FTBoolean ||
        (variant.typedFeatureAsBool && ReferenceKindInModels(models, current, reference) == FeatureReference);
  }

  method ConstraintSeqWellTypedExec(
    constraints: seq<Constraint>,
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    variant: SemVariant,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>
  ) returns (ok: bool)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures ok == (forall i :: 0 <= i < |constraints| ==> WellTypedConstraintInModels(constraints[i], models, current, introTypes, variant))
    decreases |constraints|
  {
    if |constraints| == 0 {
      ok := true;
    } else {
      var headOk := WellTypedConstraintExec(constraints[0], models, ctxs, variant, current, introTypes);
      if !headOk {
        ok := false;
      } else {
        ok := ConstraintSeqWellTypedExec(constraints[1..], models, ctxs, variant, current, introTypes);
      }
    }
  }

  method WellTypedConstraintExec(
    constraint: Constraint,
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    variant: SemVariant,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>
  ) returns (ok: bool)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures ok == WellTypedConstraintInModels(constraint, models, current, introTypes, variant)
    decreases constraint
  {
    match constraint
    case CRef(reference) =>
      ok := BoolLiteralReferenceAllowedExec(reference, models, ctxs, variant, current, introTypes);
    case CEquation(equation) =>
      ok := WellTypedEquationExec(equation, models, ctxs, variant, current, introTypes);
    case CNot(inner) =>
      ok := WellTypedConstraintExec(inner, models, ctxs, variant, current, introTypes);
    case CBinop(left, _, right) =>
      var leftOk := WellTypedConstraintExec(left, models, ctxs, variant, current, introTypes);
      if !leftOk {
        ok := false;
      } else {
        ok := WellTypedConstraintExec(right, models, ctxs, variant, current, introTypes);
      }
  }

  method ConstraintsWellTypedExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    variant: SemVariant,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>
  ) returns (ok: bool)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures ok == ConstraintsWellTypedInModels(models, current, introTypes, variant)
  {
    var globalOk := ConstraintSeqWellTypedExec(models[current].constraints, models, ctxs, variant, current, introTypes);
    if !globalOk {
      ok := false;
    } else {
      match models[current].rootFeature
      case None =>
        ok := true;
      case Some(root) =>
        ok := FeatureAttributesWellTypedInModels(root, models, current, introTypes, variant);
    }
  }

  method FirstTypingErrorInModelWithCtx(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    current: ModelPath,
    variant: SemVariant
  ) returns (error: option<TypingError>)
    requires current in models
    requires WF_SemVariant(variant)
    requires CoreWF_ModelInModels(models, current, variant)
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures error.None? ==> WellTypedModelInModels(models, current, variant)
  {
    var uvlConstraints := ExtractUVLConstraints(models[current]);
    var inferredRefs := ExtractIntroducibleRefs(uvlConstraints, models[current], variant);
    if inferredRefs == {} {
      var wellTyped := ConstraintsWellTypedExec(models, ctxs, variant, current, map[]);
      if wellTyped {
        assert IntroTypesOKInModels(models, current, variant, map[]);
        error := None;
      } else {
        error := Some(IllTypedModel(current));
      }
    } else {
      var typeConstraints := GenerateTypeConstraintsInModels(
        uvlConstraints,
        models,
        current,
        inferredRefs
      );
      var solverResult := SolveTypeConstraints(typeConstraints);
      match solverResult
      case Contradiction(domains) =>
        error := Some(IntroTypeInferenceContradiction(current, domains));
      case Underconstrained(domains) =>
        {
          var concretised := ConcretiseDomains(domains);
          match concretised
          case None =>
            error := Some(IntroTypeInferenceUnderconstrained(current, domains));
          case Some(solution) =>
            var introTypes := SolutionIntroTypesInModels(models, current, variant, solution);
            var wellTyped := ConstraintsWellTypedExec(models, ctxs, variant, current, introTypes);
            if wellTyped {
              assert IntroTypesOKInModels(models, current, variant, introTypes);
              error := None;
            } else {
              error := Some(IntroTypeInferenceUnderconstrained(current, domains));
            }
        }
      case Solved(solution) =>
        var introTypes := SolutionIntroTypesInModels(models, current, variant, solution);
        var wellTyped := ConstraintsWellTypedExec(models, ctxs, variant, current, introTypes);
        if wellTyped {
          assert IntroTypesOKInModels(models, current, variant, introTypes);
          error := None;
        } else {
          error := Some(IllTypedModel(current));
        }
    }
  }

  // Full typing diagnostics assume the caller already passed the core checks.
  method FirstTypingError(
    models: ModelEnv,
    variant: SemVariant
  ) returns (error: option<TypingError>)
    requires CoreWF_Models(models, variant)
    ensures error.None? ==> WellTypedModels(models, variant)
  {
    var ctxs := CoreExecCtxEnvOf(models, variant);
    CoreExecCtxEnvOfOK(models, variant);
    var unchecked := set path | path in models :: path;
    error := FirstTypingErrorInSetWithCtx(models, ctxs, variant, unchecked);
  }

  method FirstTypingErrorInSetWithCtx(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    variant: SemVariant,
    unchecked: set<ModelPath>
  ) returns (error: option<TypingError>)
    requires CoreWF_Models(models, variant)
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    requires unchecked <= set path | path in models :: path
    requires forall path :: path in models && path !in unchecked ==> WellTypedModelInModels(models, path, variant)
    ensures error.None? ==> forall path :: path in unchecked ==> WellTypedModelInModels(models, path, variant)
    decreases |unchecked|
  {
    if unchecked == {} {
      error := None;
    } else {
      var current :| current in unchecked;
      var currentError := FirstTypingErrorInModelWithCtx(models, ctxs, current, variant);
      if currentError.Some? {
        error := currentError;
      } else {
        forall path | path in models && path !in (unchecked - {current})
          ensures WellTypedModelInModels(models, path, variant)
        {
          if path in unchecked {
            assert path == current;
          }
        }
        error := FirstTypingErrorInSetWithCtx(models, ctxs, variant, unchecked - {current});
      }
    }
  }

}
