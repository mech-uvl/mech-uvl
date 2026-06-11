// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module generates finite-domain type constraints for introduced
// attributes mentioned in constraints. It computes which introduced references
// are inferable at each constraint site and which feature types remain
// possible for them. For numeric types, when the problem is under-constrained,
// a type (Integer or Real) is chosen. If there is at least one usage that
// suggests the reference could be typed as a real, it's a real (which is
// always correct as real here is really mathematical reals that include
// integers), otherwise it is typed as an integer.

module UVL_TypeInference {
  import opened ExtLib.Option
  import opened UVL_Syntax
  import opened UVL_Environment
  import opened UVL_Variant
  import opened UVL_TypingEnvironment
  import opened UVL_References
  import opened UVL_ModelsResolution
  import opened UVL_ModelsTypeChecking
  import opened UVL_TypeConstraintSolver
  import opened UVL_ConstraintSites

  function AllowedTypeConstraintsInModels(
    reference: Reference,
    allowed: set<FeatureType>
  ): seq<TypeConstraint>
  {
    [TypeIn(reference, allowed)]
  }

  method RestrictInferredReferenceInModels(
    reference: Reference,
    allowed: set<FeatureType>,
    inferredRefs: set<Reference>
  ) returns (constraints: seq<TypeConstraint>)
  {
    if reference in inferredRefs {
      constraints := AllowedTypeConstraintsInModels(reference, allowed);
    } else {
      constraints := [];
    }
  }

  method ReferenceSetTypeConstraintsInModels(
    references: set<Reference>,
    allowed: set<FeatureType>
  ) returns (constraints: seq<TypeConstraint>)
    decreases |references|
  {
    if references == {} {
      constraints := [];
    } else {
      var reference :| reference in references;
      var rest := ReferenceSetTypeConstraintsInModels(references - {reference}, allowed);
      constraints := AllowedTypeConstraintsInModels(reference, allowed) + rest;
    }
  }

  function AggregateScopeSelectsIntroducedRefInModels(
    key: string,
    scope: option<Reference>,
    models: ModelEnv,
    current: ModelPath,
    reference: Reference
  ): bool
    requires current in models
    requires 1 < |reference|
  {
    reference[|reference| - 1] == key &&
    match scope
    case None => true
    case Some(scopeReference) =>
      match ResolveReference(models, current, scopeReference)
      case Some(ResolvedFeature(path, targetFeature)) =>
        path == current && ReferenceLocalTo(targetFeature, AttributeOwner(reference))
      case _ => false
  }

  function AggregateIntroducedRefsInModels(
    key: string,
    scope: option<Reference>,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ): set<Reference>
    requires current in models
  {
    set reference |
      reference in inferredRefs &&
      1 < |reference| &&
      AggregateScopeSelectsIntroducedRefInModels(key, scope, models, current, reference) ::
      reference
  }

  method AggregateTypeConstraintsInModels(
    aggregate: AggregateFunction,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (constraints: seq<TypeConstraint>)
    requires current in models
  {
    match aggregate
    case Sum(target, scope) =>
      if IsBareAggregateTargetKey(target) {
        constraints := ReferenceSetTypeConstraintsInModels(
          AggregateIntroducedRefsInModels(target[0], scope, models, current, inferredRefs),
          {FTInteger, FTReal});
      } else {
        constraints := [];
      }
    case Avg(target, scope) =>
      if IsBareAggregateTargetKey(target) {
        constraints := ReferenceSetTypeConstraintsInModels(
          AggregateIntroducedRefsInModels(target[0], scope, models, current, inferredRefs),
          {FTInteger, FTReal});
      } else {
        constraints := [];
      }
    case Len(target) =>
      constraints := RestrictInferredReferenceInModels(target, {FTString}, inferredRefs);
    case Floor(target) =>
      constraints := RestrictInferredReferenceInModels(target, {FTReal}, inferredRefs);
    case Ceil(target) =>
      constraints := RestrictInferredReferenceInModels(target, {FTReal}, inferredRefs);
  }

  function EqualityCompatibleTypes(possibleTypes: set<FeatureType>): set<FeatureType>
  {
    (if FTBoolean in possibleTypes then {FTBoolean} else {}) +
    (if FTString in possibleTypes then {FTString} else {}) +
    (if FTInteger in possibleTypes || FTReal in possibleTypes then {FTInteger, FTReal} else {})
  }

  function OrderedComparisonCompatibleTypes(possibleTypes: set<FeatureType>): set<FeatureType>
  {
    (if FTInteger in possibleTypes || FTReal in possibleTypes then {FTInteger, FTReal} else {}) +
    (if FTString in possibleTypes then {FTString} else {})
  }

  method AggregatePossibleTypesInModels(
    aggregate: AggregateFunction,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (possibleTypes: set<FeatureType>)
    requires current in models
  {
    match AggregateExpressionTypeInModels(aggregate, models, current, map[])
    case Some(featureType) =>
      possibleTypes := {featureType};
    case None =>
      match aggregate
      case Sum(target, scope) =>
        if IsBareAggregateTargetKey(target) &&
           AggregateIntroducedRefsInModels(target[0], scope, models, current, inferredRefs) != {} {
          possibleTypes := {FTInteger, FTReal};
        } else {
          possibleTypes := {};
        }
      case Avg(target, scope) =>
        if IsBareAggregateTargetKey(target) &&
           AggregateIntroducedRefsInModels(target[0], scope, models, current, inferredRefs) != {} {
          possibleTypes := {FTReal};
        } else {
          possibleTypes := {};
        }
      case Len(_) =>
        possibleTypes := {FTInteger};
      case Floor(_) =>
        possibleTypes := {FTInteger};
      case Ceil(_) =>
        possibleTypes := {FTInteger};
  }

  // Computes an over-approximation of the types an expression may have before
  // introduced-attribute inference finishes. Equation constraints use this to
  // propagate type-family information across both sides even when one side
  // still contains introduced references.
  method ExpressionPossibleTypesInModels(
    expression: Expression,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (possibleTypes: set<FeatureType>)
    requires current in models
    decreases expression
  {
    match expression
    case EInt(_) =>
      possibleTypes := {FTInteger};
    case EFloat(_) =>
      possibleTypes := {FTReal};
    case EString(_) =>
      possibleTypes := {FTString};
    case ERef(reference) =>
      if reference in inferredRefs {
        possibleTypes := AllTypes();
      } else {
        match DeclaredReferenceTypeInModels(models, current, reference)
        case Some(featureType) =>
          possibleTypes := {featureType};
        case None =>
          possibleTypes := {};
      }
    case EAggr(aggregate) =>
      possibleTypes := AggregatePossibleTypesInModels(aggregate, models, current, inferredRefs);
    case EBinop(left, op, right) =>
      var leftPossible := ExpressionPossibleTypesInModels(left, models, current, inferredRefs);
      var rightPossible := ExpressionPossibleTypesInModels(right, models, current, inferredRefs);
      possibleTypes := set featureType |
        exists leftType, rightType ::
          leftType in leftPossible &&
          rightType in rightPossible &&
          ArithmeticResultType(op, leftType, rightType) == Some(featureType) ::
        featureType;
  }

  method ExpressionInferredRefsInModels(
    expression: Expression,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (refs: set<Reference>)
    requires current in models
    decreases expression
  {
    match expression
    case EInt(_) =>
      refs := {};
    case EFloat(_) =>
      refs := {};
    case EString(_) =>
      refs := {};
    case ERef(reference) =>
      if reference in inferredRefs {
        refs := {reference};
      } else {
        refs := {};
      }
    case EAggr(aggregate) =>
      {
        match aggregate
        case Sum(_, _) =>
          refs := {};
        case Avg(_, _) =>
          refs := {};
        case Len(target) =>
          if target in inferredRefs { refs := {target}; } else { refs := {}; }
        case Floor(target) =>
          if target in inferredRefs { refs := {target}; } else { refs := {}; }
        case Ceil(target) =>
          if target in inferredRefs { refs := {target}; } else { refs := {}; }
      }
    case EBinop(left, _, right) =>
      var leftRefs := ExpressionInferredRefsInModels(left, models, current, inferredRefs);
      var rightRefs := ExpressionInferredRefsInModels(right, models, current, inferredRefs);
      refs := leftRefs + rightRefs;
  }

  // Collects introduced references that should prefer RealType when residual
  // concretisation still leaves the numeric ambiguity {Integer, RealType}. This
  // is a heuristic bias, not a logical typing obligation.
  method ExpressionRealBiasRefsInModels(
    expression: Expression,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (refs: set<Reference>)
    requires current in models
    decreases expression
  {
    match expression
    case EInt(_) =>
      refs := {};
    case EFloat(_) =>
      refs := {};
    case EString(_) =>
      refs := {};
    case ERef(_) =>
      refs := {};
    case EAggr(_) =>
      refs := {};
    case EBinop(left, _, right) =>
      var leftBias := ExpressionRealBiasRefsInModels(left, models, current, inferredRefs);
      var rightBias := ExpressionRealBiasRefsInModels(right, models, current, inferredRefs);
      var leftPossible := ExpressionPossibleTypesInModels(left, models, current, inferredRefs);
      var rightPossible := ExpressionPossibleTypesInModels(right, models, current, inferredRefs);
      var leftExtra: set<Reference>;
      if rightPossible == {FTReal} {
        leftExtra := ExpressionInferredRefsInModels(left, models, current, inferredRefs);
      } else {
        leftExtra := {};
      }
      var rightExtra: set<Reference>;
      if leftPossible == {FTReal} {
        rightExtra := ExpressionInferredRefsInModels(right, models, current, inferredRefs);
      } else {
        rightExtra := {};
      }
      refs := leftBias + rightBias + leftExtra + rightExtra;
  }

  method ExpressionTypeConstraintsInModels(
    expression: Expression,
    models: ModelEnv,
    current: ModelPath,
    expected: set<FeatureType>,
    inferredRefs: set<Reference>
  ) returns (constraints: seq<TypeConstraint>)
    requires current in models
    decreases expression
  {
    match expression
    case EInt(_) => constraints := [];
    case EFloat(_) => constraints := [];
    case EString(_) => constraints := [];
    case ERef(reference) =>
      constraints := RestrictInferredReferenceInModels(reference, expected, inferredRefs);
    case EAggr(aggregate) =>
      constraints := AggregateTypeConstraintsInModels(aggregate, models, current, inferredRefs);
    case EBinop(left, _, right) =>
      if expected * {FTInteger, FTReal} == {} {
        constraints := [];
      } else {
        var leftConstraints := ExpressionTypeConstraintsInModels(left, models, current, {FTInteger, FTReal}, inferredRefs);
        var rightConstraints := ExpressionTypeConstraintsInModels(right, models, current, {FTInteger, FTReal}, inferredRefs);
        constraints := leftConstraints + rightConstraints;
      }
  }

  // Generates the typing constraints induced by one equation operand, given
  // the possible type family already inferred from the opposite side.
  method OperandTypeConstraintsInModels(
    expression: Expression,
    models: ModelEnv,
    current: ModelPath,
    op: ComparisonOp,
    otherPossibleTypes: set<FeatureType>,
    inferredRefs: set<Reference>
  ) returns (constraints: seq<TypeConstraint>)
    requires current in models
  {
    if op == Eq || op == Neq {
      var allowed := EqualityCompatibleTypes(otherPossibleTypes);
      if allowed == {} {
        constraints := [];
      } else {
        constraints := ExpressionTypeConstraintsInModels(expression, models, current, allowed, inferredRefs);
      }
    } else {
      var allowed := OrderedComparisonCompatibleTypes(otherPossibleTypes);
      if allowed == {} {
        constraints := ExpressionTypeConstraintsInModels(expression, models, current, {FTInteger, FTReal, FTString}, inferredRefs);
      } else {
        constraints := ExpressionTypeConstraintsInModels(expression, models, current, allowed, inferredRefs);
      }
    }
  }

  // Generates the typing constraints induced by one equation.
  method EquationTypeConstraintsInModels(
    equation: Equation,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (constraints: seq<TypeConstraint>)
    requires current in models
  {
    var leftConstraints := ExpressionTypeConstraintsInModels(equation.left, models, current, AllTypes(), inferredRefs);
    var rightConstraints := ExpressionTypeConstraintsInModels(equation.right, models, current, AllTypes(), inferredRefs);
    var rightPossibleTypes := ExpressionPossibleTypesInModels(equation.right, models, current, inferredRefs);
    var lhsOperandConstraints := OperandTypeConstraintsInModels(
      equation.left,
      models,
      current,
      equation.op,
      rightPossibleTypes,
      inferredRefs);
    var leftPossibleTypes := ExpressionPossibleTypesInModels(equation.left, models, current, inferredRefs);
    var rhsOperandConstraints := OperandTypeConstraintsInModels(
      equation.right,
      models,
      current,
      equation.op,
      leftPossibleTypes,
      inferredRefs);
    constraints := leftConstraints + rightConstraints + lhsOperandConstraints + rhsOperandConstraints;
  }

  method EquationRealBiasRefsInModels(
    equation: Equation,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (refs: set<Reference>)
    requires current in models
  {
    var leftBias := ExpressionRealBiasRefsInModels(equation.left, models, current, inferredRefs);
    var rightBias := ExpressionRealBiasRefsInModels(equation.right, models, current, inferredRefs);
    var leftPossibleTypes := ExpressionPossibleTypesInModels(equation.left, models, current, inferredRefs);
    var rightPossibleTypes := ExpressionPossibleTypesInModels(equation.right, models, current, inferredRefs);
    var leftExtra: set<Reference>;
    if rightPossibleTypes == {FTReal} {
      leftExtra := ExpressionInferredRefsInModels(equation.left, models, current, inferredRefs);
    } else {
      leftExtra := {};
    }
    var rightExtra: set<Reference>;
    if leftPossibleTypes == {FTReal} {
      rightExtra := ExpressionInferredRefsInModels(equation.right, models, current, inferredRefs);
    } else {
      rightExtra := {};
    }
    refs := leftBias + rightBias + leftExtra + rightExtra;
  }

  // Generates the typing constraints induced by one constraint.
  method ConstraintTypeConstraintsInModels(
    constraint: Constraint,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (constraints: seq<TypeConstraint>)
    requires current in models
    decreases constraint
  {
    match constraint
    case CRef(reference) =>
      constraints := RestrictInferredReferenceInModels(reference, {FTBoolean}, inferredRefs);
    case CEquation(equation) =>
      constraints := EquationTypeConstraintsInModels(equation, models, current, inferredRefs);
    case CNot(inner) =>
      constraints := ConstraintTypeConstraintsInModels(inner, models, current, inferredRefs);
    case CBinop(left, _, right) =>
      var leftConstraints := ConstraintTypeConstraintsInModels(left, models, current, inferredRefs);
      var rightConstraints := ConstraintTypeConstraintsInModels(right, models, current, inferredRefs);
      constraints := leftConstraints + rightConstraints;
  }

  method ConstraintRealBiasRefsInModels(
    constraint: Constraint,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (refs: set<Reference>)
    requires current in models
    decreases constraint
  {
    match constraint
    case CRef(_) =>
      refs := {};
    case CEquation(equation) =>
      refs := EquationRealBiasRefsInModels(equation, models, current, inferredRefs);
    case CNot(inner) =>
      refs := ConstraintRealBiasRefsInModels(inner, models, current, inferredRefs);
    case CBinop(left, _, right) =>
      var leftRefs := ConstraintRealBiasRefsInModels(left, models, current, inferredRefs);
      var rightRefs := ConstraintRealBiasRefsInModels(right, models, current, inferredRefs);
      refs := leftRefs + rightRefs;
  }

  // Collects the solver constraints generated by one sequence of UVL
  // constraint sites.
  method UVLConstraintSeqTypeConstraintsInModels(
    uvlConstraints: seq<UVLConstraintSite>,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (constraints: seq<TypeConstraint>)
    requires current in models
    decreases |uvlConstraints|
  {
    if |uvlConstraints| == 0 {
      constraints := [];
    } else {
      var headConstraints := ConstraintTypeConstraintsInModels(ConstraintOf(uvlConstraints[0]), models, current, inferredRefs);
      var tailConstraints := UVLConstraintSeqTypeConstraintsInModels(uvlConstraints[1..], models, current, inferredRefs);
      constraints := headConstraints + tailConstraints;
    }
  }

  method GenerateTypeConstraintsInModels(
    uvlConstraints: seq<UVLConstraintSite>,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (constraints: seq<TypeConstraint>)
    requires current in models
  {
    constraints := UVLConstraintSeqTypeConstraintsInModels(uvlConstraints, models, current, inferredRefs);
  }

  method UVLConstraintSeqRealBiasRefsInModels(
    uvlConstraints: seq<UVLConstraintSite>,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (refs: set<Reference>)
    requires current in models
    decreases |uvlConstraints|
  {
    if |uvlConstraints| == 0 {
      refs := {};
    } else {
      var headRefs := ConstraintRealBiasRefsInModels(ConstraintOf(uvlConstraints[0]), models, current, inferredRefs);
      var tailRefs := UVLConstraintSeqRealBiasRefsInModels(uvlConstraints[1..], models, current, inferredRefs);
      refs := headRefs + tailRefs;
    }
  }

  method GenerateRealBiasRefsInModels(
    uvlConstraints: seq<UVLConstraintSite>,
    models: ModelEnv,
    current: ModelPath,
    inferredRefs: set<Reference>
  ) returns (refs: set<Reference>)
    requires current in models
  {
    refs := UVLConstraintSeqRealBiasRefsInModels(uvlConstraints, models, current, inferredRefs);
  }

  method ApplyNumericBiasToSolution(
    solution: map<Reference, FeatureType>,
    domains: map<Reference, set<FeatureType>>,
    realBiasedRefs: set<Reference>
  ) returns (biased: map<Reference, FeatureType>)
  {
    biased := map[];
    var unchecked: set<Reference> := set reference | reference in solution :: reference;
    while unchecked != {}
      invariant unchecked <= set reference | reference in solution :: reference
      invariant forall reference :: reference in biased <==> reference in solution && reference !in unchecked
      decreases |unchecked|
    {
      var reference: Reference :| reference in unchecked;
      var featureType := solution[reference];
      if reference in domains &&
         domains[reference] == {FTInteger, FTReal} &&
         reference !in realBiasedRefs {
        featureType := FTInteger;
      }
      biased := biased[reference := featureType];
      unchecked := unchecked - {reference};
    }
  }

  function SolutionIntroTypesInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant,
    solution: map<Reference, FeatureType>
  ): map<Reference, FeatureType>
    requires current in models
  {
    map reference | reference in solution &&
                    IsAdmissibleIntroReference(models[current], variant, reference) &&
                    DeclaredReferenceTypeInModels(models, current, reference).None? ::
      solution[reference]
  }

  // Steps 1 to 4:
  // 1. extract contributing UVL constraints
  // 2. collect owner-qualified introduced references whose types must be inferred
  // 3. generate typing constraints
  // 4. solve them and validate the inferred map against IntroTypesOKInModels
  method InferIntroTypesInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant
  ) returns (result: option<map<Reference, FeatureType>>)
    requires current in models
    ensures result.Some? ==> IntroTypesOKInModels(models, current, variant, result.value)
  {
    var uvlConstraints := ExtractUVLConstraints(models[current]);
    var inferredRefs := ExtractIntroducibleRefs(uvlConstraints, models[current], variant);
    var typeConstraints := GenerateTypeConstraintsInModels(uvlConstraints, models, current, inferredRefs);
    var realBiasedRefs := GenerateRealBiasRefsInModels(uvlConstraints, models, current, inferredRefs);
    var solverResult := SolveTypeConstraints(typeConstraints);
    match solverResult
    case Contradiction(_) =>
      result := None;
    case Underconstrained(domains) =>
      {
        var concretised := ConcretiseDomains(domains);
        match concretised
        case None =>
          result := None;
        case Some(solution) =>
          // The bias approach was added afterwards. Instead of concretising
          // and then correcting, we could refactor.
          var biasedSolution := ApplyNumericBiasToSolution(solution, domains, realBiasedRefs);
          var introTypes := SolutionIntroTypesInModels(models, current, variant, biasedSolution);
          if ConstraintsWellTypedInModels(models, current, introTypes, variant) {
            result := Some(introTypes);
          } else {
            result := None;
          }
      }
    case Solved(solution) =>
      var introTypes := SolutionIntroTypesInModels(models, current, variant, solution);
      if ConstraintsWellTypedInModels(models, current, introTypes, variant) {
        result := Some(introTypes);
      } else {
        result := None;
      }
  }
}
