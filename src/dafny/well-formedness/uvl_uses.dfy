// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module defines when names, references, and aggregate uses are valid
// inside a model environment. It states the logical conditions checked by the
// executable use-check layer.



module UVL_ModelsUses {
  import opened ExtLib.Option
  import opened UVL_Syntax
  import opened UVL_Environment
  import opened UVL_References
  import opened UVL_ModelsResolution
  import opened UVL_TypingEnvironment
  import opened UVL_Variant

  // A feature tree attachment may either declare a local feature name or
  // denote exactly the root of an imported model.
  predicate ImportedRootAttachmentInModels(
    models: ModelEnv,
    current: ModelPath,
    reference: Reference
  ) requires current in models
  {
    match ResolveReference(models, current, reference)
    case Some(ResolvedFeature(path, target)) =>
      if path != current && path in models then
        match models[path].rootFeature
        case Some(root) => target == root.name
        case None => false
      else
        false
    case Some(ResolvedAttribute(_, _, _)) =>
      false
    case None =>
      false
  }

  predicate ValidFeatureTreeNameInModels(
    models: ModelEnv,
    current: ModelPath,
    reference: Reference
  ) requires current in models
  {
    |reference| == 1 || ImportedRootAttachmentInModels(models, current, reference)
  }

  // Reference occurrences are valid when they resolve in the model environment
  // or denote a locally introducible attribute.
  predicate ValidReferenceOccurrenceInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant,
    reference: Reference
  ) requires current in models
  {
    ResolveReference(models, current, reference).Some? ||
    IsAdmissibleIntroReference(models[current], variant, reference)
  }

  // The validity of an attribute reference as an argument of an aggregation
  // depends on the semantic variant. Introducible attribute references may be
  // allowed or not.
  predicate ValidAggregateUseInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant,
    aggregate: AggregateFunction
  ) requires current in models
  {
    match aggregate
    case Sum(target, scope) =>
      IsBareAggregateTargetKey(target) &&
      (match scope
       case None => true
       case Some(reference) =>
         match ResolveReference(models, current, reference)
         case Some(ResolvedFeature(_, _)) => true
         case _ => false)
    case Avg(target, scope) =>
      IsBareAggregateTargetKey(target) &&
      (match scope
       case None => true
       case Some(reference) =>
         match ResolveReference(models, current, reference)
         case Some(ResolvedFeature(_, _)) => true
         case _ => false)
    case Len(target) =>
      ValidReferenceOccurrenceInModels(models, current, variant, target)
    case Floor(target) =>
      ValidReferenceOccurrenceInModels(models, current, variant, target)
    case Ceil(target) =>
      ValidReferenceOccurrenceInModels(models, current, variant, target)
  }

  predicate ValidExpressionUsesInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant,
    expression: Expression
  ) requires current in models
    decreases expression
  {
    match expression
    case EInt(_) => true
    case EFloat(_) => true
    case EString(_) => true
    case ERef(reference) =>
      ValidReferenceOccurrenceInModels(models, current, variant, reference)
    case EAggr(aggregate) =>
      ValidAggregateUseInModels(models, current, variant, aggregate)
    case EBinop(left, _, right) =>
      ValidExpressionUsesInModels(models, current, variant, left) &&
      ValidExpressionUsesInModels(models, current, variant, right)
  }

  predicate ValidEquationUsesInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant,
    equation: Equation
  ) requires current in models
  {
    ValidExpressionUsesInModels(models, current, variant, equation.left) &&
    ValidExpressionUsesInModels(models, current, variant, equation.right)
  }

  predicate ValidConstraintUsesInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant,
    constraint: Constraint
  ) requires current in models
    decreases constraint
  {
    match constraint
    case CRef(reference) =>
      ValidReferenceOccurrenceInModels(models, current, variant, reference)
    case CEquation(equation) =>
      ValidEquationUsesInModels(models, current, variant, equation)
    case CNot(inner) =>
      ValidConstraintUsesInModels(models, current, variant, inner)
    case CBinop(left, _, right) =>
      ValidConstraintUsesInModels(models, current, variant, left) &&
      ValidConstraintUsesInModels(models, current, variant, right)
  }

  predicate ValidAttributeUsesInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant,
    attribute: Attribute
  ) requires current in models
  {
    match attribute
    case AValue(_) => true
    case ASingleConstraint(constraint) =>
      ValidConstraintUsesInModels(models, current, variant, constraint)
    case AListConstraints(constraints) =>
      forall i :: 0 <= i < |constraints| ==>
                    ValidConstraintUsesInModels(models, current, variant, constraints[i])
  }

  predicate ValidFeatureUsesInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant,
    feature: Feature
  ) requires current in models
    decreases feature
  {
    ValidFeatureTreeNameInModels(models, current, feature.name) &&
    (forall i :: 0 <= i < |feature.attributes| ==>
                   ValidAttributeUsesInModels(models, current, variant, feature.attributes[i])) &&
    (forall i :: 0 <= i < |feature.groups| ==>
                   forall j :: 0 <= j < |feature.groups[i].features| ==>
                                 ValidFeatureUsesInModels(models, current, variant, feature.groups[i].features[j]))
  }

  predicate ValidModelUsesInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant
  ) requires current in models
  {
    (forall i :: 0 <= i < |models[current].constraints| ==>
                   ValidConstraintUsesInModels(models, current, variant, models[current].constraints[i])) &&
    match models[current].rootFeature
    case None => true
    case Some(root) => ValidFeatureUsesInModels(models, current, variant, root)
  }
}
