// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module analyses the reference occurrences that appear inside
// expressions, constraints, and aggregates. It separates ordinary references
// and introducible attribute references.  Introducible attribute references
// are attribute references that are not declared but used in constraints:
// they are *introduced* by the constraint. The semantic variant controls
// whether and where it is allowed to introduce attributes in this way.
// It also defines the collectors for introduced references admitted by each
// semantic variant. Type checking, use checking, and type inference all
// depend on this reference analysis layer.

module UVL_References {
  import opened ExtLib.Option
  import opened ExtLib.SeqFoldLeft
  import opened ExtLib.SeqSetUnion
  import opened UVL_Syntax
  import opened UVL_TypingEnvironment
  import opened UVL_Variant

  // Returns the owner part of an owner-qualified attribute reference.
  function AttributeOwner(reference: Reference): Reference
    requires 1 < |reference|
  {
    reference[..|reference| - 1]
  }

  // Recognises ordinary owner-qualified attribute references that are not yet
  // declared in the current model.
  function IsIntroducibleAttributeReference(model: FeatureModel, reference: Reference): bool
  {
    1 < |reference| &&
    reference !in TypeEnv(model) &&
    AttributeOwner(reference) in RootFeatureTypeEnv(model)
  }

  // Recognises the bare attribute key used as the target of sum/avg
  // aggregates.
  function IsBareAggregateTargetKey(reference: Reference): bool
  {
    |reference| == 1
  }

  // Returns whether one reference stays within the subtree rooted at owner.
  function ReferenceLocalTo(owner: Reference, reference: Reference): bool
  {
    |owner| <= |reference| && reference[..|owner|] == owner
  }

  // Collects ordinary references mentioned by one aggregate expression. Bare
  // aggregate targets for sum/avg are excluded, since they are not ordinary
  // owner qualified references.
  function ReferencesInAggregate(aggregate: AggregateFunction): set<Reference>
  {
    match aggregate
    case Sum(_, scope) =>
      (match scope
       case None => {}
       case Some(reference) => {reference})
    case Avg(_, scope) =>
      (match scope
       case None => {}
       case Some(reference) => {reference})
    case Len(target) => {target}
    case Floor(target) => {target}
    case Ceil(target) => {target}
  }

  // Collects ordinary references mentioned by one expression.
  function ReferencesInExpression(expression: Expression): set<Reference>
    decreases expression
  {
    match expression
    case EInt(_) => {}
    case EFloat(_) => {}
    case EString(_) => {}
    case ERef(reference) => {reference}
    case EAggr(aggregate) => ReferencesInAggregate(aggregate)
    case EBinop(left, _, right) =>
      ReferencesInExpression(left) + ReferencesInExpression(right)
  }

  // Collects ordinary references mentioned by one equation.
  function ReferencesInEquation(equation: Equation): set<Reference>
  {
    ReferencesInExpression(equation.left) + ReferencesInExpression(equation.right)
  }

  // Collects ordinary references mentioned by one constraint.
  function ReferencesInConstraint(constraint: Constraint): set<Reference>
    decreases constraint
  {
    match constraint
    case CRef(reference) => {reference}
    case CEquation(equation) => ReferencesInEquation(equation)
    case CNot(inner) => ReferencesInConstraint(inner)
    case CBinop(left, _, right) =>
      ReferencesInConstraint(left) + ReferencesInConstraint(right)
  }

  // Collects the introducible attribute references mentioned by one constraint.
  function IntroducibleAttrRefsInConstraint(constraint: Constraint, model: FeatureModel): set<Reference>
  {
    set reference | reference in ReferencesInConstraint(constraint) && IsIntroducibleAttributeReference(model, reference) :: reference
  }

  function GetIntroRefsFromConstraint(constraint: Constraint, model: FeatureModel): set<Reference>
    decreases constraint
  {
    match constraint
    case CRef(reference) =>
      if IsIntroducibleAttributeReference(model, reference) then {reference} else {}
    case CEquation(equation) =>
      set reference | reference in ReferencesInEquation(equation) && IsIntroducibleAttributeReference(model, reference) :: reference
    case CNot(inner) =>
      GetIntroRefsFromConstraint(inner, model)
    case CBinop(left, _, right) =>
      GetIntroRefsFromConstraint(left, model) + GetIntroRefsFromConstraint(right, model)
  }

  function GetIntroRefsFromLocalConstraint(
    owner: Reference,
    constraint: Constraint,
    model: FeatureModel,
    localScopeOnly: bool
  ): set<Reference>
  {
    if !localScopeOnly then
      GetIntroRefsFromConstraint(constraint, model)
    else
      set reference |
        reference in GetIntroRefsFromConstraint(constraint, model) &&
        ReferenceLocalTo(owner, reference) ::
        reference
  }

  function GetIntroRefsFromAttribute(
    owner: Reference,
    attribute: Attribute,
    model: FeatureModel,
    localScopeOnly: bool
  ): set<Reference>
  {
    match attribute
    case AValue(_) => {}
    case ASingleConstraint(constraint) =>
      GetIntroRefsFromLocalConstraint(owner, constraint, model, localScopeOnly)
    case AListConstraints(constraints) =>
      Union(
        seq(|constraints|, i =>
          if 0 <= i < |constraints| then
            GetIntroRefsFromLocalConstraint(owner, constraints[i], model, localScopeOnly)
          else
            {}))
  }

  function GetIntroRefsFromAttributeSeq(
    owner: Reference,
    attributes: seq<Attribute>,
    model: FeatureModel,
    localScopeOnly: bool
  ): set<Reference>
  {
    Union(
      seq(|attributes|, i =>
        if 0 <= i < |attributes| then
          GetIntroRefsFromAttribute(owner, attributes[i], model, localScopeOnly)
        else
          {}))
  }

  function GetIntroRefsFromFeature(feature: Feature, model: FeatureModel, localScopeOnly: bool): set<Reference>
    decreases feature
  {
    GetIntroRefsFromAttributeSeq(feature.name, feature.attributes, model, localScopeOnly) +
    Union(
      seq(|feature.groups|, i =>
        if 0 <= i < |feature.groups| then
          Union(
            seq(|feature.groups[i].features|, j =>
              if 0 <= j < |feature.groups[i].features| then
                GetIntroRefsFromFeature(feature.groups[i].features[j], model, localScopeOnly)
              else
                {}))
        else
          {}))
  }

  function GetAdmissibleIntroRefs(model: FeatureModel, variant: SemVariant): set<Reference>
  {
    match variant.attrIntro
    case DeclaredOnly =>
      {}
    case LocalIntro(localScopeOnly) =>
      (match model.rootFeature
       case None => {}
       case Some(root) => GetIntroRefsFromFeature(root, model, localScopeOnly))
    case GlobalIntro =>
      Union(
        seq(|model.constraints|, i =>
          if 0 <= i < |model.constraints| then
            GetIntroRefsFromConstraint(model.constraints[i], model)
          else
            {})) +
      (match model.rootFeature
       case None => {}
       case Some(root) => GetIntroRefsFromFeature(root, model, false))
  }

  predicate IsAdmissibleIntroReference(
    model: FeatureModel,
    variant: SemVariant,
    reference: Reference
  )
  {
    reference in GetAdmissibleIntroRefs(model, variant)
  }

}
