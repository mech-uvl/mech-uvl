// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module defines typing for references, aggregates,  expressions,
// constraints, and models. The model environment is taken into account. It
// combines resolution, declared typing environments, introduced-attribute
// types, and semantic variant options. Its predicates are the logical typing
// conditions checked by the executable typing layer. It is the main typing
// specification layer over model environments.

module UVL_ModelsTypeChecking {
  import opened ExtLib.Option
  import opened ExtLib.SeqSetUnion
  import opened UVL_Syntax
  import opened UVL_Environment
  import opened UVL_WellFormedness
  import opened UVL_References
  import opened UVL_TypingEnvironment
  import opened UVL_ModelsResolution
  import opened UVL_Variant

  // Recognises the numeric fragment of feature types.
  predicate NumericFeatureType(t: FeatureType)
  {
    t == FTInteger || t == FTReal
  }

  // Computes the result type of an arithmetic binary expression when the
  // operand types are compatible.
  function ArithmeticResultType(
    op: ArithmeticOp,
    leftType: FeatureType,
    rightType: FeatureType
  ): option<FeatureType>
  {
    if leftType == FTInteger && rightType == FTInteger then
      if op == Div then Some(FTReal) else Some(FTInteger)
    else if NumericFeatureType(leftType) && NumericFeatureType(rightType) then
      Some(FTReal)
    else
      None
  }

  // Declared reference types are resolved through the models environment, so
  // imported references contribute their declared type from the referenced
  // model.
  function DeclaredReferenceTypeInModels(
    models: ModelEnv,
    current: ModelPath,
    reference: Reference
  ): option<FeatureType>
    requires current in models
  {
    match ResolveReference(models, current, reference)
    case None => None
    case Some(ResolvedFeature(path, target)) =>
      if path in models then
        var declaredTypes := TypeEnv(models[path]);
        if target in declaredTypes then Some(declaredTypes[target]) else None
      else
        None
    case Some(ResolvedAttribute(path, owner, key)) =>
      if path in models then
        var declaredTypes := TypeEnv(models[path]);
        var target := owner + [key];
        if target in declaredTypes then Some(declaredTypes[target]) else None
      else
        None
  }

  datatype ReferenceKind =
    | UnknownReference
    | FeatureReference
    | AttributeValueReference

  // Classifies one reference after resolution.
  function ReferenceKindInModels(
    models: ModelEnv,
    current: ModelPath,
    reference: Reference
  ): ReferenceKind
    requires current in models
  {
    match ResolveReference(models, current, reference)
    case None => UnknownReference
    case Some(ResolvedFeature(_, _)) => FeatureReference
    case Some(ResolvedAttribute(_, _, _)) => AttributeValueReference
  }

  // Introduced attribute types remain local to the model being checked. All
  // other references are looked up in the declared models environment.
  function ReferenceTypeInModels(
    models: ModelEnv,
    current: ModelPath,
    reference: Reference,
    introTypes: map<Reference, FeatureType>
  ): option<FeatureType>
    requires current in models
  {
    if 1 < |reference| && reference in introTypes then
      Some(introTypes[reference])
    else
      DeclaredReferenceTypeInModels(models, current, reference)
  }

  // Looks up the type of one attribute key on one concrete feature. Local
  // introduced attributes are taken from `introTypes`. Imported models
  // contribute only their declared attributes.
  function AttributeKeyTypeOnFeatureInModels(
    models: ModelEnv,
    ownerPath: ModelPath,
    current: ModelPath,
    owner: Reference,
    key: string,
    introTypes: map<Reference, FeatureType>
  ): option<FeatureType>
    requires ownerPath in models
    requires current in models
  {
    var reference := owner + [key];
    if ownerPath == current && reference in introTypes then
      Some(introTypes[reference])
    else if reference in TypeEnv(models[ownerPath]) then
      Some(TypeEnv(models[ownerPath])[reference])
    else
      None
  }

  function AggregateTargetKeyTypesInFeatureAuxInModels(
    key: string,
    scope: option<Reference>,
    feature: Feature,
    models: ModelEnv,
    ownerPath: ModelPath,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>,
    active: bool
  ): set<FeatureType>
    requires ownerPath in models
    requires current in models
    decreases feature
  {
    var hereActive := active || (match scope
                                 case None => true
                                 case Some(reference) => feature.name == reference);
    (match AttributeKeyTypeOnFeatureInModels(models, ownerPath, current, feature.name, key, introTypes)
     case None => {}
     case Some(featureType) =>
       if hereActive then {featureType} else {}) +
    Union(
      seq(|feature.groups|, i =>
        if 0 <= i < |feature.groups| then
          Union(
            seq(|feature.groups[i].features|, j =>
              if 0 <= j < |feature.groups[i].features| then
                AggregateTargetKeyTypesInFeatureAuxInModels(
                  key,
                  scope,
                  feature.groups[i].features[j],
                  models,
                  ownerPath,
                  current,
                  introTypes,
                  hereActive)
              else
                {}))
        else
          {}))
  }

  function AggregateTargetFamilyTypeInModels(types: set<FeatureType>): option<FeatureType>
  {
    if types == {} then
      None
    else if forall featureType :: featureType in types ==> NumericFeatureType(featureType) then
      if FTReal in types then Some(FTReal) else Some(FTInteger)
    else
      None
  }

  function AggregateTargetFamilyTypeInScopeInModels(
    key: string,
    scope: option<Reference>,
    models: ModelEnv,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>
  ): option<FeatureType>
    requires current in models
  {
    if scope.None? then
      match models[current].rootFeature
      case None => None
      case Some(root) =>
        AggregateTargetFamilyTypeInModels(
          AggregateTargetKeyTypesInFeatureAuxInModels(
            key,
            None,
            root,
            models,
            current,
            current,
            introTypes,
            true))
    else
      match ResolveReference(models, current, scope.value)
      case Some(ResolvedFeature(path, targetFeature)) =>
        if path in models then
          match models[path].rootFeature
          case None => None
          case Some(root) =>
            AggregateTargetFamilyTypeInModels(
              AggregateTargetKeyTypesInFeatureAuxInModels(
                key,
                Some(targetFeature),
                root,
                models,
                path,
                current,
                introTypes,
                false))
        else
          None
      case _ => None
  }

  // Computes the type of an aggregate expression relative to one current
  // model inside the models environment.
  function AggregateExpressionTypeInModels(
    aggregate: AggregateFunction,
    models: ModelEnv,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>
  ): option<FeatureType>
    requires current in models
  {
    match aggregate
    case Sum(target, scope) =>
      if IsBareAggregateTargetKey(target) then
        AggregateTargetFamilyTypeInScopeInModels(target[0], scope, models, current, introTypes)
      else
        None
    case Avg(target, scope) =>
      if IsBareAggregateTargetKey(target) then
        match AggregateTargetFamilyTypeInScopeInModels(target[0], scope, models, current, introTypes)
        case Some(_) => Some(FTReal)
        case None => None
      else
        None
    case Len(target) =>
      if ReferenceTypeInModels(models, current, target, introTypes) == Some(FTString) then
        Some(FTInteger)
      else
        None
    case Floor(target) =>
      if ReferenceTypeInModels(models, current, target, introTypes) == Some(FTReal) then
        Some(FTInteger)
      else
        None
    case Ceil(target) =>
      if ReferenceTypeInModels(models, current, target, introTypes) == Some(FTReal) then
        Some(FTInteger)
      else
        None
  }

  // Infers the static type of an expression relative to one current model in
  // the models environment.
  function ExpressionTypeInModels(
    expression: Expression,
    models: ModelEnv,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>
  ): option<FeatureType>
    requires current in models
    decreases expression
  {
    match expression
    case EInt(_) => Some(FTInteger)
    case EFloat(_) => Some(FTReal)
    case EString(_) => Some(FTString)
    case ERef(reference) =>
      ReferenceTypeInModels(models, current, reference, introTypes)
    case EAggr(aggregate) =>
      AggregateExpressionTypeInModels(aggregate, models, current, introTypes)
    case EBinop(left, op, right) =>
      match ExpressionTypeInModels(left, models, current, introTypes)
      case None => None
      case Some(leftType) =>
        match ExpressionTypeInModels(right, models, current, introTypes)
        case None => None
        case Some(rightType) => ArithmeticResultType(op, leftType, rightType)
  }

  predicate WellTypedEquationInModels(
    equation: Equation,
    models: ModelEnv,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>
  )
    requires current in models
  {
    match ExpressionTypeInModels(equation.left, models, current, introTypes)
    case None => false
    case Some(leftType) =>
      match ExpressionTypeInModels(equation.right, models, current, introTypes)
      case None => false
      case Some(rightType) =>
        if equation.op == Eq || equation.op == Neq then
          leftType == rightType ||
          (NumericFeatureType(leftType) && NumericFeatureType(rightType))
        else
          (NumericFeatureType(leftType) && NumericFeatureType(rightType)) ||
          (leftType == FTString && rightType == FTString)
  }

  function BoolLiteralReferenceAllowedInModels(
    reference: Reference,
    models: ModelEnv,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>,
    variant: SemVariant
  ): bool
    requires current in models
  {
    match ReferenceTypeInModels(models, current, reference, introTypes)
    case None => false
    case Some(featureType) =>
      featureType == FTBoolean ||
      (variant.typedFeatureAsBool && ReferenceKindInModels(models, current, reference) == FeatureReference)
  }

  // Checks that a constraint only uses references, expressions, and
  // constraints in a type correct way.
  predicate WellTypedConstraintInModels(
    constraint: Constraint,
    models: ModelEnv,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>,
    variant: SemVariant
  )
    requires current in models
    decreases constraint
  {
    match constraint
    case CRef(reference) =>
      BoolLiteralReferenceAllowedInModels(reference, models, current, introTypes, variant)
    case CEquation(equation) =>
      WellTypedEquationInModels(equation, models, current, introTypes)
    case CNot(inner) =>
      WellTypedConstraintInModels(inner, models, current, introTypes, variant)
    case CBinop(left, _, right) =>
      WellTypedConstraintInModels(left, models, current, introTypes, variant) &&
      WellTypedConstraintInModels(right, models, current, introTypes, variant)
  }

  // Checks that a feature's own attributes and all nested groups are
  // well typed.
  predicate FeatureAttributesWellTypedInModels(
    feature: Feature,
    models: ModelEnv,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>,
    variant: SemVariant
  )
    requires current in models
    decreases feature
  {
    (forall i :: 0 <= i < |feature.attributes| ==>
                   match feature.attributes[i]
                   case ASingleConstraint(constraint) =>
                     WellTypedConstraintInModels(constraint, models, current, introTypes, variant)
                   case AListConstraints(constraints) =>
                     forall j :: 0 <= j < |constraints| ==> WellTypedConstraintInModels(constraints[j], models, current, introTypes, variant)
                   case _ =>
                     true) &&
    forall i :: 0 <= i < |feature.groups| ==>
                  forall j :: 0 <= j < |feature.groups[i].features| ==>
                                FeatureAttributesWellTypedInModels(feature.groups[i].features[j], models, current, introTypes, variant)
  }

  // Checks that all global and local constraints are well typed.
  predicate ConstraintsWellTypedInModels(
    models: ModelEnv,
    current: ModelPath,
    introTypes: map<Reference, FeatureType>,
    variant: SemVariant
  )
    requires current in models
  {
    (forall i :: 0 <= i < |models[current].constraints| ==>
                   WellTypedConstraintInModels(models[current].constraints[i], models, current, introTypes, variant)) &&
    match models[current].rootFeature
    case None => true
    case Some(root) => FeatureAttributesWellTypedInModels(root, models, current, introTypes, variant)
  }

  // Checks that one inferred type map is admissible under the chosen semantic
  // variant and suffices to type all constraints of the current model in the
  // models environment.
  ghost predicate IntroTypesOKInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant,
    introTypes: map<Reference, FeatureType>
  )
    requires current in models
  {
    (forall reference :: reference in introTypes ==>
                           (IsAdmissibleIntroReference(models[current], variant, reference) &&
                            DeclaredReferenceTypeInModels(models, current, reference).None?)) &&
    ConstraintsWellTypedInModels(models, current, introTypes, variant)
  }

  ghost predicate WellTypedModelInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant
  )
    requires current in models
  {
    WF_SemVariant(variant) &&
    UniqueIdentifiers(models[current]) &&
    exists introTypes :: IntroTypesOKInModels(models, current, variant, introTypes)
  }

  ghost predicate WellTypedModels(models: ModelEnv, variant: SemVariant)
  {
    forall current :: current in models ==> WellTypedModelInModels(models, current, variant)
  }
}
