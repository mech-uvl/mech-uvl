// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module defines the structural semantics for the feature tree declared
// directly in one model. It checks that selected occurrences form valid root,
// child-feature, and group instances with respect to feature multiplicities
// and group cardinalities. Imported-root attachments are handled in a separate
// module.

module UVL_StructuralSemantics {
  import opened ExtLib.Option
  import opened UVL_Syntax
  import opened UVL_Environment
  import opened UVL_Variant
  import opened UVL_Configuration
  import opened UVL_ModelsWF
  import opened UVL_ModelsTypeChecking

  ghost predicate SemanticEnv(models: ModelEnv, variant: SemVariant)
  {
    WF_Models(models, variant) &&
    WellTypedModels(models, variant)
  }

  function UpperBoundAllows(upper: UpperBound, count: nat): bool
  {
    match upper
    case FiniteUpper(value) => count <= value
    case UnboundedUpper => true
  }

  function CardinalityAllows(cardinality: Cardinality, count: nat): bool
  {
    cardinality.lower <= count &&
    UpperBoundAllows(cardinality.upper, count)
  }

  function SelectedFeatureCountUnder(features: seq<Feature>, cfg: Configuration, parent: OccRef): nat
    decreases |features|
  {
    if |features| == 0 then
      0
    else
      (if |SelectedExtensionsBy(cfg, parent, features[0].name)| != 0 then 1 else 0) +
      SelectedFeatureCountUnder(features[1..], cfg, parent)
  }

  function OptionalFeatureMultiplicityAllows(feature: Feature, count: nat): bool
  {
    if count == 0 then
      true
    else
      match feature.cardinality
      case None => count == 1
      case Some(cardinality) => CardinalityAllows(cardinality, count)
  }

  function RootFeatureMultiplicityAllows(feature: Feature, count: nat): bool
  {
    match feature.cardinality
    case None => count == 1
    case Some(cardinality) => CardinalityAllows(cardinality, count)
  }

  predicate GroupSelectionOK(group: Group, cfg: Configuration, parent: OccRef)
  {
    var selectedCount := SelectedFeatureCountUnder(group.features, cfg, parent);
    match group.kind
    case MandatoryGroup => selectedCount == |group.features|
    case OptionalGroup => true
    case OrGroup => 1 <= selectedCount
    case AlternativeGroup => selectedCount == 1
    case CardinalityGroup(cardinality) => CardinalityAllows(cardinality, selectedCount)
  }

  predicate NestedFeatureStructureOK(feature: Feature, cfg: Configuration, parent: OccRef)
    decreases feature, 1
  {
    var occurrences := SelectedExtensionsBy(cfg, parent, feature.name);
    OptionalFeatureMultiplicityAllows(feature, |occurrences|) &&
    (forall occurrence :: occurrence in occurrences ==>
                            FeatureOccurrenceStructureOK(feature, cfg, occurrence))
  }

  predicate FeatureOccurrenceStructureOK(feature: Feature, cfg: Configuration, occurrence: OccRef)
    decreases feature, 0
  {
    (forall i :: 0 <= i < |feature.groups| ==>
                   GroupSelectionOK(feature.groups[i], cfg, occurrence)) &&
    (forall i, j :: 0 <= i < |feature.groups| &&
                    0 <= j < |feature.groups[i].features| ==>
                      NestedFeatureStructureOK(feature.groups[i].features[j], cfg, occurrence))
  }

  predicate RootFeatureStructureOK(root: Feature, cfg: Configuration)
    decreases root
  {
    var occurrences := SelectedOccurrencesOf(cfg, root.name);
    RootFeatureMultiplicityAllows(root, |occurrences|) &&
    (forall occurrence :: occurrence in occurrences ==>
                            FeatureOccurrenceStructureOK(root, cfg, occurrence))
  }

}
