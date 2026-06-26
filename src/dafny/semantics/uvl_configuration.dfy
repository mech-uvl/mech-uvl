// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module defines configurations and basic operations on feature
// occurrences.
// A configuration records three finite components: the set of selected feature
// occurrences, a partial map assigning values to selected typed-feature
// occurrences, and a partial map assigning values to attributes of selected
// occurrences. Occurrence references are UVL references whose path components
// carry cardinality indices.

module UVL_Configuration {
  import opened UVL_Path
  import opened UVL_Syntax

  type Index = i: nat | 1 <= i witness 1

  // Configurations talk about concrete feature occurrences, not just names.
  datatype OccurrenceId =
    | OccurrenceId(name: Id, index: Index)

  type OccRef = Path<OccurrenceId>

  datatype FeatureValue =
    | VBool(boolValue: bool)
    | VInt(intValue: IntType)
    | VReal(realValue: RealType)
    | VString(stringValue: StringType)

  datatype AttributeRef =
    | AttributeRef(owner: OccRef, key: Id)

  datatype Configuration = Configuration(
    selected: set<OccRef>,
    featureValues: map<OccRef, FeatureValue>,
    attributeValues: map<AttributeRef, AttributeValue>
  )

  predicate WF_Configuration(cfg: Configuration)
  {
    (forall feature :: feature in cfg.featureValues ==>
                         feature in cfg.selected) &&
    (forall attribute :: attribute in cfg.attributeValues ==>
                           attribute.owner in cfg.selected)
  }

  // Erases occurrence indices from a concrete occurrence reference.
  function ToRef(occurrence: OccRef): Reference
    ensures |ToRef(occurrence)| == |occurrence|
    ensures forall i :: 0 <= i < |occurrence| ==> ToRef(occurrence)[i] == occurrence[i].name
  {
    seq(|occurrence|, i =>
      if 0 <= i < |occurrence| then occurrence[i].name else "")
  }

  // Checks that a concrete occurrence denotes a given UVL reference.
  predicate OccurrenceOf(occurrence: OccRef, reference: Reference)
  {
    ToRef(occurrence) == reference
  }

  // Checks whether `child` extends `parent` by the given UVL reference.
  predicate ExtendsBy(child: OccRef, parent: OccRef, reference: Reference)
  {
    |parent| < |child| &&
    child[..|parent|] == parent &&
    ToRef(child[|parent|..]) == reference
  }

  // Checks whether `descendant` is below `ancestor`, allowing equality.
  predicate DescendantOf(descendant: OccRef, ancestor: OccRef)
  {
    HasPrefix(descendant, ancestor)
  }

  // Selects the concrete occurrences whose projected reference is `reference`.
  function SelectedOccurrencesOf(cfg: Configuration, reference: Reference): set<OccRef>
  {
    set occurrence: OccRef |
      occurrence in cfg.selected &&
      OccurrenceOf(occurrence, reference) :: occurrence
  }

  // Selects the occurrences that extend `parent` by `reference`.
  function SelectedExtensionsBy(cfg: Configuration, parent: OccRef, reference: Reference): set<OccRef>
  {
    set occurrence: OccRef |
      occurrence in cfg.selected &&
      ExtendsBy(occurrence, parent, reference) :: occurrence
  }
}
