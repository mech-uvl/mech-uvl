// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

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
}
