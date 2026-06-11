// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module defines local structural well-formedness for a single feature
// model. It extracts declared feature names, declared attribute keys, and
// visible import qualifiers from syntax. Its predicates express uniqueness
// of feature identifiers, attribute keys, import aliases, and visible
// qualifiers. The executable local checks are specified against these
// predicates.

module UVL_WellFormedness {
  import opened Std.Collections.Seq
  import opened ExtLib.Option
  import opened ExtLib.SeqNoDup
  import opened ExtLib.SeqMap
  import opened UVL_Path
  import opened UVL_Syntax


  // Collects the plain attribute names declared directly on one feature.
  function AttributeNames(attributes: seq<Attribute>): seq<string>
    decreases |attributes|
  {
    if |attributes| == 0 then
      []
    else
      match attributes[0]
      case AValue(MkAttr(key, _)) => [key] + AttributeNames(attributes[1..])
      case _ => AttributeNames(attributes[1..])
  }

  // Collects all declared feature names in one feature subtree.
  function FeatureNames(feature: Feature): seq<Reference>
    decreases feature
  {
    [feature.name] +
    Seq.Flatten(
      seq(|feature.groups|, i =>
        if 0 <= i < |feature.groups| then
          var features := feature.groups[i].features;
          Seq.Flatten(
            seq(|features|, k =>
              if 0 <= k < |features| then FeatureNames(features[k])
              else [])
          )
        else [])
    )
  }

  // Builds the feature-name to attribute-name-sequence map over one feature
  // subtree. This relies on feature names being unique in the subtree.
  function FeatureAttributeNameMap(feature: Feature): map<Reference, seq<string>>
    decreases feature
  {
    map[feature.name := AttributeNames(feature.attributes)] +
    FoldRight((acc, chunk) => chunk + acc,
              Flatten(
                seq(|feature.groups|, i =>
                  if 0 <= i < |feature.groups| then
                    seq(|feature.groups[i].features|, k =>
                      if 0 <= k < |feature.groups[i].features| then
                        FeatureAttributeNameMap(feature.groups[i].features[k])
                      else
                        map[])
                  else
                    [])), map[]
    )
  }

  function VisibleImportQualifier(importDecl: ImportDecl): Reference
  {
    match importDecl.alias
    case Some(alias) => alias
    case None => importDecl.importPath
  }

  function ImportAliases(imports: seq<ImportDecl>): seq<Reference>
    decreases |imports|
  {
    if |imports| == 0 then
      []
    else
      match imports[0].alias
      case Some(alias) => [alias] + ImportAliases(imports[1..])
      case None => ImportAliases(imports[1..])
  }

  // Checks that a reference is syntactically meaningful: it has at least one
  // path component and none of them are empty.
  predicate ValidReference(r: Reference)
  {
    forall i :: 0 <= i < |r| ==> r[i] != ""
  }

  // Checks that a cardinality describes a coherent interval of allowed counts.
  predicate ValidCardinality(c: Cardinality)
  {
    match c.upper
    case FiniteUpper(limit) => c.lower <= limit
    case UnboundedUpper => true
  }

  // Checks that all (nested) composite attribute do not have duplicate fields.
  // Satistifies the predicate if it is not a composite attribute.
  predicate ValidRecordAttribute(attrDef: AttributeDef)
  {
    (attrDef.value.Some? &&
     ((attrDef.value.value.VRecord? &&
       HasNoDup(FMap((ad: AttributeDef)=>ad.key, attrDef.value.value.attributes)) &&
       forall ad :: ad in attrDef.value.value.attributes ==> ValidRecordAttribute(ad))
      || (attrDef.value.value.VVector? &&
          forall av :: av in attrDef.value.value.elements ==>
                         av.VRecord? &&
                         HasNoDup(FMap((ad: AttributeDef)=>ad.key, av.attributes)) &&
                         forall ad :: ad in av.attributes ==> ValidRecordAttribute(ad))
      || (!attrDef.value.value.VRecord? && !attrDef.value.value.VVector?)))
    || attrDef.value.None?
  }

  // Checks that all declared feature names in the tree are pairwise distinct.
  // Plain reference occurrences in imports, attributes, and constraints are ignored.
  predicate UniqueIdentifiers(model: FeatureModel)
  {
    match model.rootFeature
    case None => true
    case Some(root) => HasNoDup(FeatureNames(root))
  }

  // Checks that each feature declares each plain attribute name at most once.
  predicate UniqueAttributeNames(model: FeatureModel)
  {
    match model.rootFeature
    case None => true
    case Some(root) =>
      var names := FeatureAttributeNameMap(root);
      forall reference :: reference in names ==> HasNoDup(names[reference])
  }

  // TODO: decide whether import aliases must be single identifiers rather
  // than arbitrary references. If yes, add a dedicated local WF predicate.
  predicate UniqueImportAliases(model: FeatureModel)
  {
    HasNoDup(ImportAliases(model.imports))
  }

  // Visible import qualifiers must be prefix-free. Otherwise a reference such
  // as a.b.C could be split either as qualifier a with internal reference b.C,
  // or as qualifier a.b with internal reference C.
  predicate PrefixFreeImportQualifiers(model: FeatureModel)
  {
    forall i, j | 0 <= i < j < |model.imports| ::
      !HasPrefix(VisibleImportQualifier(model.imports[i]), VisibleImportQualifier(model.imports[j]))
      &&
      !HasPrefix(VisibleImportQualifier(model.imports[j]), VisibleImportQualifier(model.imports[i]))
  }
}
