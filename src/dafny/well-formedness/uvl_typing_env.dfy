// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only


// This module builds the declared typing environments induced by a feature
// model. It collects declared feature types and declared primitive attribute
// types, then combines them into the reference to type map used by later
// typing-oriented layers.
module UVL_TypingEnvironment {
  import opened Std.Collections.Seq
  import opened ExtLib.Option
  import opened ExtLib.SeqMapMerge
  import opened UVL_Syntax

  // Builds the identifier-to-type environment for a feature together with all
  // identifiers declared below it.
  function FeatureTypeEnv(feature: Feature): map<Reference, FeatureType>
    decreases feature
  {
    map[feature.name :=
          (match feature.featureType
           case None => FTBoolean
           case Some(t) => t)] +
    Merge(
      Flatten(
        seq(|feature.groups|, i =>
          if 0 <= i < |feature.groups| then
            seq(|feature.groups[i].features|, k =>
              if 0 <= k < |feature.groups[i].features| then
                FeatureTypeEnv(feature.groups[i].features[k])
              else
                map[])
          else
            []))
    )
  }

  // Returns the feature-type environment induced by the root of the model.
  function RootFeatureTypeEnv(model: FeatureModel): map<Reference, FeatureType>
  {
    match model.rootFeature
    case None => map[]
    case Some(root) => FeatureTypeEnv(root)
  }

  // Extracts the type information contributed by one attribute declaration.
  // We consider composite and vector attributes are meta-data and cannot be
  // used in constraints: they are not given a type.
  function AttrTypeEnv(owner: Reference, attribute: Attribute): map<Reference, FeatureType>
  {
    match attribute
    case AValue(MkAttr(key, None)) =>
      map[owner + [key] := FTBoolean]
    case AValue(MkAttr(key, Some(value))) =>
      (match value
       case VBool(_) => map[owner + [key] := FTBoolean]
       case VFloat(_) => map[owner + [key] := FTReal]
       case VInt(_) => map[owner + [key] := FTInteger]
       case VString(_) => map[owner + [key] := FTString]
       case VRecord(_) | VVector(_) => map[])
    case ASingleConstraint(_) |
      AListConstraints(_) =>
      map[]
  }

  // Collects all declared attribute types that appear in a feature subtree.
  function AttrsTypeEnv(feature: Feature): map<Reference, FeatureType>
    decreases feature
  {
    Merge(
      seq(|feature.attributes|, i =>
        if 0 <= i < |feature.attributes| then
          AttrTypeEnv(feature.name, feature.attributes[i])
        else
          map[])) +
    Merge(
      Flatten(
        seq(|feature.groups|, i =>
          if 0 <= i < |feature.groups| then
            seq(|feature.groups[i].features|, k =>
              if 0 <= k < |feature.groups[i].features| then
                AttrsTypeEnv(feature.groups[i].features[k])
              else
                map[])
          else
            []))
    )
  }

  // Returns the type environment used when typing references in constraints,
  // combining feature references and primitive attribute references.
  function TypeEnv(model: FeatureModel): map<Reference, FeatureType>
  {
    match model.rootFeature
    case None => map[]
    case Some(root) => RootFeatureTypeEnv(model) + AttrsTypeEnv(root)
  }

}
