// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module extracts the constraint occurrences that participate in typing
// and introduced attribute inference. It represents each occurrence as either
// a global constraint or a local constraint owned by a feature. It also
// collects the introducible attribute references contributed by those sites
// under a semantic variant.
// The extracted sites are the input consumed by the typing-inference layer.

module UVL_ConstraintSites {
  import opened Std.Collections.Seq
  import opened ExtLib.Option
  import opened ExtLib.SeqMap
  import opened UVL_Syntax
  import opened UVL_Variant
  import opened UVL_References
  import opened UVL_TypingEnvironment


  // Constraint sites distinguish top-level constraints from feature-local
  // attribute constraints.
  datatype UVLConstraintSite =
    | GlobalConstraintSite(constraint: Constraint)
    | LocalConstraintSite(owner: Reference, constraint: Constraint)

  function ConstraintOf(site: UVLConstraintSite): Constraint
  {
    match site
    case GlobalConstraintSite(constraint) => constraint
    case LocalConstraintSite(_, constraint) => constraint
  }

  function GlobalUVLConstraints(constraints: seq<Constraint>): seq<UVLConstraintSite>
  {
    FMap((c)=>GlobalConstraintSite(c), constraints)
  }

  function LocalUVLConstraints(owner: Reference, constraints: seq<Constraint>): seq<UVLConstraintSite>
  {
    FMap((c)=>LocalConstraintSite(owner,c), constraints)
  }

  function UVLConstraintsInFeature(feature: Feature): seq<UVLConstraintSite>
    decreases feature
  {
    Seq.Flatten(
      seq(|feature.attributes|, i =>
        if 0 <= i < |feature.attributes| then
          match feature.attributes[i]
          case AValue(_) => []
          case ASingleConstraint(constraint) => [LocalConstraintSite(feature.name, constraint)]
          case AListConstraints(constraints) => LocalUVLConstraints(feature.name, constraints)
        else
          []))
    +
    Seq.Flatten(
      seq(|feature.groups|, i =>
        if 0 <= i < |feature.groups| then
          Seq.Flatten(
            seq(|feature.groups[i].features|, k =>
              if 0 <= k < |feature.groups[i].features| then
                UVLConstraintsInFeature(feature.groups[i].features[k])
              else
                []))
        else
          []))
  }

  // Extracts the UVL constraints of one model that may contribute typing
  // information.
  function ExtractUVLConstraints(model: FeatureModel): seq<UVLConstraintSite>
  {
    GlobalUVLConstraints(model.constraints) +
    match model.rootFeature
    case None => []
    case Some(root) => UVLConstraintsInFeature(root)
  }

  // Returns the introducible attribute references contributed by one UVL
  // constraint site under the chosen semantic variant.
  function IntroducibleRefsInUVLConstraint(
    site: UVLConstraintSite,
    model: FeatureModel,
    variant: SemVariant
  ): set<Reference>
  {
    match variant.attrIntro
    case DeclaredOnly =>
      {}
    case LocalIntro(localScopeOnly) =>
      (match site
       case GlobalConstraintSite(_) =>
         {}
       case LocalConstraintSite(owner, constraint) =>
         set reference |
           reference in IntroducibleAttrRefsInConstraint(constraint, model) &&
           (!localScopeOnly || ReferenceLocalTo(owner, reference)) ::
           reference)
    case GlobalIntro =>
      set reference | reference in IntroducibleAttrRefsInConstraint(ConstraintOf(site), model) :: reference
  }

  // Collects all introducible references mentioned by the extracted UVL
  // constraints.
  function ExtractIntroducibleRefs(
    uvlConstraints: seq<UVLConstraintSite>,
    model: FeatureModel,
    variant: SemVariant
  ): set<Reference>
    decreases |uvlConstraints|
  {
    if |uvlConstraints| == 0 then
      {}
    else
      IntroducibleRefsInUVLConstraint(uvlConstraints[0], model, variant) +
      ExtractIntroducibleRefs(uvlConstraints[1..], model, variant)
  }

}
