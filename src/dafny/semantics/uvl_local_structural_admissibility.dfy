// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module defines local structural admissibility for one model in a
// composed environment. It checks the declared feature tree of the current
// model and treats imported-root attachments as local anchors: selected
// descendants below such anchors are admitted here, but the imported model
// itself is checked by the recursive extensional layer.

module UVL_LocalStructuralAdmissibility {
  import opened ExtLib.Option
  import opened UVL_Syntax
  import opened UVL_Environment
  import opened UVL_Variant
  import opened UVL_Configuration
  import opened UVL_ModelsResolution
  import opened UVL_StructuralSemantics

  datatype ImportedRoot =
    | ImportedRoot(path: ModelPath, root: Feature)

  // Resolves a feature-tree reference that denotes the root feature of an
  // imported model. Such references act as imported-root attachments in the
  // current model.
  function ImportedRootAttachmentOf(
    models: ModelEnv,
    current: ModelPath,
    reference: Reference
  ): option<ImportedRoot>
    requires current in models
  {
    match ResolveReference(models, current, reference)
    case Some(ResolvedFeature(path, target)) =>
      if path != current && path in models then
        match models[path].rootFeature
        case Some(root) =>
          if target == root.name then Some(ImportedRoot(path, root)) else None
        case None => None
      else
        None
    case Some(ResolvedAttribute(_, _, _)) => None
    case None => None
  }

  // Checks whether `target` is locally admitted below `featureOccurrence`.
  // The occurrence may follow declarations in the current feature subtree, or
  // may lie below an imported-root attachment. This predicate does not validate
  // the imported subtree itself.
  predicate OccurrenceLocallyAdmittedByFeature(
    models: ModelEnv,
    current: ModelPath,
    feature: Feature,
    cfg: Configuration,
    featureOccurrence: OccRef,
    target: OccRef
  )
    requires current in models
    decreases feature
  {
    target == featureOccurrence ||
    (exists i, j, childOccurrence ::
       0 <= i < |feature.groups| &&
       0 <= j < |feature.groups[i].features| &&
       childOccurrence in SelectedExtensionsBy(
                            cfg,
                            featureOccurrence,
                            feature.groups[i].features[j].name) &&
       OccurrenceLocallyAdmittedByFeature(
         models,
         current,
         feature.groups[i].features[j],
         cfg,
         childOccurrence,
         target)) ||
    (match ImportedRootAttachmentOf(models, current, feature.name)
     case None => false
     case Some(_) => DescendantOf(target, featureOccurrence))
  }

  // Checks the local structural part of a configuration for the current model:
  // configuration data consistency, root structure, local feature/group
  // cardinalities, and local admissibility of every selected occurrence.
  // Imported subtrees are admitted at their attachment points and verified
  // separately by recursive imported-model satisfaction.
  predicate LocalModelStructureOK(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant,
    cfg: Configuration
  )
    requires current in models
    requires SemanticEnv(models, variant)
  {
    WF_Configuration(cfg) &&
    match models[current].rootFeature
    case None => cfg.selected == {}
    case Some(root) =>
      RootFeatureStructureOK(root, cfg) &&
      (forall occurrence :: occurrence in cfg.selected ==>
                              exists rootOccurrence ::
                                rootOccurrence in SelectedOccurrencesOf(cfg, root.name) &&
                                OccurrenceLocallyAdmittedByFeature(
                                  models,
                                  current,
                                  root,
                                  cfg,
                                  rootOccurrence,
                                  occurrence))
  }
}
