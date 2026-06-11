// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module resolves feature and attribute references in a model
// environment. Resolution means here that these functions establish whether
// the reference is a valid reference in the model environment and what kind
// of element (feature or attribute) it refers to. Resolution first searches
// the current model and then follows imported models visible from the current
// path. A successful result records the target model path and whether the
// target is a feature or an attribute.

module UVL_ModelsResolution {
  import opened ExtLib.Option
  import opened UVL_Path
  import opened UVL_Syntax
  import opened UVL_Environment
  import opened UVL_WellFormedness

  datatype ResolvedReference =
    | ResolvedFeature(path: ModelPath, reference: Reference)
    | ResolvedAttribute(path: ModelPath, owner: Reference, key: string)

  function ResolveReferenceInModel(
    model: FeatureModel,
    path: ModelPath,
    reference: Reference
  ): option<ResolvedReference>
  {
    match model.rootFeature
    case None => None
    case Some(root) =>
      if |reference| == 1 && reference in FeatureNames(root) then
        Some(ResolvedFeature(path, reference))
      else
        var names := FeatureAttributeNameMap(root);
        var owner := reference[..|reference| - 1];
        if 1 < |reference| && owner in names && reference[|reference| - 1] in names[owner] then
          Some(ResolvedAttribute(path, owner, reference[|reference| - 1]))
        else
          None
  }

  function ResolveImportedReference(
    env: ModelEnv,
    current: ModelPath,
    imports: seq<ImportDecl>,
    reference: Reference
  ): option<ResolvedReference>
    decreases |imports|
  {
    if |imports| == 0 then
      None
    else
      // Imported references are matched against the visible qualifier of each
      // import, not against the imported file path.
      var qualifier := VisibleImportQualifier(imports[0]);
      var child := ChildPath(current, qualifier);
      if child in env && |qualifier| < |reference| && HasPrefix(reference, qualifier) then
        match ResolveReferenceInModel(
            env[child],
            child,
            reference[|qualifier|..]
          )
        case Some(resolved) => Some(resolved)
        case None => ResolveImportedReference(env, current, imports[1..], reference)
      else
        ResolveImportedReference(env, current, imports[1..], reference)
  }

  function ResolveReference(env: ModelEnv, current: ModelPath, reference: Reference): option<ResolvedReference>
    requires current in env
  {
    match ResolveReferenceInModel(env[current], current, reference)
    case Some(resolved) => Some(resolved)
    case None => ResolveImportedReference(env, current, env[current].imports, reference)
  }

}
