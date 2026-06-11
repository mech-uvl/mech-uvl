// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

module UVL_Environment {
  import opened UVL_Syntax
  import opened ExtLib.Option

  // None denotes the root model. Some(path) denotes a model reached by
  // following a visible import path from the root model.
  type ModelPath = option<Reference>

  // Model environment keyed by path, alias or None for the root model.
  type ModelEnv =
    env: map<ModelPath, FeatureModel> |
      None in env
    witness map[None := MkFeatureModel(None, [], [], None, [])]

  // Extends a root-relative model path with one additional import path.
  function ChildPath(current: ModelPath, child: Reference): ModelPath
  {
    match current
    case None => Some(child)
    case Some(path) =>
      var combined: Reference := path + child;
      Some(combined)
  }
}
