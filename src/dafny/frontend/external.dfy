// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module declares the trusted parser entry point for UVL source files.

module UVL_Parse {
  import opened ExtLib.Option
  import opened UVL_Syntax

  // Parses one UVL file in the import space rooted at rootPath. The second
  // argument is the root-relative UVL path of the model to parse, where None
  // denotes the root model itself. The ghost set makes explicit the fact that
  // there is only a finite set of files that can be possibly imported from the
  // root, because the number of files in a filesystem is finite.
  method {:extern "UvlExternal", "Parse"} {:axiom} Parse(
    rootPath: string,
    path: option<Reference>,
    ghost accessiblePaths: set<option<Reference>>
  ) returns (model: option<FeatureModel>)
    ensures path !in accessiblePaths ==> model.None?
    ensures model.Some? ==> path in accessiblePaths
}
