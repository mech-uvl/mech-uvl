// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

module UVL_Path {

  type Path<T> = p: seq<T> | 0 < |p| witness *

  function HasPrefix<T(==)>(path: Path<T>, prefix: Path<T>): bool
  {
    |prefix| <= |path| && path[..|prefix|] == prefix
  }

  type Id = string

  type Ref = Path<Id>
}
