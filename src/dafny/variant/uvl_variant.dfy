// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

module UVL_Variant {

  datatype AttrIntro =
    | DeclaredOnly
    | LocalIntro(localScopeOnly: bool)
    | GlobalIntro

  datatype SemVariant = SemVariant(
    attrIntro: AttrIntro,
    typedFeatureAsBool: bool,
    undefConstraintAsFalse: bool,
    shortCircuit: bool
  )

  predicate WF_SemVariant(variant: SemVariant)
  {
    (variant.undefConstraintAsFalse && variant.shortCircuit) ==> variant.typedFeatureAsBool
  }
}
