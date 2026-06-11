// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module defines the error datatypes returned by the executable checking
// passes. It separates local well-formedness errors, use errors, level errors,
// and typing errors. Each datatype is defined so callers can report the
// model path of the failure  together with the local cause. The rest of the
// frontend and analysis code uses these types.

module UVL_Errors {
  import opened UVL_Syntax
  import opened UVL_Environment

  // These errors concern the well formedness of one model only. They are
  // separate from reference and level errors that depend on the model
  // environment.
  datatype LocalWFError =
    | DuplicateFeatureIdentifier(reference: Reference)
    | DuplicateAttributeName(owner: Reference, key: string)
    | DuplicateImportAlias(qualifier: Reference)
    | NonPrefixFreeImportQualifiers(left: Reference, right: Reference)

  datatype CoreCheckError =
    | LocalModelWFError(
        current: ModelPath,
        error: LocalWFError
      )
    | InvalidFeatureTreeUse(
        current: ModelPath,
        reference: Reference
      )
    | InvalidReferenceUse(
        current: ModelPath,
        reference: Reference
      )
    | InvalidAggregateUse(
        current: ModelPath,
        aggregate: AggregateFunction
      )

  datatype LevelCheckError =
    | InvalidLevelDeclaration(
        current: ModelPath,
        level: LanguageLevel
      )
    | InsufficientMajorLevel(
        current: ModelPath,
        required: MajorLevel,
        declared: MajorLevel
      )
    | MissingMinorLevels(
        current: ModelPath,
        missing: set<MinorLevel>
      )

  datatype TypingError =
    | IllTypedModel(current: ModelPath)
    | IntroTypeInferenceContradiction(
        current: ModelPath,
        domains: map<Reference, set<FeatureType>>
      )
    | IntroTypeInferenceUnderconstrained(
        current: ModelPath,
        domains: map<Reference, set<FeatureType>>
      )
}
