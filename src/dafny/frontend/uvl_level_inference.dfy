// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module computes explicit `includes` declarations from already established required levels.
// It updates either only the root model or every model in a model environment.
// The computation reuses the required-level analysis defined in `UVL_ModelsLevels`.
// It does not validate models; its precondition requires core well-formedness already established.
module UVL_LevelInference {
  import opened Syntax = UVL_Syntax
  import opened Environment = UVL_Environment
  import opened Levels = UVL_Levels
  import opened UVL_ModelsWF
  import opened ModelsLevels = UVL_ModelsLevels
  import opened TypingChecks = UVL_ModelsTypingChecks
  import opened Variant = UVL_Variant

  datatype LevelInferenceScope =
    | Root
    | All

  function UpdateIncludes(
    model: FeatureModel,
    includes: seq<LanguageLevel>
  ): FeatureModel
  {
    MkFeatureModel(
      model.namespace,
      includes,
      model.imports,
      model.rootFeature,
      model.constraints
    )
  }

  function InInferenceScope(
    scope: LevelInferenceScope,
    current: ModelPath
  ): bool
  {
    scope.All? || current.None?
  }

  method InferLevelsForModels(
    models: ModelEnv,
    variant: SemVariant,
    scope: LevelInferenceScope
  ) returns (updated: ModelEnv)
    requires CoreWF_Models(models, variant)
    ensures forall current :: current in models ==> current in updated
    ensures forall current :: current in models && InInferenceScope(scope, current) ==>
                                updated[current].includes == ExplicitLevelsOf(RequiredLevelsInModels(models, current))
    ensures forall current :: current in models && !InInferenceScope(scope, current) ==>
                                updated[current] == models[current]
  {
    updated := map current | current in models ::
      if InInferenceScope(scope, current) then
        UpdateIncludes(
          models[current],
          ExplicitLevelsOf(RequiredLevelsInModels(models, current))
        )
      else
        models[current];
  }
}
