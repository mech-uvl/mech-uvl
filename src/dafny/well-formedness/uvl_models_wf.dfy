// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

module UVL_ModelsWF {
  import opened UVL_Environment
  import opened UVL_Variant
  import opened UVL_WellFormedness
  import opened UVL_ModelsImports
  import opened UVL_ModelsUses
  import opened UVL_ModelsLevels

  predicate CoreWF_ModelInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant
  ) requires current in models
  {
    RootFeaturePresent(models[current]) &&
    ValidCardinalitiesInModel(models[current]) &&
    ValidRecordAttributesInModel(models[current]) &&
    UniqueIdentifiers(models[current]) &&
    UniqueAttributeNames(models[current]) &&
    UniqueImportAliases(models[current]) &&
    PrefixFreeImportQualifiers(models[current]) &&
    ValidModelUsesInModels(models, current, variant)
  }

  predicate WF_ModelInModels(
    models: ModelEnv,
    current: ModelPath,
    variant: SemVariant
  ) requires current in models
  {
    CoreWF_ModelInModels(models, current, variant) &&
    LevelsOKInModels(models, current)
  }

  ghost predicate CoreWF_Models(models: ModelEnv, variant: SemVariant)
  {
    WF_SemVariant(variant) &&
    ImportClosed(models) &&
    AcyclicImportGraph(models) &&
    forall current :: current in models ==> CoreWF_ModelInModels(models, current, variant)
  }

  ghost predicate WF_Models(models: ModelEnv, variant: SemVariant)
  {
    CoreWF_Models(models, variant) &&
    LevelsOKForModels(models)
  }

}
