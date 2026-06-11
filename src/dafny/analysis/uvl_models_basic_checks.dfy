// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module provides executable entry points for level checking and for core
// well-formedness checks over a model environment. It checks declared levels
// against the required levels computed from models, imports, and typing
// information.
// Each entry point returns the first detected error rather than accumulating
// all failures.

module UVL_ModelsBasicChecks {
  import opened ExtLib.Option
  import opened UVL_Syntax
  import opened UVL_Environment
  import opened UVL_Variant
  import opened UVL_Levels
  import opened UVL_ModelsLevels
  import opened UVL_ModelsImports
  import opened UVL_ModelsWF
  import opened UVL_Errors
  import opened UVL_ChecksExecSupport
  import opened UVL_LocalChecks
  import opened UVL_UseChecks

  method FirstLevelDeclarationError(
    current: ModelPath,
    levels: seq<LanguageLevel>
  ) returns (error: option<LevelCheckError>)
    ensures error.None? ==> ValidLevels(levels)
    decreases |levels|
  {
    if |levels| == 0 {
      error := None;
    } else if ValidLevel(levels[0]) {
      error := FirstLevelDeclarationError(current, levels[1..]);
    } else {
      error := Some(InvalidLevelDeclaration(current, levels[0]));
    }
  }

  method FirstLevelErrorInModels(
    models: ModelEnv,
    current: ModelPath
  ) returns (error: option<LevelCheckError>)
    requires current in models
    ensures error.None? ==> LevelsOKInModels(models, current)
  {
    var declarationError := FirstLevelDeclarationError(current, models[current].includes);
    if declarationError.Some? {
      error := declarationError;
    } else {
      var requiredMajor := RequiredMajorInModels(models, current);
      var declaredMajor := DeclaredMajor(models[current].includes);
      if !Levels.Le(requiredMajor, declaredMajor) {
        error := Some(InsufficientMajorLevel(current, requiredMajor, declaredMajor));
      } else {
        var missing := RequiredMinorsInModels(models, current) - DeclaredMinors(models[current].includes);
        if missing != {} {
          error := Some(MissingMinorLevels(current, missing));
        } else {
          error := None;
        }
      }
    }
  }

  method FirstLevelCheckError(
    models: ModelEnv
  ) returns (error: option<LevelCheckError>)
    ensures error.None? ==> LevelsOKForModels(models)
  {
    var unchecked := set path | path in models :: path;
    error := FirstLevelCheckErrorInSet(models, unchecked);
  }

  method FirstLevelCheckErrorInSet(
    models: ModelEnv,
    unchecked: set<ModelPath>
  ) returns (error: option<LevelCheckError>)
    requires unchecked <= set path | path in models :: path
    requires forall path :: path in models && path !in unchecked ==> LevelsOKInModels(models, path)
    ensures error.None? ==> forall path :: path in unchecked ==> LevelsOKInModels(models, path)
    decreases |unchecked|
  {
    if unchecked == {} {
      error := None;
    } else {
      var current :| current in unchecked;
      var currentError := FirstLevelErrorInModels(models, current);
      if currentError.Some? {
        error := currentError;
      } else {
        forall path | path in models && path !in (unchecked - {current})
          ensures LevelsOKInModels(models, path)
        {
          if path in unchecked {
            assert path == current;
          }
        }
        error := FirstLevelCheckErrorInSet(models, unchecked - {current});
      }
    }
  }

  // This checker assumes the models environment has already been built. Import
  // closure and cycle rejection are therefore expected to be handled by Build.
  method FirstCoreCheckErrorInModelExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    current: ModelPath,
    variant: SemVariant
  ) returns (error: option<CoreCheckError>)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures error.None? ==> CoreWF_ModelInModels(models, current, variant)
  {
    var localError := FirstLocalWFErrorInCtx(models[current], ctxs[current]);
    if localError.Some? {
      error := Some(LocalModelWFError(current, localError.value));
    } else {
      error := FirstInvalidModelUseInModelsExec(models, ctxs, current, variant);
    }
  }

  method FirstCoreCheckError(
    models: ModelEnv,
    variant: SemVariant
  ) returns (error: option<CoreCheckError>)
    requires ImportClosed(models)
    requires AcyclicImportGraph(models)
    requires Variant.WF_SemVariant(variant)
    ensures error.None? ==> CoreWF_Models(models, variant)
  {
    var unchecked := set path | path in models :: path;
    var ctxs := CoreExecCtxEnvOf(models, variant);
    CoreExecCtxEnvOfOK(models, variant);
    assert CoreExecCtxEnvOK(models, variant, ctxs);
    error := FirstCoreCheckErrorInSetExec(models, ctxs, variant, unchecked);
  }

  method FirstCoreCheckErrorInSetExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    variant: SemVariant,
    unchecked: set<ModelPath>
  ) returns (error: option<CoreCheckError>)
    requires Variant.WF_SemVariant(variant)
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    requires unchecked <= set path | path in models :: path
    requires forall path :: path in models && path !in unchecked ==> CoreWF_ModelInModels(models, path, variant)
    ensures error.None? ==> forall path :: path in unchecked ==> CoreWF_ModelInModels(models, path, variant)
    decreases |unchecked|
  {
    if unchecked == {} {
      error := None;
    } else {
      var current :| current in unchecked;
      var currentError := FirstCoreCheckErrorInModelExec(models, ctxs, current, variant);
      if currentError.Some? {
        error := currentError;
      } else {
        forall path | path in models && path !in (unchecked - {current})
          ensures CoreWF_ModelInModels(models, path, variant)
        {
          if path in unchecked {
            assert path == current;
          }
        }
        error := FirstCoreCheckErrorInSetExec(models, ctxs, variant, unchecked - {current});
      }
    }
  }
}
