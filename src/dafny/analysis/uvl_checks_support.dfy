// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module builds executable summaries of a model and a model environment
// for core checking, to optimize the checking wrt to executing the WF
// predicates directly.
// A summary records declared feature identifiers, declared attribute name
// maps, semantic reference types, and admissible introduced references. The
// module also provides executable reference resolution and executable use
// validation over those summaries.
// It is the execution oriented counterpart of the logical resolution and use
// layers.

module UVL_ChecksExecSupport {
  import opened ExtLib.Option
  import opened UVL_Path
  import opened UVL_Syntax
  import opened UVL_Environment
  import opened UVL_Variant
  import opened UVL_TypingEnvironment
  import opened UVL_References
  import opened UVL_ModelsResolution
  import opened UVL_ModelsUses
  import opened UVL_WellFormedness

  import opened Errors = UVL_Errors

  function MapKeys(values: map<Reference, seq<string>>): set<Reference>
  {
    set key | key in values :: key
  }

  function StringSet(values: seq<string>): set<string>
  {
    set value | value in values :: value
  }

  function FeatureIdSetOf(references: seq<Reference>): set<Reference>
  {
    set reference | reference in references :: reference
  }

  function AttributeNameSetMapOf(names: map<Reference, seq<string>>): map<Reference, set<string>>
  {
    map owner | owner in names :: StringSet(names[owner])
  }

  datatype ModelCoreExecCtx = MkModelCoreExecCtx(
    featureIdSeq: seq<Reference>,
    featureIds: set<Reference>,
    attributeNameSeqs: map<Reference, seq<string>>,
    attributeNames: map<Reference, set<string>>,
    semanticRefTypes: map<Reference, FeatureType>,
    admissibleIntroRefs: set<Reference>
  )

  type CoreExecCtxEnv = map<ModelPath, ModelCoreExecCtx>

  function ModelCoreExecCtxFromSummaries(
    featureIdSeq: seq<Reference>,
    attributeNameSeqs: map<Reference, seq<string>>,
    semanticRefTypes: map<Reference, FeatureType>,
    admissibleIntroRefs: set<Reference>
  ): ModelCoreExecCtx
  {
    MkModelCoreExecCtx(
      featureIdSeq,
      FeatureIdSetOf(featureIdSeq),
      attributeNameSeqs,
      AttributeNameSetMapOf(attributeNameSeqs),
      semanticRefTypes,
      admissibleIntroRefs
    )
  }

  function ModelCoreExecCtxOf(
    model: FeatureModel,
    variant: SemVariant
  ): ModelCoreExecCtx
  {
    match model.rootFeature
    case None =>
      ModelCoreExecCtxFromSummaries([], map[], map[], GetAdmissibleIntroRefs(model, variant))
    case Some(root) =>
      ModelCoreExecCtxFromSummaries(
        FeatureNames(root),
        FeatureAttributeNameMap(root),
        TypeEnv(model),
        GetAdmissibleIntroRefs(model, variant)
      )
  }

  function CoreExecCtxEnvOf(
    models: ModelEnv,
    variant: SemVariant
  ): CoreExecCtxEnv
  {
    map path | path in models :: ModelCoreExecCtxOf(models[path], variant)
  }

  ghost predicate ModelCoreStructureCtxOK(
    model: FeatureModel,
    ctx: ModelCoreExecCtx
  )
  {
    match model.rootFeature
    case None =>
      ctx.featureIdSeq == [] &&
      ctx.featureIds == {} &&
      ctx.attributeNameSeqs == map[] &&
      ctx.attributeNames == map[] &&
      ctx.semanticRefTypes == map[]
    case Some(root) =>
      ctx.featureIdSeq == FeatureNames(root) &&
      ctx.featureIds == FeatureIdSetOf(ctx.featureIdSeq) &&
      ctx.attributeNameSeqs == FeatureAttributeNameMap(root) &&
      ctx.attributeNames == AttributeNameSetMapOf(ctx.attributeNameSeqs) &&
      ctx.semanticRefTypes == TypeEnv(model)
  }

  ghost predicate ModelCoreExecCtxOK(
    model: FeatureModel,
    variant: SemVariant,
    ctx: ModelCoreExecCtx
  )
  {
    ModelCoreStructureCtxOK(model, ctx) &&
    ctx.admissibleIntroRefs == GetAdmissibleIntroRefs(model, variant)
  }

  ghost predicate CoreExecCtxEnvOK(
    models: ModelEnv,
    variant: SemVariant,
    ctxs: CoreExecCtxEnv
  )
  {
    (forall path :: path in models <==> path in ctxs) &&
    (forall path :: path in models ==> ModelCoreExecCtxOK(models[path], variant, ctxs[path]))
  }

  lemma ModelCoreExecCtxOfOK(
    model: FeatureModel,
    variant: SemVariant
  )
    ensures ModelCoreExecCtxOK(model, variant, ModelCoreExecCtxOf(model, variant))
  {
    match model.rootFeature
    case None =>
    case Some(root) =>
  }

  lemma CoreExecCtxEnvOfOK(
    models: ModelEnv,
    variant: SemVariant
  )
    ensures CoreExecCtxEnvOK(models, variant, CoreExecCtxEnvOf(models, variant))
  {
    var ctxs := CoreExecCtxEnvOf(models, variant);
    forall path
      ensures path in models <==> path in ctxs
    {
    }
    forall path | path in models
      ensures ModelCoreExecCtxOK(models[path], variant, ctxs[path])
    {
      assert ctxs[path] == ModelCoreExecCtxOf(models[path], variant);
      ModelCoreExecCtxOfOK(models[path], variant);
    }
  }

  method ResolveReferenceInModelExec(
    model: FeatureModel,
    ctx: ModelCoreExecCtx,
    variant: SemVariant,
    path: ModelPath,
    reference: Reference
  ) returns (resolved: option<ResolvedReference>)
    requires ModelCoreExecCtxOK(model, variant, ctx)
    ensures resolved == ResolveReferenceInModel(model, path, reference)
  {
    match model.rootFeature
    case None =>
      resolved := None;
    case Some(root) =>
      if |reference| == 1 && reference in ctx.featureIds {
        resolved := Some(ResolvedFeature(path, reference));
        assert ctx.featureIds == FeatureIdSetOf(ctx.featureIdSeq);
        assert ctx.featureIdSeq == FeatureNames(root);
        assert reference in FeatureNames(root);
      } else {
        var owner := reference[..|reference| - 1];
        if 1 < |reference| && owner in ctx.attributeNames && reference[|reference| - 1] in ctx.attributeNames[owner] {
          resolved := Some(ResolvedAttribute(path, owner, reference[|reference| - 1]));
          assert ctx.attributeNameSeqs == FeatureAttributeNameMap(root);
          assert ctx.attributeNames == AttributeNameSetMapOf(ctx.attributeNameSeqs);
          assert owner in ctx.attributeNameSeqs;
          assert ctx.attributeNames[owner] == StringSet(ctx.attributeNameSeqs[owner]);
          assert reference[|reference| - 1] in ctx.attributeNameSeqs[owner];
        } else {
          resolved := None;
          assert ctx.featureIds == FeatureIdSetOf(ctx.featureIdSeq);
          if |reference| == 1 {
            assert ctx.featureIdSeq == FeatureNames(root);
            assert reference !in FeatureNames(root);
          }
          assert ctx.attributeNameSeqs == FeatureAttributeNameMap(root);
          assert ctx.attributeNames == AttributeNameSetMapOf(ctx.attributeNameSeqs);
          if 1 < |reference| {
            if owner !in ctx.attributeNames {
              assert owner !in ctx.attributeNameSeqs;
            } else {
              assert owner in ctx.attributeNameSeqs;
              assert ctx.attributeNames[owner] == StringSet(ctx.attributeNameSeqs[owner]);
              assert reference[|reference| - 1] !in ctx.attributeNameSeqs[owner];
            }
          }
        }
      }
  }

  method ResolveImportedReferenceExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    variant: SemVariant,
    current: ModelPath,
    imports: seq<ImportDecl>,
    reference: Reference
  ) returns (resolved: option<ResolvedReference>)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures resolved == ResolveImportedReference(models, current, imports, reference)
    decreases |imports|
  {
    if |imports| == 0 {
      resolved := None;
    } else {
      var qualifier := VisibleImportQualifier(imports[0]);
      var child := ChildPath(current, qualifier);
      if child in models && |qualifier| < |reference| && HasPrefix(reference, qualifier) {
        var local := ResolveReferenceInModelExec(
          models[child],
          ctxs[child],
          variant,
          child,
          reference[|qualifier|..]
        );
        if local.Some? {
          resolved := local;
        } else {
          resolved := ResolveImportedReferenceExec(models, ctxs, variant, current, imports[1..], reference);
        }
      } else {
        resolved := ResolveImportedReferenceExec(models, ctxs, variant, current, imports[1..], reference);
      }
    }
  }

  method ResolveReferenceExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    variant: SemVariant,
    current: ModelPath,
    reference: Reference
  ) returns (resolved: option<ResolvedReference>)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures resolved == ResolveReference(models, current, reference)
  {
    var local := ResolveReferenceInModelExec(models[current], ctxs[current], variant, current, reference);
    if local.Some? {
      resolved := local;
    } else {
      resolved := ResolveImportedReferenceExec(models, ctxs, variant, current, models[current].imports, reference);
    }
  }

  method ValidReferenceOccurrenceExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    current: ModelPath,
    variant: SemVariant,
    reference: Reference
  ) returns (ok: bool)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures ok == ValidReferenceOccurrenceInModels(models, current, variant, reference)
  {
    var resolved := ResolveReferenceExec(models, ctxs, variant, current, reference);
    if resolved.Some? {
      ok := true;
    } else {
      ok := reference in ctxs[current].admissibleIntroRefs;
      assert ctxs[current].admissibleIntroRefs == GetAdmissibleIntroRefs(models[current], variant);
      // assert IsAdmissibleIntroReference(models[current], variant, reference) == (reference in GetAdmissibleIntroRefs(models[current], variant));
    }
  }

  method ImportedRootAttachmentExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    current: ModelPath,
    variant: SemVariant,
    reference: Reference
  ) returns (ok: bool)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures ok == ImportedRootAttachmentInModels(models, current, reference)
  {
    var resolved := ResolveReferenceExec(models, ctxs, variant, current, reference);
    match resolved
    case Some(ResolvedFeature(path, target)) =>
      if path != current && path in models {
        match models[path].rootFeature
        case Some(root) =>
          ok := target == root.name;
        case None =>
          ok := false;
      } else {
        ok := false;
      }
    case Some(ResolvedAttribute(_, _, _)) =>
      ok := false;
    case None =>
      ok := false;
  }

  method ValidFeatureTreeNameExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    current: ModelPath,
    variant: SemVariant,
    reference: Reference
  ) returns (ok: bool)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures ok == ValidFeatureTreeNameInModels(models, current, reference)
  {
    if |reference| == 1 {
      ok := true;
    } else {
      ok := ImportedRootAttachmentExec(models, ctxs, current, variant, reference);
    }
  }

  method ValidAggregateUseExec(
    models: ModelEnv,
    ctxs: CoreExecCtxEnv,
    current: ModelPath,
    variant: SemVariant,
    aggregate: AggregateFunction
  ) returns (ok: bool)
    requires current in models
    requires CoreExecCtxEnvOK(models, variant, ctxs)
    ensures ok == ValidAggregateUseInModels(models, current, variant, aggregate)
  {
    match aggregate
    case Sum(target, scope) =>
      var targetOk := IsBareAggregateTargetKey(target);
      if !targetOk {
        ok := false;
      } else {
        match scope
        case None =>
          ok := true;
        case Some(reference) =>
          var resolved := ResolveReferenceExec(models, ctxs, variant, current, reference);
          match resolved
          case Some(ResolvedFeature(_, _)) => ok := true;
          case _ => ok := false;
      }
    case Avg(target, scope) =>
      var targetOk := IsBareAggregateTargetKey(target);
      if !targetOk {
        ok := false;
      } else {
        match scope
        case None =>
          ok := true;
        case Some(reference) =>
          var resolved := ResolveReferenceExec(models, ctxs, variant, current, reference);
          match resolved
          case Some(ResolvedFeature(_, _)) => ok := true;
          case _ => ok := false;
      }
    case Len(target) =>
      ok := ValidReferenceOccurrenceExec(models, ctxs, current, variant, target);
    case Floor(target) =>
      ok := ValidReferenceOccurrenceExec(models, ctxs, current, variant, target);
    case Ceil(target) =>
      ok := ValidReferenceOccurrenceExec(models, ctxs, current, variant, target);
  }

}
