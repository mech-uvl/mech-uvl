// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module executes the structural well-formedness checks that concern one
// model. It detects duplicate feature identifiers, duplicate declared
// attribute keys, duplicate import aliases, and prefix conflicts between
// visible import qualifiers.
// A `None` result establishes the corresponding local well-formedness
// predicates.

module UVL_LocalChecks {
  import opened ExtLib.Option
  import opened ExtLib.SeqNoDup
  import opened UVL_Path
  import opened UVL_Syntax
  import opened UVL_WellFormedness
  import opened UVL_Errors
  import opened UVL_ChecksExecSupport

  // Returns the first reference in `references` that is already present in
  // `seen` or that repeats an earlier reference in `references`.
  method FirstDuplicateReference(
    references: seq<Reference>,
    seen: set<Reference>
  ) returns (duplicate: option<Reference>)
    ensures duplicate.None? ==> HasNoDup(references)
    ensures duplicate.None? ==> forall reference :: reference in references ==> reference !in seen
    decreases |references|
  {
    if |references| == 0 {
      duplicate := None;
    } else if references[0] in seen {
      duplicate := Some(references[0]);
    } else {
      duplicate := FirstDuplicateReference(references[1..], seen + {references[0]});
    }
  }

  // Returns the first duplicated declared attribute key in `values` relative
  // to an initial set of already seen keys.
  method FirstDuplicateString(
    values: seq<string>,
    seen: set<string>
  ) returns (duplicate: option<string>)
    ensures duplicate.None? ==> HasNoDup(values)
    ensures duplicate.None? ==> forall value :: value in values ==> value !in seen
    decreases |values|
  {
    if |values| == 0 {
      duplicate := None;
    } else if values[0] in seen {
      duplicate := Some(values[0]);
    } else {
      duplicate := FirstDuplicateString(values[1..], seen + {values[0]});
    }
  }

  // Returns the first duplicated explicit import alias while ignoring imports
  // that do not declare any alias.
  method FirstDuplicateImportAlias(
    imports: seq<ImportDecl>,
    seen: set<Reference>
  ) returns (error: option<LocalWFError>)
    ensures error.None? ==> HasNoDup(ImportAliases(imports))
    ensures error.None? ==> forall alias :: alias in ImportAliases(imports) ==> alias !in seen
    decreases |imports|
  {
    if |imports| == 0 {
      error := None;
    } else {
      match imports[0].alias
      case None =>
        error := FirstDuplicateImportAlias(imports[1..], seen);
      case Some(alias) =>
        if alias in seen {
          error := Some(DuplicateImportAlias(alias));
        } else {
          error := FirstDuplicateImportAlias(imports[1..], seen + {alias});
        }
    }
  }

  // Returns the first visible import qualifier from `imports` that has a
  // prefix conflict with an earlier qualifier or with one from `checked`.
  method FirstNonPrefixFreeImportQualifiers(
    imports: seq<ImportDecl>,
    checked: seq<Reference>
  ) returns (error: option<LocalWFError>)
    ensures error.None? ==> forall i, j | 0 <= i < j < |imports| ::
                !HasPrefix(VisibleImportQualifier(imports[i]), VisibleImportQualifier(imports[j])) &&
                !HasPrefix(VisibleImportQualifier(imports[j]), VisibleImportQualifier(imports[i]))
    ensures error.None? ==> forall i, j | 0 <= i < |imports| && 0 <= j < |checked| ::
                !HasPrefix(VisibleImportQualifier(imports[i]), checked[j]) &&
                !HasPrefix(checked[j], VisibleImportQualifier(imports[i]))
    decreases |imports|
  {
    if |imports| == 0 {
      error := None;
    } else {
      var qualifier := VisibleImportQualifier(imports[0]);
      var k := 0;
      while k < |checked|
        invariant 0 <= k <= |checked|
        invariant forall j :: 0 <= j < k ==> !HasPrefix(qualifier, checked[j]) &&
                                             !HasPrefix(checked[j], qualifier)
        decreases |checked| - k
      {
        if HasPrefix(qualifier, checked[k]) || HasPrefix(checked[k], qualifier) {
          error := Some(NonPrefixFreeImportQualifiers(qualifier, checked[k]));
          return;
        }
        k := k + 1;
      }
      error := FirstNonPrefixFreeImportQualifiers(imports[1..], checked + [qualifier]);
      if error.None? {
        forall i, j | 0 <= i < j < |imports|
          ensures !HasPrefix(VisibleImportQualifier(imports[i]), VisibleImportQualifier(imports[j])) &&
                  !HasPrefix(VisibleImportQualifier(imports[j]), VisibleImportQualifier(imports[i]))
        {
          if i == 0 {
            assert 0 <= j - 1 < |imports[1..]|;
            assert 0 <= |checked| < |checked + [qualifier]|;
            assert imports[1..][j - 1] == imports[j];
            assert (checked + [qualifier])[|checked|] == qualifier;
            assert !HasPrefix(VisibleImportQualifier(imports[1..][j - 1]), (checked + [qualifier])[|checked|]);
            assert !HasPrefix((checked + [qualifier])[|checked|], VisibleImportQualifier(imports[1..][j - 1]));
          }
        }
        forall i, j | 0 <= i < |imports| && 0 <= j < |checked|
          ensures !HasPrefix(VisibleImportQualifier(imports[i]), checked[j]) &&
                  !HasPrefix(checked[j], VisibleImportQualifier(imports[i]))
        {
          if i == 0 {
            assert !HasPrefix(qualifier, checked[j]);
            assert !HasPrefix(checked[j], qualifier);
          } else {
            assert imports[1..][i - 1] == imports[i];
            assert (checked + [qualifier])[j] == checked[j];
            assert !HasPrefix(VisibleImportQualifier(imports[1..][i - 1]), (checked + [qualifier])[j]);
            assert !HasPrefix((checked + [qualifier])[j], VisibleImportQualifier(imports[1..][i - 1]));
          }
        }
      }
    }
  }

  // Checks the owners in `remaining` and returns the first owner/key pair that
  // repeats a declared attribute name.
  method FirstDuplicateAttributeNameForOwnerSet(
    names: map<Reference, seq<string>>,
    remaining: set<Reference>
  ) returns (error: option<LocalWFError>)
    requires remaining <= MapKeys(names)
    ensures error.None? ==> forall owner :: owner in remaining ==> HasNoDup(names[owner])
    decreases |remaining|
  {
    if remaining == {} {
      error := None;
    } else {
      var owner :| owner in remaining;
      var duplicate := FirstDuplicateString(names[owner], {});
      if duplicate.Some? {
        error := Some(DuplicateAttributeName(owner, duplicate.value));
      } else {
        error := FirstDuplicateAttributeNameForOwnerSet(names, remaining - {owner});
        if error.None? {
          forall key | key in remaining
            ensures HasNoDup(names[key])
          {
            if key == owner {
            } else {
              assert key in remaining - {owner};
            }
          }
        }
      }
    }
  }

  // Runs the local well-formedness checks for one model using a precomputed
  // structural context and returns the first detected error.
  method FirstLocalWFErrorInCtx(
    model: FeatureModel,
    ctx: ModelCoreExecCtx
  ) returns (error: option<LocalWFError>)
    requires ModelCoreStructureCtxOK(model, ctx)
    ensures error.None? ==> UniqueIdentifiers(model)
    ensures error.None? ==> UniqueAttributeNames(model)
    ensures error.None? ==> UniqueImportAliases(model)
    ensures error.None? ==> PrefixFreeImportQualifiers(model)
  {
    match model.rootFeature
    case None =>
      var aliasError := FirstDuplicateImportAlias(model.imports, {});
      if aliasError.Some? {
        error := aliasError;
      } else {
        error := FirstNonPrefixFreeImportQualifiers(model.imports, []);
      }
    case Some(root) =>
      var duplicateId := FirstDuplicateReference(ctx.featureIdSeq, {});
      if duplicateId.Some? {
        error := Some(DuplicateFeatureIdentifier(duplicateId.value));
      } else {
        assert UniqueIdentifiers(model);
        var attributeError := FirstDuplicateAttributeNameForOwnerSet(
          ctx.attributeNameSeqs,
          MapKeys(ctx.attributeNameSeqs)
        );
        if attributeError.Some? {
          error := attributeError;
        } else {
          assert UniqueAttributeNames(model);
          var aliasError := FirstDuplicateImportAlias(model.imports, {});
          if aliasError.Some? {
            error := aliasError;
          } else {
            error := FirstNonPrefixFreeImportQualifiers(model.imports, []);
            if error.None? {
              assert UniqueImportAliases(model);
              assert PrefixFreeImportQualifiers(model);
            }
          }
        }
      }
  }

}
