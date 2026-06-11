// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module defines logical properties of import graphs over model
// environments. It formalises import edges, import walks, import closure, and
// acyclicity. Its lemmas show that visible-path depth strictly increases
// along import edges and walks. The frontend builder relies on these facts to
// justify its cycle checks.

module UVL_ModelsImports {
  import opened ExtLib.Option
  import opened UVL_Syntax
  import opened UVL_Environment
  import opened UVL_WellFormedness

  // Visible import paths strictly grow when we follow an import edge, so their
  // length provides a simple ranking for the acyclicity proof.
  function ModelPathDepth(path: ModelPath): nat
  {
    match path
    case None => 0
    case Some(reference) => |reference|
  }

  // The import graph is defined over visible model paths, not over file paths.
  predicate DirectImportEdge(env: ModelEnv, current: ModelPath, next: ModelPath)
  {
    current in env &&
    next in env &&
    exists i :: 0 <= i < |env[current].imports| &&
                next == ChildPath(current, VisibleImportQualifier(env[current].imports[i]))
  }

  // A walk follows only direct visible-import edges already present in env.
  predicate ImportWalk(env: ModelEnv, walk: seq<ModelPath>)
  {
    0 < |walk| &&
    forall i :: 0 <= i < |walk| - 1 ==> DirectImportEdge(env, walk[i], walk[i + 1])
  }

  // A cycle would contradict the strict growth of visible import paths.
  ghost predicate AcyclicImportGraph(env: ModelEnv)
  {
    forall walk :: 1 < |walk| && ImportWalk(env, walk) ==> walk[0] != walk[|walk| - 1]
  }

  // All visible children induced by one import sequence are present in the
  // environment.
  predicate ImportsPresentFor(env: ModelEnv, current: ModelPath, imports: seq<ImportDecl>)
  {
    current in env &&
    forall i :: 0 <= i < |imports| ==>
                  ChildPath(current, VisibleImportQualifier(imports[i])) in env
  }

  // All models except those on the current DFS frontier already have their
  // visible imports present in the environment.
  predicate ImportClosedExcept(env: ModelEnv, frontier: set<ModelPath>)
  {
    forall current :: current in env && current !in frontier ==>
                        ImportsPresentFor(env, current, env[current].imports)
  }

  predicate ImportClosed(env: ModelEnv)
  {
    ImportClosedExcept(env, {})
  }

  lemma ChildPathIncreasesDepth(current: ModelPath, child: Reference)
    ensures ModelPathDepth(current) < ModelPathDepth(ChildPath(current, child))
  {
  }

  lemma DirectImportEdgeIncreasesDepth(env: ModelEnv, current: ModelPath, next: ModelPath)
    requires DirectImportEdge(env, current, next)
    ensures ModelPathDepth(current) < ModelPathDepth(next)
  {
    var i :| 0 <= i < |env[current].imports| &&
             next == ChildPath(current, VisibleImportQualifier(env[current].imports[i]));
    ChildPathIncreasesDepth(current, VisibleImportQualifier(env[current].imports[i]));
  }

  lemma ImportWalkIncreasesDepth(env: ModelEnv, walk: seq<ModelPath>, i: nat, j: nat)
    requires ImportWalk(env, walk)
    requires i < j < |walk|
    ensures ModelPathDepth(walk[i]) < ModelPathDepth(walk[j])
    decreases j - i
  {
    if i + 1 == j {
      DirectImportEdgeIncreasesDepth(env, walk[i], walk[j]);
    } else {
      ImportWalkIncreasesDepth(env, walk, i, j - 1);
      DirectImportEdgeIncreasesDepth(env, walk[j - 1], walk[j]);
    }
  }

  lemma ImportGraphIsAcyclic(env: ModelEnv)
    ensures AcyclicImportGraph(env)
  {
    forall walk | 1 < |walk| && ImportWalk(env, walk)
      ensures walk[0] != walk[|walk| - 1]
    {
      ImportWalkIncreasesDepth(env, walk, 0, |walk| - 1);
    }
  }
}
