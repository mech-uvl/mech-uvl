// Copyright (C) 2026 Université d'Orléans
// Author: Frédéric Loulergue
// SPDX-License-Identifier: GPL-3.0-only

// This module constructs a model environment by parsing a root model and
// recursively following imports. It tracks both filesystem import paths and
// visible model paths during the traversal. It reports four build failures:
// root parse failure, imported parse failure, import cycle, and visible-path
// collision. A successful result is an model environment that is import-closed
// and acyclic.

module UVL_BuildEnvironment {
  import opened ExtLib.Option
  import opened UVL_Syntax
  import opened UVL_Environment
  import opened UVL_ModelsImports
  import opened UVL_WellFormedness
  import opened UVL_Parse

  // Build failures happen while constructing the models environment from one
  // root file and its import closure.
  datatype BuildError =
    | RootParseFailed
    | ImportedModelParseFailed(
        parent: ModelPath,
        importPath: Reference,
        child: ModelPath
      )
    | ImportCycle(path: ModelPath)
    | VisibleImportPathCollision(path: ModelPath)

  // The builder reports either one completed environment or the first
  // build failure encountered during the recursive import traversal.
  datatype BuildResult =
    | BuildSuccess(env: ModelEnv)
    | BuildFailure(error: BuildError)

  method BuildChildren(
    rootPath: string,
    currentFilePath: ModelPath,
    currentVisiblePath: ModelPath,
    imports: seq<ImportDecl>,
    active: set<ModelPath>,
    env: ModelEnv,
    ghost frontier: set<ModelPath>,
    ghost accessiblePaths: set<ModelPath>
  ) returns (result: BuildResult)
    requires currentFilePath in active
    requires currentVisiblePath in env
    requires currentVisiblePath in frontier
    requires |imports| <= |env[currentVisiblePath].imports|
    requires imports == env[currentVisiblePath].imports[|env[currentVisiblePath].imports| - |imports|..]
    requires ImportsPresentFor(
               env,
               currentVisiblePath,
               env[currentVisiblePath].imports[..|env[currentVisiblePath].imports| - |imports|]
             )
    requires ImportClosedExcept(env, frontier)
    // active is the current DFS stack on file paths.
    // accessiblePaths bounds the finite file universe used for the
    // termination argument.
    decreases accessiblePaths - active, |imports|
    ensures result.BuildSuccess? ==> forall path :: path in env ==> path in result.env && result.env[path] == env[path]
    ensures result.BuildSuccess? ==> ImportClosedExcept(result.env, frontier - {currentVisiblePath})
  {
    if |imports| == 0 {
      assert env[currentVisiblePath].imports[..|env[currentVisiblePath].imports|] == env[currentVisiblePath].imports;
      result := BuildSuccess(env);
    } else {
      // File traversal follows the declared import path, while the environment
      // key follows the visible qualifier chain.
      var allImports := env[currentVisiblePath].imports;
      var processedCount := |allImports| - |imports|;
      assert processedCount < |allImports|;
      assert imports == allImports[processedCount..];
      assert allImports[processedCount] == imports[0];
      assert imports[1..] == allImports[processedCount + 1..];
      var childFilePath := ChildPath(currentFilePath, imports[0].importPath);
      var childVisiblePath := ChildPath(currentVisiblePath, VisibleImportQualifier(imports[0]));
      if childFilePath in active {
        result := BuildFailure(ImportCycle(childFilePath));
      } else if childVisiblePath in env {
        result := BuildFailure(VisibleImportPathCollision(childVisiblePath));
      } else {
        var parsed := Parse(rootPath, childFilePath, accessiblePaths);
        match parsed
        case None =>
          result := BuildFailure(
            ImportedModelParseFailed(
              currentFilePath,
              imports[0].importPath,
              childFilePath
            )
          );
        case Some(childModel) =>
          var envWithChild := env[childVisiblePath := childModel];
          var childResult := BuildChildren(
            rootPath,
            childFilePath,
            childVisiblePath,
            childModel.imports,
            active + {childFilePath},
            envWithChild,
            frontier + {childVisiblePath},
            accessiblePaths);
          match childResult
          case BuildFailure(error) =>
            result := BuildFailure(error);
          case BuildSuccess(envAfterChild) =>
            assert envAfterChild[currentVisiblePath] == env[currentVisiblePath];
            assert ImportsPresentFor(
                envAfterChild,
                currentVisiblePath,
                allImports[..processedCount + 1]
              );
            result := BuildChildren(
              rootPath,
              currentFilePath,
              currentVisiblePath,
              imports[1..],
              active,
              envAfterChild,
              frontier,
              accessiblePaths);
      }
    }
  }

  method Build(rootPath: string, ghost accessiblePaths: set<ModelPath>) returns (result: BuildResult)
    ensures result.BuildSuccess? ==> ImportClosed(result.env)
    ensures result.BuildSuccess? ==> AcyclicImportGraph(result.env)
  {
    var parsed := Parse(rootPath, None, accessiblePaths);
    match parsed
    case None =>
      result := BuildFailure(RootParseFailed);
    case Some(root) =>
      var env := map[None := root];
      result := BuildChildren(rootPath, None, None, root.imports, {None}, env, {None}, accessiblePaths);
      if result.BuildSuccess? {
        ImportGraphIsAcyclic(result.env);
      }
  }

}
