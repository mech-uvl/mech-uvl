<img src="assets/logo.svg" alt="mech-uvl logo" width="50%">

# mech-uvl 

`mech-uvl` is a Dafny-centered formalization and tooling project for the Universal Variability Language (UVL). The repository is organized around one verified core written in Dafny and one executable .NET tool that preprocesses, parses, and pretty-prints UVL files against the official ANTLR grammar. The well-formedness checks and type checking are done by the Dafny code but called from the CLI written in C#.

Current development version: `0.1.0-dev`.
Versioning policy: [`VERSIONING.md`](VERSIONING.md).

## Repository Layout

- `src/dafny/`: UVL formalization in Dafny, including checking and inference methods
- `src/tool/`: the single executable .NET tool. It hosts the preprocessing stage, the ANTLR-based parser frontend, CLI commands, and user-facing diagnostics.
- `grammar/`: the official UVL grammar, tracked as a git submodule. The base ANTLR files currently live under `grammar/uvl/UVLLexer.g4` and `grammar/uvl/UVLParser.g4`.
- `examples/`: tiny project example inputs, organised by CLI command. See `examples/README.md`.
- `MechUvl.sln`: the .NET solution entry point.
- `dfyconfig.toml`: Dafny project configuration for the verified core.

## Current Status

The Dafny core is present under `src/dafny/`. 

The .NET tool currently supports:

- `preprocess`: normalize indentation and strip comments as preparation for parsing
- `parse`: preprocess, parse, and dump the extracted Dafny AST for one or more UVL files
- `fmt`: preprocess, parse, and pretty-print one or more UVL files in a canonical UVL form, with configurable indentation
- `check`: build the Dafny model environment and run core, level, and typing checks
- `levels infer`: build the Dafny model environment, infer levels, and print the inferred `include` declarations

## Requirements

- Dafny 4 (tested with Dafny 4.11.0)
- .NET 8 SDK
- Java 17 or later
- Git with submodule support

## Getting Started with the Tool

Clone the repository and initialize the grammar submodule:

```sh
git submodule update --init --recursive
```

Build the .NET tool:

```sh
dotnet build
```

You can either add the `mech-uvl` executable to your `PATH`, or run the tool through `dotnet run`.

```sh
dotnet run --no-restore --no-build --project src/tool/MechUvl.Tool.csproj --
```

Run a semantic check:

```sh
mech-uvl check path/to/root.uvl
```

Run only the core phase, or only the core plus typing phase:

```sh
mech-uvl check --phase core path/to/root.uvl
mech-uvl check --phase typing path/to/root.uvl
```

Show the successfully inferred introduced attribute types:

```sh
mech-uvl check --show-inferred-types path/to/root.uvl
```

Infer levels for the root model, or for all models in the built environment:

```sh
mech-uvl levels infer path/to/root.uvl
mech-uvl levels infer --scope all --format includes path/to/root.uvl
```

Select a non-default semantic variant:

```sh
mech-uvl check --attribute-intro global --typed-feature-as-bool path/to/root.uvl
mech-uvl check --undef-constraint-as-false --short-circuit --typed-feature-as-bool path/to/root.uvl
```

Format a UVL file with the default indentation:

```sh
mech-uvl fmt path/to/model.uvl
```

Format with four-space indentation or tabs:

```sh
mech-uvl fmt --indent-size 4 path/to/model.uvl
mech-uvl fmt --indent-style tabs path/to/model.uvl
```

Verify the Dafny core:

```sh
dafny verify dfyconfig.toml
```


## Getting Started with the Formalization

Recommended Reading Order: 

1. `extlib/core.dfy`            
1. `syntax/uvl_path.dfy`     
1. `syntax/uvl_ast.dfy`      
1. `syntax/uvl_env.dfy`      

1. `variant/uvl_variant.dfy` 

1. `well-formedness/uvl_basic_wf.dfy`
1. `well-formedness/uvl_models_wf.dfy`
1. `well-formedness/uvl_basic_levels.dfy`
1. `well-formedness/uvl_typing_env.dfy`     
1. `well-formedness/uvl_imports.dfy`.       
1. `well-formedness/uvl_references.dfy`         
1. `well-formedness/uvl_resolution.dfy`     
1. `well-formedness/uvl_uses.dfy`           
1. `well-formedness/uvl_models_typing.dfy` 
1. `well-formedness/uvl_models_levels.dfy`  

1. `analysis/uvl_errors.dfy`
1. `analysis/uvl_type_constraint_solver.dfy`
1. `analysis/uvl_constraint_sites.dfy`
1. `analysis/uvl_checks_support.dfy`
1. `analysis/uvl_checks_local.dfy`
1. `analysis/uvl_checks_use.dfy`
1. `analysis/uvl_models_basic_checks.dfy`
1. `analysis/uvl_type_inference.dfy`
1. `analysis/uvl_models_typing_checks.dfy`

1. `frontend/external.dfy`
1. `frontend/uvl_env_build.dfy`
1. `frontend/uvl_level_inference.dfy`

1. `semantics/uvl_configuration.dfy`
1. `semantics/uvl_structural_semantics.dfy`
1. `semantics/uvl_local_structural_admissibility.dfy`
1. `semantics/uvl_configuration_projection.dfy`
