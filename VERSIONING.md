# Versioning

`mech-uvl` uses semantic versioning from the start, including during the
private pre-release phase.

## Current Development Version

- `0.1.0-dev`

## Policy

- `MAJOR`: increment for intentional breaking changes to the exposed contract.
  This includes incompatible CLI changes, incompatible output-format changes,
  or incompatible changes to documented behavior.
- `MINOR`: increment for backward-compatible feature additions, such as new
  commands, new checks, broader UVL coverage, or new pretty-printing modes.
- `PATCH`: increment for backward-compatible fixes and corrections.

## Pre-1.0 Phase

Before `1.0.0`, the project stays in the `0.x.y` range:

- use `0.MINOR.0` for meaningful internal milestones;
- use `0.MINOR.PATCH` for bug-fix follow-ups on the same milestone;
- use `-dev` on the in-progress branch version between tags.

Examples:

- branch version: `0.1.0-dev`
- first milestone tag: `v0.1.0`
- next branch version after tagging: `0.2.0-dev`

## Where the Version Is Defined

- the current development version is defined in `Directory.Build.props`;
- release points are identified by git tags of the form `vMAJOR.MINOR.PATCH`;
- the CLI reports the current build version through `mech-uvl --version`.
