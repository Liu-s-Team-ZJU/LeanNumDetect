# Repository-wide Lean CI

The [workflow](../workflows/lean.yml) runs on pushes, pull requests, and manual dispatch. It builds every Lean source module and checks the repository's proof-admission boundary. It does not run `lake test` or rely on a whitelist of theorem names, test instances, or external-declaration counts.

## Local commands

With the pinned Lean toolchain and shared dependencies installed, use Python 3.11 or newer to run the same checks as CI from the repository root:

```sh
python3 .github/ci/check.py
```

To verify the dependency environment without building or changing it:

```sh
python3 .github/ci/setup_mathlib.py --verify
```

For a normal incremental project build, use `lake build`. If elan is not on `PATH`, the executable is also available as `~/.elan/bin/lake`. Build artifacts and Python caches are not committed.

## Pinned environment and shared paths

| Configuration | Purpose |
| --- | --- |
| [lean-toolchain](../../lean-toolchain) | Pins Lean 4.32.0 for this project without changing the user's default toolchain |
| [mathlib-revision](mathlib-revision) | Pins mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997` |
| [lakefile.toml](../../lakefile.toml) | Selects the external mathlib checkout, shared package directory, and project libraries |
| [lake-manifest.json](../../lake-manifest.json) | Records package paths and exact dependency revisions |

Lake resolves paths relative to the repository root. The current mathlib path is `../../.local/share/lean/mathlib4-v4.32.0`, and `packagesDir` points to its `.lake/packages` subdirectory. This layout reuses the shared checkout and compiled dependency caches rather than installing mathlib inside the project. If the repository moves to a different directory depth, keep the paths in both the Lake configuration and manifest consistent.

Verification checks actual Git revisions, rejects tracked local modifications in dependency checkouts, and confirms that mathlib and the project require the same Lean toolchain. Updating Lean or mathlib requires coordinated changes to the toolchain pin, mathlib revision, Lake configuration, and manifest.

## Build and admission checks

[check.py](check.py) reads `srcDir` from the Lake configuration and discovers every `.lean` file below it. It passes every source file to Lake explicitly, including modules that no other file imports. New source directories must belong to a configured Lake library.

[CheckAdmissions.lean](CheckAdmissions.lean) loads full declaration information, including private declarations and proof bodies, and enforces these rules:

- Only declarations originating in `src/External/` may directly contain `sorryAx`, whether introduced by `sorry`, `admit`, or a direct call.
- Other directories may depend on registered External results, but must provide their own proofs.
- New project `axiom` declarations cannot bypass the boundary.
- Ownership is determined by the source module, not the declaration namespace. A hypothetical `src/External.lean` at the source root is not inside `src/External/`.

The check also inspects persisted compiler diagnostics and scans source code with Lean's lexer. Consequently, anonymous `example` declarations cannot hide missing proofs by disabling `warn.sorry`, and cached diagnostics are checked too. Comments, documentation, name literals, and ordinary string text are not treated as admissions; expressions inside interpolated strings are checked.

The source-registration requirements for original external results are documented in [AGENTS.md](../../AGENTS.md) and the [External registry](../../src/External/README.md).

## CI setup and caching

[setup_mathlib.py](setup_mathlib.py) resolves the shared path from the existing Lake configuration. In a fresh environment it creates a mathlib checkout at the pinned revision outside the repository. For an existing checkout it verifies the revision rather than resetting or overwriting it. This script alone does not install the entire Lean and mathlib dependency environment.

The workflow then uses the official [lean-action](https://github.com/leanprover/lean-action) to install Lean and obtain mathlib's precompiled artifacts. GitHub caches the Lean installation and pinned dependencies; project source is built from a fresh checkout. All Actions are pinned to full commit hashes.

CI uses `LEAN_NUM_THREADS=2`. To use the same thread setting locally:

```sh
LEAN_NUM_THREADS=2 python3 .github/ci/check.py
```
