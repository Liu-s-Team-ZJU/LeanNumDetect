# External

This directory is the registration boundary for original theorems and formulas from external literature that have not yet been formalized. It currently contains no external-result Lean files; the project has no direct admissions.

## Registration policy

Only Lean files under `src/External/` may use `sorry`. Every such original result must appear in the table below with its exact source and theorem or formula identifier. For an unnumbered result, give a section, page, or nearby numbered formula instead of inventing a number.

Preserve the source's full statement, hypotheses, parameters, and normalization. Prove adaptations to this project outside this directory: reusable conversions belong in `src/General/` and theorem-specific conversions in their respective directories. Update this registry, imports, and audits together whenever an external result changes.

## Source registry

| File | Original source | Original theorem or formula identifier | Lean declaration |
| --- | --- | --- | --- |

There are currently no entries. The empty registry and its rules are retained for future external results.

## Enforcement

[Repository-wide CI](../../.github/ci/README.md) checks admissions by source
module rather than namespace and rejects project axioms. The complete proof and
attribution rules are in [AGENTS.md](../../AGENTS.md).
