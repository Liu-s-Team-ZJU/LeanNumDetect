# External

This directory is the registration boundary for original theorems and formulas from external literature that have not yet been formalized.

## Registration policy

Only Lean files under `src/External/` may use `sorry`. Every such original result must appear in the table below with its exact source and theorem or formula identifier. For an unnumbered result, give a section, page, or nearby numbered formula instead of inventing a number.

Preserve the source's full statement, hypotheses, parameters, and normalization. Prove adaptations to this project outside this directory: reusable conversions belong in `src/General/` and theorem-specific conversions in their respective directories. Update this registry, imports, and audits together whenever an external result changes.

## Source registry

| File | Original source | Original theorem or formula identifier | Lean declaration |
| --- | --- | --- | --- |

There are currently no admitted external results.

`SeparatedCubeFourier.lean` retains only source-normalized definitions. The
former registration of Li's Theorem 2.3 was removed after source audit found
that the combined Lean statement used torus separation for both its continuous
and discrete conclusions, whereas the source uses Euclidean separation for the
continuous operator. The source's proof of the discrete statement for arbitrary
real radius also replaces `m` by `⌊m⌋` without preserving the separation
hypothesis. Fully proved algebraic and measure-theoretic reductions are recorded
in `General/Fourier/SeparatedCubeFourierInternal.lean` and
`General/Fourier/SeparatedCubeFourierContinuous.lean`; the missing
Beurling--Selberg/Barton extremal-function construction is not admitted.

## Enforcement

[Repository-wide CI](../../.github/ci/README.md) checks admissions by source
module rather than namespace and rejects project axioms. The complete proof and
attribution rules are in [AGENTS.md](../../AGENTS.md).
