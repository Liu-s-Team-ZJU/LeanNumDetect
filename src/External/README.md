# External admission registry

`src/External/` is reserved for original theorems or formulas from external
literature whose proofs have not yet been formalized. Only Lean files in this
directory may use `sorry`; proved definitions, lemmas, and conversions belong
under `src/General/` or the directory for the theorem that uses them.

Every admitted result must be registered below with its exact source, theorem
or formula identifier, and Lean declaration. Preserve the source's full
statement, hypotheses, parameters, and normalization. For an unnumbered result,
record a section, page, or nearby numbered formula instead of inventing a
number. Update the registry, imports, and repository audits together whenever
an external result is added, changed, proved, or removed.

| File | Original source | Original theorem or formula identifier | Lean declaration |
| --- | --- | --- | --- |
| `TranslatedCubeFourier.lean` | Weilin Li, *Nonharmonic multivariate Fourier transforms and matrices: condition numbers and hyperplane geometry*, ACHA 79 (2025), 101791 | Beurling--Selberg discussion preceding Theorem 2.2, Theorem 2.2, and the translated discrete argument in the proof of Theorem 2.3, Section 5.1 | `External.translatedCubeFourier_lowerFrame` |

The translated-cube bound above is the only admitted external result.
[Repository-wide CI](../../.github/ci/README.md) enforces the admission policy
and rejects project axioms; the complete proof and attribution rules are in
[AGENTS.md](../../AGENTS.md).
