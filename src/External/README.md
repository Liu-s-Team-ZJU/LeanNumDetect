# External admission policy

`src/External/` is reserved for original theorems or formulas from external
literature whose proofs have not yet been formalized. Only Lean files in this
directory may use `sorry`; proved definitions, lemmas, and conversions belong
under `src/General/` or the directory for the theorem that uses them.

Every admitted result must be registered here with its exact source, theorem
or formula identifier, and Lean declaration. Preserve the source's full
statement, hypotheses, parameters, and normalization. For an unnumbered result,
record a section, page, or nearby numbered formula instead of inventing a
number. Update the registry, imports, and repository audits together whenever
an external result is added, changed, proved, or removed.

There are currently no admitted results and therefore no Lean files in this
directory. [Repository-wide CI](../../.github/ci/README.md) enforces the
admission policy and rejects project axioms; the complete proof and attribution
rules are in [AGENTS.md](../../AGENTS.md).
