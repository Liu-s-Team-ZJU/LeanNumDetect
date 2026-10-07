# Independent one-dimensional manuscript–Lean consistency review

Fresh source comparison completed on October 8, 2026, after the multidimensional multiclump theorem replaced the former independent one-dimensional proof. This report supersedes the earlier primary-theorem mapping and verification counts. The reviewer did not author or edit the manuscript or Lean proofs. The previously completed concentration review is retained below with its original scope.

**Verdict: the primary theorem in [MultiClumpRandomSampling.tex](MultiClumpRandomSampling.tex) remains exactly the current Lean statement, with sampling constant $3072$. Its proof is now an exact dimension-one corollary of the fully proved frequency-cube theorem. No unresolved statement discrepancy remains.** The general theorem, model, sharp lower exponent and detailed proof review are recorded in [MultidimensionalMultiClumpConsistency.md](MultidimensionalMultiClumpConsistency.md).

## Exact preservation and specialization

I compared the current source with the previous repository version directly. The complete definitions `multiClumpSamplingConstant`, `MultiClumpSuccess`, `MultiClumpSamplingConclusion`, `MultiClumpSamplingStatement` and `MultiClumpDeterministicControl` in [MultiClumpSampling.lean](../src/RandSamp/MultiClumpSampling.lean) are unchanged. The declaration types of all three public results `multiClump_deterministic_control`, `multiClump_random_row_sampling` and `multiClump_sampling_statement` are also unchanged. The proof bodies and supporting imports have changed.

| Item | Current manuscript and Lean correspondence |
| --- | --- |
| Fixed constant | `multiClumpSamplingConstant` is exactly $3072$. The cube constant $3072\,512^{d-1}$ simplifies to this value at $d=1$. |
| Outer quantifiers | Every $2\le n^\star\le n$ precedes the existence of $0<c_0<1$ and $C_0\ge n$. These geometry constants precede $M$, the partition, nodes, $K,\Delta,m,\rho,\delta$ and do not depend on $K$ or $\Delta$. |
| Geometry and maximum | `ClumpPartition` gives nonempty exhaustive disjoint fibers; `HasMaxClumpSize` includes attainment. `MultiClumpGeometry` requires distinct angular nodes, within-clump diameter at most $c_0/M$, and cross distance at least $C_0/M$. These are exactly the dimension-one cube hypotheses. |
| Representatives and matrices | Angular winding distance, the full normalization $(M+1)^{-1/2}$ and sampled normalization $m^{-1/2}$ are unchanged. `cubeFullVandermonde_one_reindex`, `cubeFullGram_one` and the full/sampled singular-value identities prove equality under frequency reindexing. |
| Actual subset law | `Equiv.funUnique` identifies `Fin 1 → Fin (M+1)` with `Fin (M+1)`. `finiteSampleEquiv` identifies actual $m$-element subsets, and `probability_comp_equiv` preserves their uniform counting law. The range remains $1\le m\le M+1$. |
| Exact sufficient rate | `sizePowerSum 1` is exactly `sizeSquareSum`. The condition remains $m\ge3072\rho^{-2}\sum_a n_a^2\log(2n/\delta)$ with $\rho,\delta\in(0,1)$ and probability at least $1-\delta$. No full-sampling alternative or inverse-spacing factor is introduced. |
| Complete common event | `multidimensionalMultiClumpSuccess_one` specializes Gram order, all $n$ ordered column singular values, and every admissible $K,\Delta$ inside one event. `multiClumpSamplingConclusion_of_multidimensional_one` transports the complete probability conclusion with the same spectral functions. |
| Least singular value | `multidimensionalClumpUpperExponent 1 nstar` is $n^\star-1$, so both powers remain $n^\star-1$, with the exact factors $\sqrt{1\pm\rho}$. The least column singular value has Lean index $n-1$. |
| Fixed-node scope | Nodes remain fixed outside probability. The one relative Gram event works for all coefficient vectors and later spacing choices; no uniform event over varying node configurations is claimed. |

The proof chain in [MultiClumpTheorem.lean](../src/RandSamp/MultiClumpTheorem.lean) is now explicit:

- `multiClump_deterministic_control` applies `multidimensionalMultiClump_deterministic_control` at dimension one, followed by deterministic transport.
- `multiClump_random_row_sampling` applies `multidimensionalMultiClump_random_row_sampling` at dimension one, followed by complete sampling-conclusion transport.
- `multiClump_sampling_statement` packages this same result with the original fixed positive constant.

The original deterministic-to-sampling adapter is also transported through dimension one. Its reverse adapter proves the cube positive-definiteness field from the already present distinctness and bandwidth hypotheses; it adds no hypothesis to the original statement. The dimension-one identification covers all one-coordinate functions, not only a restricted subclass of node tuples.

The former project modules `ClumpSignals`, `ClumpSingularLower`, `ClumpSingularUpper`, `ClumpSubspaceGeometry`, `MultiClumpAssembly`, `MultiClumpLeverage` and `SingleClumpLeverage` have been removed. A source search confirms that no imports of those modules remain. Their obsolete line references and proof mappings have therefore been removed from this report. Reusable polynomial, companion, Fourier and finite-energy tools remain in `General`; the final geometry and sampling proof is the multidimensional one.

The primary theorem preserves its original existential spectral constants. The specialization need not return the particular numerical witnesses used by the former independent proof: no such witness values occur in the retained manuscript or public theorem types. The sampling constant, hypotheses, event, exponents and all quantifiers are exact.

## Previously reviewed arbitrary-law concentration replacement

Before deletion of the old external source, I captured its complete `boundedRows_concentration` declaration. I compared it with the final [BoundedRieszConcentration.lean](../src/General/Probability/BoundedRieszConcentration.lean), line 53. **The declaration type is verbatim identical**, including every quantifier, hypothesis, normalization, logarithm, and strict probability inequality. The proof supplies $\kappa=1$, $c_0=10^{12}$, and $c_1=178$ for the existing existential-constant statement.

| Item | Independent check |
| --- | --- |
| Quantifiers and parameters | All three universal positive constants occur before $N,m,s,K,\delta$, both probability spaces and their measures, the random variables, and the target set. The two spaces retain independent universe parameters. $s,K$ are arbitrary positive real numbers; no integer sparsity or lower-envelope condition is added. |
| Laws and target sets | The theorem retains arbitrary complex bounded row distributions, independent identically distributed copies, and arbitrary subsets of the actual coordinate $\ell^1$ ball. No finite-law, rational-weight, finite-target, isotropy, orthogonality, real-coefficient, or target-measurability hypothesis appears. |
| Rate and event | The premise remains exactly $c_0K^2\delta^{-2}s\log(eN)\log^2(sK^2/\delta)\le m$. The conclusion remains the actual normalized empirical-energy deviation with the original population-energy supremum and success probability strictly exceeding $1-2\exp(-\delta^2m/(sK^2))$. |
| Causal sharp expectation | The proved prefix identity uses only approximants through the selected shell level. Separable clipped real and imaginary squares allow scalar contraction; cardinality-normalized mask processes have a proved squared-maximum bound. Pathwise Cauchy–Schwarz retains the square root of the number of levels. `WeakShellDecomposition.lean:151` retains the exceptional-row energy explicitly in both the residual and shell-mass estimates. Neither of the earlier lookahead-counting or omitted-exception concerns remains in this construction. |
| Closing the finite estimate | `finiteBoundedRow_expectation_le` (`FiniteBoundedRowExpectation.lean:194`) proves the required expectation estimate under arbitrary nonnegative real weights summing to one. Adding the zero target preserves both energy and deviation maxima exactly. The small-envelope branch is handled deterministically, so the auxiliary $4\delta\le sK^2$ condition is discharged. The variance-sensitive replacement-entropy proof gives the literal exponential rate with finite threshold coefficient 88. |
| Lifting to arbitrary laws and sets | Measurable finite row quantization preserves the exact coordinate envelope $K$. Its pushforward singleton weights represent the law and its iid product exactly. Finite coefficient approximants lie inside the original target set; uniform perturbation estimates control every original coefficient vector. `restrictedDeviation_aemeasurable` (`BoundedRowContinuity.lean:161`) proves measurability through continuity in the sampled row tuple without regularity of the target. `boundedRows_concentration_of_finite` (`BoundedRowsFiniteReduction.lean:115`) absorbs the explicit approximation errors, giving $2\cdot88+2=178$. Its failure bound by one exponential implies the original strict success bound with the factor two. |

The statement agrees with [BDJR Theorem 1.1, manuscript page 2](https://arxiv.org/pdf/2005.06994). The new construction proves that statement directly; it does not rely on the earlier source-proof indexing argument. No unresolved statement or proof-interface discrepancy remains.

## Current trust boundary and verification evidence

The reviewer independently ran the final `.github/ci/check.py` once after the Lean source was frozen; it exited with code 0. The regenerated [CI log](../build/ci-check.log) records a successful explicit-source build of **9013 jobs** and a whole-project result of **271 modules, 4780 declarations, zero admissions and zero project axioms**. The inspected [default full-build log](../build/full-build.log) records success for **9017 jobs**. These are regenerated current-source results, replacing the former 262-module verification counts.

The checker discovers and builds every source module, including unused modules, checks persisted compiler admission warnings, lexes source tokens, and imports all project modules with private declarations and proof bodies. It rejects admitted types or proofs and every project axiom, with no named-result exceptions. `src/External` contains only its source-attribution README and no Lean source files.

[MultiClumpAudit.lean](../src/RandSamp/MultiClumpAudit.lean) confirms that the cube theorem, joint sharp lower conclusion, exact dimension-one corollary, deterministic dependencies and real-exponent sharpness use only `propext`, `Classical.choice` and `Quot.sound`. The all-source run also includes the unchanged arbitrary-law concentration and off-grid audit chain reviewed above. The complete multiclump result has zero transitive admissions. The final proof now reaches the original one-dimensional theorem through the multidimensional result and exact subset-law transport.

The detailed current multidimensional statement and proof checks are in [MultidimensionalMultiClumpConsistency.md](MultidimensionalMultiClumpConsistency.md). Both report files were checked for resolving local links and clean whitespace.
