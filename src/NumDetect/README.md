# NumDetect

This directory contains the manuscript-facing definitions and main theoretical
results for source-number detection with generalized Hankel and Toeplitz
matrices. The modules are kept in one directory and grouped by descriptive
prefixes. Import [Main.lean](Main.lean) for the complete public interface.

## Main results and entry points

| Main result | Exact Lean location |
| --- | --- |
| Contiguous-grid VDM minimum-singular-value estimate (`lem:uniform-Vandermonde`) | [UniformVandermonde.lean](UniformVandermonde.lean): theorem `uniformVandermonde_minimumSingularValue` |
| Multidimensional number-detection resolution (`thm:li-resolution`) | [Uniform.lean](Uniform.lean): theorem `noAdmissibleMeasureWithFewerSupports` |
| Number-detection CRL upper bound (`eq:crl-number-upper`) | [CRL.lean](CRL.lean): theorem `numberDetectionCRL_le_numberDetectionSeparationThreshold` |
| Segmented-grid VDM minimum-singular-value estimate (`thm:segmented-vandermonde`) | [Segmented.lean](Segmented.lean): theorem `segmentedVandermonde_minimumSingularValue` |
| Segmented-grid number-detection singular-value threshold (`thm:segmented_threshold`) | [Segmented.lean](Segmented.lean): theorem `segmentedGHM_singularValueThreshold` |
| General GHM-MUSIC stability (`lem:stability_ghm_music`) | [MUSIC.lean](MUSIC.lean): theorem `ghmMUSIC_correlation_stability` |
| Segmented-grid MUSIC stability (`cor:stability_multidim_segmented`) | [MUSIC.lean](MUSIC.lean): theorem `segmentedMUSIC_correlation_stability` |

The exact GHM/GTM factorizations are structural foundations rather than main
theorems. The uniform threshold `uniformGHM_singularValueThreshold` is the
matrix-level input to the final number-detection resolution theorem. The exact
noiseless MUSIC characterization supports the perturbation result. The random-GHM
results are conditional on explicit properties of the realized frequency
draws; their scope is described below.

[CRL.lean](CRL.lean) also contains the two-sided and positive-amplitude CRL
statements. [Segmented.lean](Segmented.lean) provides one-dimensional variants
under the proved consecutive-block frame range in addition to the
multidimensional manuscript statements.

## Model and indexing conventions

`AtomicMeasure d n` implements the manuscript's reduced representation:
amplitudes are nonzero and nodes are pairwise distinct. `IsBandMeasurement`
contains the Fourier observation equation and the strict pointwise noise bound
on $[-\Omega,\Omega]^d$. `IsAdmissible` uses the same strict inequality.
`LpIndex` represents all $p\in[1,\infty]$, including a separate infinity case
for the resolution-limit definitions.

`IsAngularClumpStructure` represents a finite clump partition. It records a
surjective clump label, an upper bound $n^\star$ on every clump size, attainment
of that bound by at least one clump, a same-clump periodic $\ell^\infty$
diameter bound, and separation between different clumps.
`localSparsity_eq_of_angularClumpStructure` proves the resulting identity
$\nu_\infty(\tau,\mathcal X)=n^\star$.

Lean singular-value indices are zero-based. Thus the manuscript's
$\hat\sigma_n$ is `matrixSingularValue A (n - 1)`, and the paper range
$j=n+1,\ldots,L^d$ is represented by `n ≤ j ∧ j < L ^ d`.

## Proof organization

| Modules | Role |
| --- | --- |
| [Basic.lean](Basic.lean), [Matrices.lean](Matrices.lean), [MatrixFacts.lean](MatrixFacts.lean) | Atomic measures, measurements, admissibility, GHM/GTM and Vandermonde matrices, exact Fourier factorizations, and shared matrix estimates |
| [UniformDefinitions.lean](UniformDefinitions.lean), [UniformInterpolation.lean](UniformInterpolation.lean), [UniformVandermonde.lean](UniformVandermonde.lean), [UniformThreshold.lean](UniformThreshold.lean), [Uniform.lean](Uniform.lean) | Contiguous-grid interpolation, Vandermonde lower bounds, singular-value thresholding, and number-detection uniqueness |
| [SegmentedDefinitions.lean](SegmentedDefinitions.lean), [SegmentedVandermonde.lean](SegmentedVandermonde.lean), [SegmentedThreshold.lean](SegmentedThreshold.lean), [Segmented.lean](Segmented.lean) | Angular clumps, segmented interpolation packets, the multidimensional Vandermonde bound, and segmented GHM thresholding |
| [RandomMatrixBounds.lean](RandomMatrixBounds.lean), [Random.lean](Random.lean) | Matrix estimates and deterministic consequences for fixed realized random-frequency draws |
| [MUSICPerturbation.lean](MUSICPerturbation.lean), [MUSIC.lean](MUSIC.lean) | Fixed-rank trailing singular subspaces, noiseless MUSIC, general GHM stability, and the segmented specialization |
| [CRLLowerBound.lean](CRLLowerBound.lean), [CRL.lean](CRL.lean) | Finite-difference obstructions, upper guarantees, and two-sided computational resolution limits |
| [Main.lean](Main.lean) | Aggregate public import for all groups above |

The multidimensional segmented proof uses the translated-cube Fourier frame in
[General/Fourier/TranslatedCubeFourier.lean](../General/Fourier/TranslatedCubeFourier.lean).
Its conversion to the manuscript's angular one-sided cube is proved in
[General/Fourier/BartonCubeFrame.lean](../General/Fourier/BartonCubeFrame.lean).
The real cube is centered at `K / 2` with radius `(K + 1) / 2`, so its integer
points are exactly `{0, ..., K}^d` for either parity of `K`; this preserves the
manuscript denominator `K + 1` without rounding the radius.

## Formalization choices and manuscript gaps

| Topic | Formalized statement |
| --- | --- |
| Random GHM | `realizedRandomGHM_tail_singularValue_lt` proves the noise-tail conclusion for arbitrary dimension and fixed draws. `randomGHM_singularValueThreshold` proves the one-dimensional signal conclusion under explicit lower bounds for the two realized Vandermonde factors. No probability theorem is asserted: the manuscript assumes spread of the parent frequency sets but uses spread of the realized draws, which does not follow, and its “sufficiently close/small” conditions do not specify thresholds or an event. |
| MUSIC perturbation | The perturbed noise space is the trailing left singular subspace with the source rank fixed. Using the kernel of the perturbed adjoint would make the claimed stability false under arbitrarily small full-rank perturbations. The required perturbation theorem is proved in [MUSICSubspacePerturbation.lean](../General/MatrixAnalysis/MUSICSubspacePerturbation.lean). |
| CRL lower constant | The constant-$2$ lower bound, including the positive-amplitude case, is proved directly by finite differences. The cited Liu--Zhang result has the different constant $0.81e^{-3/2}$ for general complex amplitudes and does not supply the displayed constant-$2$ formula. |
| CRL endpoint | The CRL is defined with `sInf`. The upper-bound proof gives guarantees at every separation strictly above the displayed threshold, but does not prove that the endpoint is itself admissible; the manuscript's word “smallest” would require this additional attainment result. |

The translated-cube estimate is no longer an external admission. Barton's box
minorant, its exact mass, the modulated lattice sums, and the final exponential
relaxation are all proved in Lean. The one-dimensional Vaaler--Selberg and
Poisson-summation dependency is vendored with its source and license under
[vendor/vaaler](../../vendor/vaaler/README.md).

## Dependencies and verification

There are no admitted results in the current project. `src/External/` contains
only the repository's admission policy, and the CI audit rejects direct
admissions or project axioms elsewhere.

From the repository root, run:

```sh
python3 .github/ci/setup_mathlib.py --verify
lake build
python3 .github/ci/check.py
```

The final command explicitly builds every source module and checks declaration
bodies for `sorryAx` and project-defined axioms. See the
[repository guide](../../README.md) and [CI guide](../../.github/ci/README.md)
for environment and verification details.
