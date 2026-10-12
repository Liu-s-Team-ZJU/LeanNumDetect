# LeanNumDetect

LeanNumDetect formalizes the theoretical results of the NumDetect manuscript on
source-number detection in multidimensional spectral super-resolution. It
covers generalized Hankel and Toeplitz factorizations, uniform and segmented
Vandermonde lower bounds, singular-value detection thresholds, MUSIC stability,
and computational resolution limits. Algorithms, complexity estimates, and
numerical experiments are outside the current scope.

Import `NumDetect.Main` for the NumDetect results and `RandSamp.Main` for the
nonuniform Fourier--Vandermonde estimate, fixed-support and uniform random
sampling, and off-grid relative Gram results of the RandSamp manuscript.

## Main theoretical results

| Main result | Exact Lean location |
| --- | --- |
| Contiguous-grid VDM minimum-singular-value estimate (`lem:uniform-Vandermonde`) | [Uniform/Vandermonde.lean](src/NumDetect/Uniform/Vandermonde.lean): theorem `uniformVandermonde_minimumSingularValue` |
| Multidimensional number-detection resolution (`thm:li-resolution`) | [Uniform/NumberDetection.lean](src/NumDetect/Uniform/NumberDetection.lean): theorem `noAdmissibleMeasureWithFewerSupports` |
| Number-detection CRL upper bound (`eq:crl-number-upper`) | [CRL/Bounds.lean](src/NumDetect/CRL/Bounds.lean): theorem `numberDetectionCRL_le_numberDetectionSeparationThreshold` |
| Segmented-grid VDM minimum-singular-value estimate (`thm:segmented-vandermonde`) | [Segmented/Main.lean](src/NumDetect/Segmented/Main.lean): theorem `segmentedVandermonde_minimumSingularValue` |
| Well-separated segmented VDM two-sided singular-value estimate (`thm:well_separated_segmented`) | [Segmented/WellSeparated.lean](src/NumDetect/Segmented/WellSeparated.lean): theorem `wellSeparatedSegmented_singularValue_bounds` |
| Fixed-node random sampling (`lem:fixed-support-singular-values`) | [FixedSupport.lean](src/RandSamp/FixedSupport.lean): theorem `fixedSupport_singularValues` |
| Fixed separated nodes (`thm:fixed-separated-singular-values`) | [FixedSeparated.lean](src/RandSamp/FixedSeparated.lean): theorem `fixedSeparated_singularValues` |
| Fixed separated nodes in higher dimensions (`thm:fixed-separated-singular-values-higher-dimensional`) | [FixedSeparatedCube.lean](src/RandSamp/FixedSeparatedCube.lean): theorem `fixedSeparatedCube_singularValues` |
| Multidimensional multiclump random row sampling and sharp lower exponent | [MultidimensionalMultiClumpTheorem.lean](src/RandSamp/MultidimensionalMultiClumpTheorem.lean): `multidimensionalMultiClump_random_row_sampling`, `multidimensionalMultiClump_sampling_with_sharp_lower` |
| Exact one-dimensional multiclump corollary | [MultiClumpTheorem.lean](src/RandSamp/MultiClumpTheorem.lean): `multiClump_sampling_statement` |
| Segmented-grid number-detection singular-value threshold (`thm:segmented_threshold`) | [Segmented/Main.lean](src/NumDetect/Segmented/Main.lean): theorem `segmentedGHM_singularValueThreshold` |
| Fourier-cube logarithmic determinant average (`lem:cube-logdet-mean`) | [Random/LogDetMean.lean](src/NumDetect/Random/LogDetMean.lean): `cubeNormalizedFourierRow_logDetMean_lower` |
| Smooth variational frame weights for random sampling | [SmoothWeightExistence.lean](src/General/Probability/SmoothWeightExistence.lean): `exists_smoothFramePotential_minimizer_of_entropy` and `smoothFramePotential_inverse_quadratic_lower_of_entropy`, [SmoothFrameStationarity.lean](src/General/MatrixAnalysis/SmoothFrameStationarity.lean): `smoothFramePotential_minimizer_stationary`, and [LogarithmicFrameSampling.lean](src/General/Probability/LogarithmicFrameSampling.lean): `sampleMean_logarithmic_frame_lower_bound_probability` |
| Multi-clump random VDM lower bound (`thm:random-cube-multiclump`) | [Random/ClumpVandermonde.lean](src/NumDetect/Random/ClumpVandermonde.lean): `positiveCubeClumpVandermonde_lower_highProbability`, with the exact [manuscript model bridge](src/NumDetect/Random/ClumpModel.lean), unnormalized $\mathcal V_{\mathcal W}$, explicit independent bandwidth and separation thresholds, $C(d,n,n^\star,\beta)$ and sample count $m\ge3n\rho^{-2}\log(n/\epsilon)$ |
| Multi-clump random-GHM number detection (`cor:random-ghm-number-detection-multiclump`) | [Random/ClumpMUSIC.lean](src/NumDetect/Random/ClumpMUSIC.lean): `positiveCubeClumpGHM_numberDetection_highProbability`, with the strict noise threshold and exact singular-value count |
| Multi-clump random-GHM MUSIC correlation stability (`cor:random-ghm-music-multiclump`) | [Random/ClumpMUSIC.lean](src/NumDetect/Random/ClumpMUSIC.lean): `positiveCubeClumpMUSIC_correlation_stability_highProbability` |
| General GHM-MUSIC stability (`lem:stability_ghm_music`) | [MUSIC/Stability.lean](src/NumDetect/MUSIC/Stability.lean): theorem `ghmMUSIC_correlation_stability` |
| Segmented-grid MUSIC stability (`cor:stability_multidim_segmented`) | [Segmented/MUSICStability.lean](src/NumDetect/Segmented/MUSICStability.lean): theorem `segmentedMUSIC_correlation_stability` |

See more in [NumDetect guide](src/NumDetect/README.md).

## Retained earlier NumDetect results

These declarations remain fully proved and available through
`NumDetect.Retained.Main`, but their former statements and sampling-spread definition have been
removed from the current manuscript. The new number-detection corollary uses
uniform random subsets; the earlier signal estimate instead applies to fixed
one-dimensional frequency families satisfying its sampling-spread condition.

| Former manuscript result | Retained Lean location |
| --- | --- |
| Random-GHM noise and signal thresholds (`thm:resolutionrandghmnumber1`) | [Retained/RealizedRandomGHM.lean](src/NumDetect/Retained/RealizedRandomGHM.lean): `realizedRandomGHM_tail_singularValue_lt`, `randomGHM_signalThreshold_of_separation` |
| Nonuniform VDM scaling (`thm:nonuniform_vdm_scaling`) | [NonuniformVandermonde.lean](src/RandSamp/NonuniformVandermonde.lean): `nonuniformVandermonde_minimumSingularValue`, with `finiteFamilySamplingSpread` |

The general library also retains standalone capped-weight iteration,
subspace-thickness estimates, and smooth weight constructions from thickness.
See the [matrix-analysis](src/General/MatrixAnalysis/README.md),
[Fourier](src/General/Fourier/README.md), and
[probability](src/General/Probability/README.md) guides for these reusable
alternatives. The current random-clump theorem uses the direct logarithmic
determinant and stationary-weight construction; its audit checks that proof
route as well as the trust boundary of the retained alternatives.

## Repository structure

| Path | Purpose |
| --- | --- |
| [src/NumDetect](src/NumDetect/README.md) | Manuscript results in MUSIC, Segmented, Random, Uniform, Preliminaries, Retained, and CRL; active interface `NumDetect.Main`, earlier results `NumDetect.Retained.Main` |
| [src/RandSamp](src/RandSamp/README.md) | Nonuniform Fourier--Vandermonde scaling, fixed-support and uniform random Fourier sampling, and off-grid relative Gram estimates |
| [src/SegmentedVDM](src/SegmentedVDM/README.md) | Independent one-dimensional segmented Vandermonde construction and singular-value theorem |
| [src/General](src/General/README.md) | Reusable finite, Fourier, matrix-analysis, and spectral-perturbation results |
| [src/External](src/External/README.md) | Source-attribution registry only; no Lean source files |

## Build and verify

The project uses Lean 4.32.0 and a pinned mathlib checkout. With Python 3.11 or
newer and the Lean environment available, run from the repository root:

```sh
python3 .github/ci/setup_mathlib.py --verify
lake build
python3 .github/ci/check.py
```

The first command verifies the pinned dependency checkout, `lake build` builds
the source libraries, and the final check builds every source module and
rejects every project admission and project-defined axiom, including in
private proofs and cached diagnostics. It also requires `src/External/` to
contain no Lean source files. Both matrix Chernoff tails, arbitrary-law
bounded-row concentration, and all RandSamp and NumDetect applications are
fully proved. The RandSamp, off-grid, multiclump sampling and [random-clump MUSIC audit](src/NumDetect/Random/ClumpAudit.lean) require the final results and their dependencies to use only standard Lean axioms.
If the shared
mathlib checkout is absent, run `python3 .github/ci/setup_mathlib.py` once before these
commands. See the [CI guide](.github/ci/README.md) for environment setup and
cache details.
