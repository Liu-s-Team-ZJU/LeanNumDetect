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
| Contiguous-grid VDM minimum-singular-value estimate (`lem:uniform-Vandermonde`) | [UniformVandermonde.lean](src/NumDetect/UniformVandermonde.lean): theorem `uniformVandermonde_minimumSingularValue` |
| Multidimensional number-detection resolution (`thm:li-resolution`) | [Uniform.lean](src/NumDetect/Uniform.lean): theorem `noAdmissibleMeasureWithFewerSupports` |
| Number-detection CRL upper bound (`eq:crl-number-upper`) | [CRL.lean](src/NumDetect/CRL.lean): theorem `numberDetectionCRL_le_numberDetectionSeparationThreshold` |
| Segmented-grid VDM minimum-singular-value estimate (`thm:segmented-vandermonde`) | [Segmented.lean](src/NumDetect/Segmented.lean): theorem `segmentedVandermonde_minimumSingularValue` |
| Well-separated segmented VDM two-sided singular-value estimate (`thm:well_separated_segmented`) | [WellSeparatedSegmented.lean](src/NumDetect/WellSeparatedSegmented.lean): theorem `wellSeparatedSegmented_singularValue_bounds` |
| Nonuniform VDM scaling (`thm:nonuniform_vdm_scaling`) | [NonuniformVandermonde.lean](src/RandSamp/NonuniformVandermonde.lean): theorem `nonuniformVandermonde_minimumSingularValue` |
| Fixed-node random sampling (`lem:fixed-support-singular-values`) | [FixedSupport.lean](src/RandSamp/FixedSupport.lean): theorem `fixedSupport_singularValues` |
| Fixed separated nodes (`thm:fixed-separated-singular-values`) | [FixedSeparated.lean](src/RandSamp/FixedSeparated.lean): theorem `fixedSeparated_singularValues` |
| Fixed separated nodes in higher dimensions (`thm:fixed-separated-singular-values-higher-dimensional`) | [FixedSeparatedCube.lean](src/RandSamp/FixedSeparatedCube.lean): theorem `fixedSeparatedCube_singularValues` |
| Multidimensional multiclump random row sampling and sharp lower exponent | [MultidimensionalMultiClumpTheorem.lean](src/RandSamp/MultidimensionalMultiClumpTheorem.lean): `multidimensionalMultiClump_random_row_sampling`, `multidimensionalMultiClump_sampling_with_sharp_lower` |
| Exact one-dimensional multiclump corollary | [MultiClumpTheorem.lean](src/RandSamp/MultiClumpTheorem.lean): `multiClump_sampling_statement` |
| Segmented-grid number-detection singular-value threshold (`thm:segmented_threshold`) | [Segmented.lean](src/NumDetect/Segmented.lean): theorem `segmentedGHM_singularValueThreshold` |
| Random-GHM number-detection threshold (`thm:resolutionrandghmnumber1`) | [Random.lean](src/NumDetect/Random.lean): theorem `randomGHM_singularValueThreshold_of_separation` |
| Multi-clump random VDM lower bound (`thm:random-cube-multiclump`) | [RandomClumpVandermonde.lean](src/NumDetect/RandomClumpVandermonde.lean): `positiveCubeClumpVandermonde_lower_highProbability`, with the exact [manuscript model bridge](src/NumDetect/RandomClumpModel.lean), unnormalized $\mathcal V_{\mathcal W}$, explicit independent bandwidth and separation thresholds, $C(d,n,n^\star,\beta)$ and sample count $m\ge3n\rho^{-2}\log(n/\epsilon)$ |
| Multi-clump random-GHM number detection | [RandomClumpMUSIC.lean](src/NumDetect/RandomClumpMUSIC.lean): `positiveCubeClumpGHM_numberDetection_highProbability`, with the strict noise threshold and exact singular-value count |
| Multi-clump random-GHM MUSIC correlation stability (`cor:random-ghm-music-multiclump`) | [RandomClumpMUSIC.lean](src/NumDetect/RandomClumpMUSIC.lean): `positiveCubeClumpMUSIC_correlation_stability_highProbability` |
| General GHM-MUSIC stability (`lem:stability_ghm_music`) | [MUSIC.lean](src/NumDetect/MUSIC.lean): theorem `ghmMUSIC_correlation_stability` |
| Segmented-grid MUSIC stability (`cor:stability_multidim_segmented`) | [MUSIC.lean](src/NumDetect/MUSIC.lean): theorem `segmentedMUSIC_correlation_stability` |

See more in [NumDetect guide](src/NumDetect/README.md).

## Repository structure

| Path | Purpose |
| --- | --- |
| [src/NumDetect](src/NumDetect/README.md) | Manuscript definitions and main results, grouped by flat module prefixes with aggregate import `NumDetect.Main` |
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
fully proved. The RandSamp, off-grid, multiclump sampling and [random-clump MUSIC audit](src/NumDetect/RandomClumpMUSICAudit.lean) require the final results and their dependencies to use only standard Lean axioms.
If the shared
mathlib checkout is absent, run `python3 .github/ci/setup_mathlib.py` once before these
commands. See the [CI guide](.github/ci/README.md) for environment setup and
cache details.
