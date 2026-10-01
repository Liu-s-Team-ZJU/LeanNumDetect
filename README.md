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
| Segmented-grid number-detection singular-value threshold (`thm:segmented_threshold`) | [Segmented.lean](src/NumDetect/Segmented.lean): theorem `segmentedGHM_singularValueThreshold` |
| Random-GHM number-detection threshold (`thm:resolutionrandghmnumber1`) | [Random.lean](src/NumDetect/Random.lean): theorem `randomGHM_singularValueThreshold_of_separation` |
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
| [src/External](src/External/README.md) | Source registry and one admitted original bounded-row concentration theorem |

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
rejects admissions outside `src/External/` and project-defined axioms. The
earlier random-sampling probability theorems, including both matrix Chernoff
tails and their analytic prerequisites, are fully proved with no `sorry`.
The original RandSamp audit checks that these results use only standard Lean
axioms. The new off-grid probability results depend on the one registered
original BDJR theorem in `src/External/`; their separate off-grid audit permits
exactly that direct admission and checks that every project conversion and
deterministic prerequisite is proved. NumDetect results remain admission-free.
If the shared
mathlib checkout is absent, run `python3 .github/ci/setup_mathlib.py` once before these
commands. See the [CI guide](.github/ci/README.md) for environment setup and
cache details.
