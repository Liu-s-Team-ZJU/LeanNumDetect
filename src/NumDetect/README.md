# NumDetect

This directory formalizes the NumDetect manuscript. Import [Main.lean](Main.lean)
for the public interface. The table follows the order of active definition,
theorem, lemma, corollary, and proposition environments in `main.tex`. It omits
commented-out statements and separately labeled equations. Only declarations
that directly encode a manuscript statement are listed; supporting declarations
are omitted. Names are in `LeanNumDetect.NumDetect` unless another namespace is
shown.

## Manuscript correspondence

| TeX type and label | Subject | Direct Lean declaration | Relationship |
| --- | --- | --- | --- |
| Definition `def:generalized-hankel-toeplitz` | Generalized Hankel and Toeplitz matrices | [Matrices.lean](Matrices.lean): `generalizedHankelOn`, `generalizedToeplitzOn` | **Stronger**; indexed frequency families may be infinite or contain repeats. Finite injective families give the manuscript matrices. |
| Definition `generalized vandermonde` | Generalized Vandermonde matrix and steering vector | [Matrices.lean](Matrices.lean): `generalizedVandermonde`, `steeringVector` | **Stronger**; indexed frequency families may be infinite or contain repeats. Finite injective families give the manuscript matrix. |
| Definition `def:generalized-vandermonde-decomposition` | Hankel/Toeplitz type Vandermonde decomposition | [Matrices.lean](Matrices.lean): `AdmitsGeneralizedVandermondeDecomposition` | **Stronger**; indexed row and column frequency families may be infinite or contain repeats. Finite injective families recover the manuscript definition. |
| Definition `def:sigma-admissible-measure` | $\sigma$-admissible and positive $\sigma$-admissible measures | [Basic.lean](Basic.lean): `IsAdmissible`, `IsPositiveAdmissible` | **Equivalent**. |
| Definition `def:crl-number` | General and positive number-detection CRL | [Basic.lean](Basic.lean): `numberDetectionCRL`, `positiveNumberDetectionCRL`; [CRL.lean](CRL.lean): `numberDetectionCRL_isSmallest`, `positiveNumberDetectionCRL_isSmallest` | **Equivalent**; both defining infima are attained and are the smallest nonnegative feasible thresholds for every $p$. |
| Theorem `thm:li-resolution` | Exclusion of admissible measures with fewer supports | [Uniform.lean](Uniform.lean): `noAdmissibleMeasureWithFewerSupports` | **Equivalent**. |
| Lemma `lem:uniform-Vandermonde` | Contiguous-grid minimum singular value | [UniformVandermonde.lean](UniformVandermonde.lean): `uniformVandermonde_minimumSingularValue` | **Equivalent**; the manuscript’s $n$th singular value has Lean index `n - 1`. |
| Theorem `liuthm5.1v2` | Contiguous-grid singular-value threshold | [Uniform.lean](Uniform.lean): `uniformGHM_singularValueThreshold` | **Equivalent**; the measurement and strict noise bound are required only on $\Gamma_s$. Lean singular-value indices start at zero. |
| Definition `defi:metric_separation` | Periodic distance and minimum separation | [Basic.lean](Basic.lean): `periodicDistance`, `extendedPeriodicMinimumSeparation` | **Equivalent**; `WithTop ℝ` represents the $+\infty$ convention for a singleton. |
| Definition `defi:local_sparsity` | Local neighborhood and sparsity | [Basic.lean](Basic.lean): `localNeighborhood`, `localSparsity` | **Equivalent** for a nonempty finite indexed node family. |
| Definition `defi:high_dim_clumps` | Multidimensional clump structure | [Basic.lean](Basic.lean): `IsAngularClumpStructure` | **Equivalent** for injectively indexed node sets. |
| Theorem `thm:segmented-vandermonde` | Segmented-grid minimum singular value | [Segmented/Main.lean](Segmented/Main.lean): `segmentedVandermonde_minimumSingularValue` | **Equivalent**; no additional frame hypothesis is required. |
| Theorem `thm:segmented_threshold` | Segmented-grid singular-value threshold | [Segmented/Main.lean](Segmented/Main.lean): `segmentedGHM_singularValueThreshold` | **Equivalent**; the observation equation and strict noise budget are assumed only on $\Gamma_{\mathrm{seg}}$. The signal bound retains the additional local geometry condition. |
| Theorem `thm:resolutionrandghmnumber1` | Random-GHM noise and signal thresholds | [Random.lean](Random.lean): `realizedRandomGHM_tail_singularValue_lt` (noise), `randomGHM_signalThreshold_of_separation` (signal) | Noise: **Stronger**, with a strict bound and no separation, local-cluster, or sampling-spread assumptions. Signal: **Equivalent**. |
| Theorem `thm:nonuniform_vdm_scaling` | Nonuniform one-dimensional Vandermonde scaling | [RandSamp/NonuniformVandermonde.lean](../RandSamp/NonuniformVandermonde.lean): `RandSamp.nonuniformVandermonde_minimumSingularValue` | **Stronger**; permits distinct real frequencies, gives an explicit positive small-separation threshold, and does not require $\tau<\pi/\theta_{\min}$. |
| Lemma `lem:stability_ghm_music` | General GHM-MUSIC perturbation | [MUSIC.lean](MUSIC.lean): `ghmMUSIC_correlation_stability` | **Stronger**; the diagonal coefficients may differ from the source amplitudes if their moduli retain the source's minimum-amplitude lower bound. The perturbed noise space is the fixed-rank trailing left singular subspace. |
| Corollary `cor:stability_multidim_segmented` | Segmented-grid MUSIC perturbation | [MUSIC.lean](MUSIC.lean): `segmentedMUSIC_correlation_stability` | **Equivalent**. |
| Lemma `lem:nonnegative_to_centered` | Unitary conversion from nonnegative to centered frequency grid | [UniformCentering.lean](UniformCentering.lean): `uniformVandermonde_centering` | **Equivalent**; proves the diagonal unitary factorization, equality of every singular value, and the noiseless matrix identity. |
| Lemma `lem2:uniform-Vandermonde` | Centered interpolation polynomial with a neighbor-product bound | [UniformInterpolation.lean](UniformInterpolation.lean): `CenteredPacket.exists_centeredUnitTorusInterpolation` | **Equivalent**; the integer-frequency presentation has the stated real cube support and the original pointwise neighbor-product bound. |
| Definition `defi:high_dim_uniform_poly` | Multivariate segmented trigonometric polynomials | [Segmented/Polynomial.lean](Segmented/Polynomial.lean): `SegmentedPolynomial`, `SegmentedPolynomial.eval` | **Equivalent**; `m < D` is stored in the polynomial structure. |
| Definition `defi:high_dim_lagrange` | Lagrange interpolant family | [Segmented/Polynomial.lean](Segmented/Polynomial.lean): `SegmentedPolynomial.IsLagrangeFamily` | **Equivalent**; `angularValue` evaluates $f(y/(2\pi))$. |
| Lemma `lem:minsvd_bound_by_lagInterp_high_dim` | Interpolants bound inverse minimum singular value | [Segmented/Interpolation.lean](Segmented/Interpolation.lean): `segmentedPolynomial_lagrange_minimumSingularValue` | **Equivalent**; positivity of the minimum singular value is also proved. |
| Lemma `lem:interpolation_via_svd` | Full-rank interpolation and $L^2/L^\infty$ bounds | [Segmented/Interpolation.lean](Segmented/Interpolation.lean): `segmentedPolynomial_interpolation_of_fullColumnRank` | **Equivalent**. |
| Theorem `thm:well_separated_segmented` | Two-sided singular-value estimate for separated nodes | [WellSeparatedSegmented.lean](WellSeparatedSegmented.lean): `wellSeparatedSegmented_singularValue_bounds` | **Equivalent**; includes $n=1$ and the endpoint $\beta=1/(2\log 2)$. |
| Proposition `prop:decomposition` | Partition of a subset into separated classes | [Segmented/ClumpBasics.lean](Segmented/ClumpBasics.lean): `angularClump_decomposition` | **Equivalent**; subsets are finite sets of node indices. |
| Lemma `lem:localization` | Polynomial vanishing outside an anchor neighborhood | [Segmented/ClumpBounds.lean](Segmented/ClumpBounds.lean): `localizationPolynomial_of_angularClumpStructure` | **Equivalent**; uses the manuscript’s $L^\infty$ norm bound. |
| Lemma `lem:freq_quantization` | Quantized integer frequency with phase separation | [Segmented/NeighborFactors.lean](Segmented/NeighborFactors.lean): `frequency_quantization_manuscript` | **Equivalent**; Hölder-conjugate exponents include the endpoints $1$ and $\infty$. |
| Lemma `lem:neighborset_segmented` | Neighbor-set interpolation polynomial and $L^2$ bound | [Segmented/Interpolation.lean](Segmented/Interpolation.lean): `neighborSetSegmented_polynomial_finiteSet` | **Equivalent**; the finite set and the short-neighbor product are stated explicitly. |

## Organization and conventions

| Modules | Contents |
| --- | --- |
| [Basic.lean](Basic.lean), [Matrices.lean](Matrices.lean), [MatrixFacts.lean](MatrixFacts.lean) | Atomic measures, Fourier observations, GHM/GTM definitions, factorizations, and matrix estimates |
| [UniformDefinitions.lean](UniformDefinitions.lean), [UniformInterpolation.lean](UniformInterpolation.lean), [UniformCentering.lean](UniformCentering.lean), [UniformVandermonde.lean](UniformVandermonde.lean), [UniformThreshold.lean](UniformThreshold.lean), [Uniform.lean](Uniform.lean) | Contiguous-grid interpolation, frequency centering, singular-value bounds, and number detection |
| [Segmented/](Segmented/), [WellSeparatedSegmented.lean](WellSeparatedSegmented.lean) | Clump geometry, segmented polynomials, interpolation, and segmented-grid estimates |
| [RandomMatrixBounds.lean](RandomMatrixBounds.lean), [Random.lean](Random.lean), [RandSamp/](../RandSamp/) | Fixed realized random-frequency draws and nonuniform Vandermonde bounds |
| [MUSICPerturbation.lean](MUSICPerturbation.lean), [MUSIC.lean](MUSIC.lean) | MUSIC noise spaces and stability |
| [CRLLowerBound.lean](CRLLowerBound.lean), [CRL.lean](CRL.lean) | CRL bounds, including the two-sided and positive-amplitude results corresponding to the manuscript's equation labels |

The equation-only CRL bounds are in [CRL.lean](CRL.lean) and
[CRLLowerBound.lean](CRLLowerBound.lean). The latter proves the constant-$2$
lower bound by a direct finite-difference construction.

## Verification

There are no admitted results in the current project. From the repository root:

```sh
python3 .github/ci/setup_mathlib.py --verify
lake build
python3 .github/ci/check.py
```

The final command checks every source module and audits declaration bodies for
`sorryAx` and project-defined axioms. See the [repository guide](../../README.md)
and [CI guide](../../.github/ci/README.md).
