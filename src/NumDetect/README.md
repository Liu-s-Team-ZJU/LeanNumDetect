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
| Definition `def:generalized-hankel-toeplitz` | Generalized Hankel and Toeplitz matrices | [Matrices.lean](Matrices.lean): `generalizedHankelOn`, `generalizedToeplitzOn` | **Equivalent**. |
| Definition `generalized vandermonde` | Generalized Vandermonde matrix and steering vector | [Matrices.lean](Matrices.lean): `generalizedVandermonde`, `steeringVector` | **Equivalent**. |
| Definition `def:generalized-vandermonde-decomposition` | Hankel/Toeplitz type Vandermonde decomposition | [Matrices.lean](Matrices.lean): `AdmitsGeneralizedVandermondeDecomposition` | **Equivalent**. |
| Definition `def:sigma-admissible-measure` | $\sigma$-admissible and positive $\sigma$-admissible measures | [Basic.lean](Basic.lean): `IsAdmissible`, `IsPositiveAdmissible` | **Equivalent**. |
| Definition `def:crl-number` | General and positive number-detection CRL | [Basic.lean](Basic.lean): `numberDetectionCRL`, `positiveNumberDetectionCRL`; [CRL.lean](CRL.lean): `numberDetectionCRL_isSmallest`, `positiveNumberDetectionCRL_isSmallest` | **Equivalent**. |
| Theorem `thm:li-resolution` | Exclusion of admissible measures with fewer supports | [Uniform.lean](Uniform.lean): `noAdmissibleMeasureWithFewerSupports` | **Equivalent**. |
| Lemma `lem:uniform-Vandermonde` | Contiguous-grid minimum singular value | [UniformVandermonde.lean](UniformVandermonde.lean): `uniformVandermonde_minimumSingularValue` | **Equivalent**. |
| Theorem `liuthm5.1v2` | Contiguous-grid singular-value threshold | [Uniform.lean](Uniform.lean): `uniformGHM_singularValueThreshold` | **Equivalent**. |
| Definition `defi:metric_separation` | Periodic distance and minimum separation | [Basic.lean](Basic.lean): `periodicDistance`, `extendedPeriodicMinimumSeparation` | **Equivalent**. |
| Definition `defi:local_sparsity` | Local neighborhood and sparsity | [Basic.lean](Basic.lean): `localNeighborhood`, `localSparsity` | **Equivalent**. |
| Definition `defi:high_dim_clumps` | Multidimensional clump structure | [Basic.lean](Basic.lean): `IsAngularClumpStructure` | **Equivalent**. |
| Theorem `thm:segmented-vandermonde` | Segmented-grid minimum singular value | [Segmented/Main.lean](Segmented/Main.lean): `segmentedVandermonde_minimumSingularValue` | **Equivalent**. |
| Theorem `thm:segmented_threshold` | Segmented-grid singular-value threshold | [Segmented/Main.lean](Segmented/Main.lean): `segmentedGHM_singularValueThreshold` | **Equivalent**. |
| Lemma `lem:random-cube-vandermonde` | Fixed-support random cube Vandermonde minimum singular-value lower bound | [RandomCubeMUSIC.lean](RandomCubeMUSIC.lean): `positiveCubeVandermonde_lower_highProbability` | **Equivalent**; only the lower bound is exposed, and the automatic periodic upper spacing bound is proved internally. |
| Lemma `lem:random-cube-multiclump` | Unnormalized multi-clump random cube Vandermonde minimum singular-value lower bound | [RandomClumpVandermonde.lean](RandomClumpVandermonde.lean): `positiveCubeClumpVandermonde_lower_highProbability` | **Equivalent**; exact $(A,\infty,\tau,\eta,n^\star)$ geometry, literal sampling coefficient $3$, $C(d,n^\star)$, and $\sqrt{m(1-\rho)}$ on the right. No upper spectral conclusion or comparable-spacing premise. |
| Paragraph following `lem:random-cube-multiclump` | Random-GHM number detection under multi-clump and well-separated geometry | [RandomClumpMUSIC.lean](RandomClumpMUSIC.lean): `positiveCubeClumpGHM_numberDetection_highProbability`; [RandomCubeNumberDetection.lean](RandomCubeNumberDetection.lean): `positiveCubeGHM_numberDetection_highProbability` | **Equivalent**; proves the strict signal and tail thresholds and exactly $n$ values above $\sigma\sqrt{M_1M_2}$. |
| Theorem `thm:resolutionrandghmnumber1` | Random-GHM noise and signal thresholds | [Random.lean](Random.lean): `realizedRandomGHM_tail_singularValue_lt` (noise), `randomGHM_signalThreshold_of_separation` (signal) | **Equivalent**. |
| Theorem `thm:nonuniform_vdm_scaling` | Nonuniform one-dimensional Vandermonde scaling | [RandSamp/NonuniformVandermonde.lean](../RandSamp/NonuniformVandermonde.lean): `RandSamp.nonuniformVandermonde_minimumSingularValue` | **Equivalent**. |
| Lemma `lem:stability_ghm_music` | General GHM-MUSIC perturbation | [MUSIC.lean](MUSIC.lean): `ghmMUSIC_correlation_stability` | **Equivalent**. |
| Theorem `thm:ghm-music-location-stability` | Location stability for the separated continuous MUSIC selection | [MUSICLocation.lean](MUSICLocation.lean): `ghmMUSIC_location_stability`; [MUSICSelector.lean](MUSICSelector.lean): `exists_ghmMUSIC_location_stability` | **Equivalent**; the selector theorem also proves existence and universal minimization on compact search regions. |
| Theorem `thm:ghm-music-peak-stability` | Continuous selection of the `n` lowest local minima with a location bound | [MUSICPeakSelection.lean](MUSICPeakSelection.lean): `exists_top_MUSIC_peaks_of_globalGrowth_and_strictConvex`; [MUSICPeakReciprocal.lean](MUSICPeakReciprocal.lean): `top_squaredResidual_minima_are_extendedMUSIC_peaks` | **Conditional selection layer**; derives the exterior value gap and location error from growth and residual perturbation, assuming strict convexity of the noisy squared residual on source neighborhoods. The reciprocal theorem identifies these minima with the highest continuous MUSIC peaks, including zeros of the residual. |
| Corollary `cor:segmented-music-peaks` | Largest continuous MUSIC peaks for equally distributed arrays | [SegmentedMUSICPeakFinal.lean](SegmentedMUSICPeakFinal.lean): `exists_segmentedMUSIC_highestExtendedPeaks_explicit` | **Equivalent for continuous local peaks**; proves one of the top `n` peaks near each source, strict dominance over all other local peaks, and the displayed explicit location error. The reciprocal image is extended real valued, with value $\infty$ at residual zeros. The analytic curvature bounds are proved in the Fourier and projector modules below. |
| Proposition `prop:segmented-music-growth` | Explicit noiseless MUSIC residual growth for equally distributed arrays | [SegmentedMUSICGrowth.lean](SegmentedMUSICGrowth.lean): `segmentedMUSIC_growth` | **Equivalent**; proves full column rank and positivity of the exact displayed growth constant. |
| Corollary `cor:stability_multidim_segmented` | Segmented-grid MUSIC perturbation | [MUSIC.lean](MUSIC.lean): `segmentedMUSIC_correlation_stability` | **Equivalent**. |
| Corollary `cor:segmented-music-location` | Explicit location error for equally distributed arrays under multi-clump geometry | [SegmentedMUSICLocation.lean](SegmentedMUSICLocation.lean): `exists_segmentedMUSIC_location_stability_explicit` | **Equivalent** for the separated continuous minimax selection; proves existence, the displayed measurement-noise condition, and the displayed location-error constant. |
| Corollary `cor:random-ghm-music-well-separated` | Fixed-support high-probability random-GHM MUSIC correlation bound | [RandomCubeMUSIC.lean](RandomCubeMUSIC.lean): `positiveCubeMUSIC_correlation_stability_highProbability` | **Equivalent**. |
| Corollary `cor:random-ghm-music-multiclump` | Fixed-source high-probability random-GHM MUSIC correlation stability under the original multi-clump geometry | [RandomClumpMUSIC.lean](RandomClumpMUSIC.lean): `positiveCubeClumpMUSIC_correlation_stability_highProbability` | **Equivalent**; exact periodic one-norm spacing, independent uniform subsets, and the deterministic measurement-noise bound. No arrangement or comparable-spacing hypothesis is introduced. |
| Lemma `lem:nonnegative_to_centered` | Unitary conversion from nonnegative to centered frequency grid | [UniformCentering.lean](UniformCentering.lean): `uniformVandermonde_centering` | **Equivalent**. |
| Lemma `lem2:uniform-Vandermonde` | Centered interpolation polynomial with a neighbor-product bound | [UniformInterpolation.lean](UniformInterpolation.lean): `CenteredPacket.exists_centeredUnitTorusInterpolation` | **Equivalent**. |
| Definition `defi:high_dim_uniform_poly` | Multivariate segmented trigonometric polynomials | [Segmented/Polynomial.lean](Segmented/Polynomial.lean): `SegmentedPolynomial`, `SegmentedPolynomial.eval` | **Equivalent**. |
| Definition `defi:high_dim_lagrange` | Lagrange interpolant family | [Segmented/Polynomial.lean](Segmented/Polynomial.lean): `SegmentedPolynomial.IsLagrangeFamily` | **Equivalent**. |
| Lemma `lem:minsvd_bound_by_lagInterp_high_dim` | Interpolants bound inverse minimum singular value | [Segmented/Interpolation.lean](Segmented/Interpolation.lean): `segmentedPolynomial_lagrange_minimumSingularValue` | **Equivalent**. |
| Lemma `lem:interpolation_via_svd` | Full-rank interpolation and $L^2/L^\infty$ bounds | [Segmented/Interpolation.lean](Segmented/Interpolation.lean): `segmentedPolynomial_interpolation_of_fullColumnRank` | **Equivalent**. |
| Theorem `thm:well_separated_segmented` | Two-sided singular-value estimate for separated nodes | [WellSeparatedSegmented.lean](WellSeparatedSegmented.lean): `wellSeparatedSegmented_singularValue_bounds` | **Equivalent**. |
| Proposition `prop:decomposition` | Partition of a subset into separated classes | [Segmented/ClumpBasics.lean](Segmented/ClumpBasics.lean): `angularClump_decomposition` | **Equivalent**. |
| Lemma `lem:localization` | Polynomial vanishing outside an anchor neighborhood | [Segmented/ClumpBounds.lean](Segmented/ClumpBounds.lean): `localizationPolynomial_of_angularClumpStructure` | **Equivalent**. |
| Lemma `lem:freq_quantization` | Quantized integer frequency with phase separation | [Segmented/NeighborFactors.lean](Segmented/NeighborFactors.lean): `frequency_quantization_manuscript` | **Equivalent**. |
| Lemma `lem:neighborset_segmented` | Neighbor-set interpolation polynomial and $L^2$ bound | [Segmented/Interpolation.lean](Segmented/Interpolation.lean): `neighborSetSegmented_polynomial_finiteSet` | **Equivalent**. |

## Organization and conventions

| Modules | Contents |
| --- | --- |
| [Basic.lean](Basic.lean), [Matrices.lean](Matrices.lean), [MatrixFacts.lean](MatrixFacts.lean) | Atomic measures, Fourier observations, GHM/GTM definitions, factorizations, and matrix estimates |
| [UniformDefinitions.lean](UniformDefinitions.lean), [UniformInterpolation.lean](UniformInterpolation.lean), [UniformCentering.lean](UniformCentering.lean), [UniformVandermonde.lean](UniformVandermonde.lean), [UniformThreshold.lean](UniformThreshold.lean), [Uniform.lean](Uniform.lean) | Contiguous-grid interpolation, frequency centering, singular-value bounds, and number detection |
| [Segmented/](Segmented/), [WellSeparatedSegmented.lean](WellSeparatedSegmented.lean) | Clump geometry, segmented polynomials, interpolation, and segmented-grid estimates |
| [RandomMatrixBounds.lean](RandomMatrixBounds.lean), [Random.lean](Random.lean), [RandSamp/](../RandSamp/) | Fixed realized random-frequency draws and nonuniform Vandermonde bounds |
| [MUSICPerturbation.lean](MUSICPerturbation.lean), [MUSIC.lean](MUSIC.lean), [SegmentedMUSICGrowth.lean](SegmentedMUSICGrowth.lean), [SegmentedMUSICLocation.lean](SegmentedMUSICLocation.lean), [RandomCubeMUSIC.lean](RandomCubeMUSIC.lean), [RandomClumpModel.lean](RandomClumpModel.lean), [RandomClumpVandermonde.lean](RandomClumpVandermonde.lean), [RandomCubeNumberDetection.lean](RandomCubeNumberDetection.lean), [RandomClumpMUSIC.lean](RandomClumpMUSIC.lean) | MUSIC noise spaces, perturbation stability, segmented-grid residual growth and location error, and well-separated and multi-clump fixed-support random-cube sampling |
| [MUSICPeakSelection.lean](MUSICPeakSelection.lean), [MUSICPeakReciprocal.lean](MUSICPeakReciprocal.lean), [SegmentedMUSICPeaks.lean](SegmentedMUSICPeaks.lean), [SegmentedMUSICPeakCurvature.lean](SegmentedMUSICPeakCurvature.lean), [SegmentedMUSICPeakFinal.lean](SegmentedMUSICPeakFinal.lean) | Continuous top-`n` local-peak selection and the complete segmented specialization |
| [MUSICPeakRegularity.lean](MUSICPeakRegularity.lean), [MUSICPeakGrowth.lean](MUSICPeakGrowth.lean), [MUSICPeakFourierDerivativeNorm.lean](MUSICPeakFourierDerivativeNorm.lean), [MUSICPeakFourierLineVector.lean](MUSICPeakFourierLineVector.lean), [MUSICPeakSegmentedFrequency.lean](MUSICPeakSegmentedFrequency.lean), [MUSICPeakQuadraticBounds.lean](MUSICPeakQuadraticBounds.lean), [MUSICPeakProjectionBridge.lean](MUSICPeakProjectionBridge.lean), [MUSICPeakStrictConvex.lean](MUSICPeakStrictConvex.lean) | Squared-residual regularity, source growth, Fourier vector derivatives and norm bounds, projection quadratic bounds, and the source-ball strict-convexity criterion |
| [MUSICPeakCurvatureIdentity.lean](MUSICPeakCurvatureIdentity.lean), [MUSICPeakFourierCurvature.lean](MUSICPeakFourierCurvature.lean), [MUSICPeakSegmentedRadialLoss.lean](MUSICPeakSegmentedRadialLoss.lean), [MUSICPeakProjectorCurvatureLoss.lean](MUSICPeakProjectorCurvatureLoss.lean), [MUSICPeakFourierProjectorCurvature.lean](MUSICPeakFourierProjectorCurvature.lean), [SegmentedMUSICPeakSignalGap.lean](SegmentedMUSICPeakSignalGap.lean), [SegmentedMUSICPeakProjectorCurvature.lean](SegmentedMUSICPeakProjectorCurvature.lean) | Concrete radial and projector curvature-loss estimates for segmented Fourier MUSIC |
| [CRLLowerBound.lean](CRLLowerBound.lean), [CRL.lean](CRL.lean) | CRL bounds, including the two-sided and positive-amplitude results corresponding to the manuscript's equation labels |

The equation-only CRL bounds are in [CRL.lean](CRL.lean) and
[CRLLowerBound.lean](CRLLowerBound.lean). The latter proves the constant-$2$
lower bound by a direct finite-difference construction.

## Multi-clump random-GHM MUSIC

The exact periodic coordinate, one-norm and infinity-norm metric equalities
are proved in [RandomClumpModel.lean](RandomClumpModel.lean). Atomic-measure
injectivity on $(-\pi,\pi]^d$ proves torus distinctness, and the chosen
nonempty clump partition preserves its attained maximum and every clump
cardinality. The global periodic $\Delta_1$ supplies the lower intraclump
spacing required by the sampling theorem.

The clump predicate is exactly the manuscript's
$(A,\infty,\tau,\eta,n^\star)$ model. Lean's `nStar` is $n^\star$;
$\eta$ is the between-clump separation and $\epsilon$ is the failure
probability. The geometry constants $c_0,C_0$ depend only on $d,n,n^\star$
and are chosen before bandwidth, nodes and probability parameters. Require
$L\ge C_0$, $\tau\le c_0/L$, $\eta\ge C_0/L$, and $2L\le\Omega$.
The lower constant depends only on $d,n^\star$:

$$
C(d,n^\star)=\frac{3}{\sqrt{10n^\star}\,2^{n^\star-1}\sqrt{2^d}
(3n^\star d)^{n^\star-1}}.
$$

For one uniform sample of $m$ rows, the manuscript-facing theorem exposes
only the unnormalized Vandermonde lower bound

$$
\sigma_{\min}(\mathcal V_{\mathcal W}(\mathcal X))
\ge\sqrt{m(1-\rho)}\,C(d,n^\star)(L\Delta_1)^{n^\star-1}
$$

with probability at least $1-\epsilon$, under

$$
m\ge\frac{3}{\rho^2}
\left(\sum_a n_a^{2d}\right)\log\frac n\epsilon.
$$

The sampling coefficient is $3$ in every dimension $d\ge1$.
The dimension dependence remains in $\sum_a n_a^{2d}$.
The manuscript-facing rate hypotheses also use the literal number $3$.

The public geometry thresholds are explicit finite formulas in
[QuantitativeClumpSectionBounds.lean](../General/Fourier/QuantitativeClumpSectionBounds.lean).
They separately bound the clump width, the bandwidth and the interclump
separation. The separation coefficient is the minimum of the pairwise
polynomial-variation bound and the global size-weighted bound. The latter
uses $A-1\le n-n^\star$, $\sum_a n_a^2\le nn^\star$ and
$\sum_a n_a^4\le n(n^\star)^3$. All three public results use the same
specified constants. The lower-only sampler
`multidimensionalMultiClump_lower_sampling_explicit` retains the spectral
coefficient $C(d,n^\star)$ and the sampling coefficient $3$. Its energy
estimate retains $3/4$ of the clump energy sum, with coordinate row factor
$1+1/(16d)$; the refined interpolation estimate at $L\ge16n^\star$
compensates for this energy factor. The exact formulas are shared with
`main.tex`; the bandwidth threshold is independent of the separation
threshold.

The two independent samples for MUSIC use $n<M_1$, $n\le M_2$,
$M_i\le(L+1)^d$, and the same rate with $\log(2n/\epsilon)$.
When

$$
2\sigma<a_{\min}(1-\rho)C(d,n^\star)^2
(L\Delta_1)^{2n^\star-2},
$$

the probability of the uniform correlation bound is at least $1-\epsilon$:

$$
\|R_\sigma-R\|_\infty\le
\frac{2\sigma}{a_{\min}(1-\rho)C(d,n^\star)^2
(L\Delta_1)^{2n^\star-2}}.
$$

The same factor event gives exactly $n$ measured singular values above
$\sigma\sqrt{M_1M_2}$, proving the manuscript's number-detection
consequence. The source tuple is fixed, and one projector event controls
all search points. No source-dependent Gram or leverage assumption,
comparable-spacing premise, or upper singular-value conclusion is exposed.
[RandomClumpMUSICAudit.lean](RandomClumpMUSICAudit.lean) audits the public
lower bound, number detection, correlation result and their model,
normalization, noise and probability conversions.

## Verification

The NumDetect results and their dependencies have no admissions or project axioms. The [external registry](../External/README.md) contains source attribution only; `src/External` contains no Lean files. From the repository root:

```sh
python3 .github/ci/setup_mathlib.py --verify
lake build
python3 .github/ci/check.py
```

The final command checks every source module and audits declaration bodies for
`sorryAx` and project-defined axioms. See the [repository guide](../../README.md)
and [CI guide](../../.github/ci/README.md).
