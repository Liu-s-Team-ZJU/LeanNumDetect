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
| Theorem `thm:random-cube-multiclump` | Unnormalized multi-clump random cube Vandermonde minimum singular-value lower bound | [RandomClumpVandermonde.lean](RandomClumpVandermonde.lean): `positiveCubeClumpVandermonde_lower_highProbability` | **Equivalent**; exact $(A,\infty,\tau,\eta,n^\star)$ geometry, literal sampling coefficient $3$, $C(d,n,n^\star,\beta)$ independent of bandwidth and spacing, and $\sqrt{m(1-\rho)}$ on the right. Li geometry and all sampling prerequisites are proved without additional leverage or thickness assumptions. |
| Paragraph following `thm:random-cube-multiclump` | Random-GHM number detection under multi-clump geometry | [RandomClumpMUSIC.lean](RandomClumpMUSIC.lean): `positiveCubeClumpGHM_signalSingularValue_lower_highProbability`, `positiveCubeClumpGHM_numberDetection_highProbability` | **Equivalent**; proves the strict signal and tail thresholds and exactly $n$ values above $\sigma\sqrt{M_1M_2}$. |
| Theorem `thm:resolutionrandghmnumber1` | Random-GHM noise and signal thresholds | [Random.lean](Random.lean): `realizedRandomGHM_tail_singularValue_lt` (noise), `randomGHM_signalThreshold_of_separation` (signal) | **Equivalent**. |
| Theorem `thm:nonuniform_vdm_scaling` | Nonuniform one-dimensional Vandermonde scaling | [RandSamp/NonuniformVandermonde.lean](../RandSamp/NonuniformVandermonde.lean): `RandSamp.nonuniformVandermonde_minimumSingularValue` | **Equivalent**. |
| Lemma `lem:stability_ghm_music` | General GHM-MUSIC perturbation | [MUSIC.lean](MUSIC.lean): `ghmMUSIC_correlation_stability` | **Equivalent**. |
| Corollary `cor:stability_multidim_segmented` | Segmented-grid MUSIC perturbation | [MUSIC.lean](MUSIC.lean): `segmentedMUSIC_correlation_stability` | **Equivalent**. |
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
| Lemma `lem:cube-vandermonde-translations` (Appendix C) | Translation identities and bandwidth-independent operator bound for normalized cube rows | [General/Fourier/CubeTranslationBounds.lean](../General/Fourier/CubeTranslationBounds.lean): `LeanNumDetect.CubeShiftBounds.integerIsotropicCubeRootRow_translation`, `LeanNumDetect.CubeShiftBounds.cubeTranslation_neg_mul`, `LeanNumDetect.CubeShiftBounds.cubeTranslation_norm_le` | **Equivalent after Gram whitening and row normalization**; the bound is $K=2^{4dn^2}$ for every integer coordinate displacement of magnitude at most $L$. |
| Lemma `lem:cube-row-selection` (Appendix C) | Quantitative selection of independent rows within the cube | [General/Fourier/CubeFrameThickness.lean](../General/Fourier/CubeFrameThickness.lean): `LeanNumDetect.CubeFrameThickness.cubeFrameRow_connectedBasis` | **Equivalent after Gram whitening and row normalization**; the coordinate sum is at most $(n-1)Q$ and the coefficient recursion is $\alpha_0=K^{-1}$, $\alpha_r=\alpha_{r-1}^2/(3KM^2)$ with $M=K\sqrt n$. |

The well-separated random bounds and the MUSIC location and peak-selection
modules remain independent fully proved results. They are not active
statements in the current manuscript and are omitted from this correspondence
table.

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

[RandomClumpModel.lean](RandomClumpModel.lean) identifies the manuscript's
periodic metrics and preserves its exact nonempty clump partition and sizes.
[LiCubeClumpBounds.lean](LiCubeClumpBounds.lean) proves the deterministic
full-cube interpolation bound rather than importing it as an axiom. Its
`LiCubeClumpGeometry` uses precisely

$$
L\text{ even},\quad L\ge8n,\quad
\beta>\frac1{2\log2},\quad
\frac{8\pi\beta d n^\star}{L}\le\tau\le\frac\pi{2d},\quad
\Delta_1\le\frac{4\pi n^\star}{L},
$$

together with the original $(A,\infty,\tau,\eta,n^\star)$ clump predicate,
including $\tau\le\eta$. The parameter $\tau$ is a selectable diameter
upper bound. Li's published cube corollary is stated for $d\ge2$; the
formalization also proves the interval case in $d=1$ from the same
localization and interpolation constructions.

The actual Fourier frame thickness is proved in
[CubeFrameThickness.lean](../General/Fourier/CubeFrameThickness.lean).
[CubeWeakLowerSampling.lean](../RandSamp/CubeWeakLowerSampling.lean)
constructs auxiliary weights and proves the unchanged uniform subset
sampling event. These weights are internal to the proof; neither the
sampling distribution nor either algorithm is modified. The exact public
coefficient is

$$
C(d,n,n^\star,\beta)=\sqrt{\delta(d,n)/2}\,
\frac{(2-e^{1/(2\beta)})^{n^\star/2}}
{\sqrt n(\sqrt2)^{n^\star-1}(\sqrt{3n^\star})^d
(4\pi n^\star)^{n^\star-1}}.
$$

Here $K=2^{4dn^2}$, $M=K\sqrt n$,
$\alpha_0=1/K$, $\alpha_{r+1}=\alpha_r^2/(3KM^2)$,
$\theta=\alpha_{n-1}/(2K)$, and

$$
\delta(d,n)=\exp[-5n-6n\log(12n/(5\theta^2))].
$$

Thus $C>0$ and is independent of $L,\Delta_1,\rho,\epsilon$.
Its dependence on $n$ is conservative. The manuscript-facing node-only
result in [RandomClumpVandermonde.lean](RandomClumpVandermonde.lean) proves

$$
\sigma_{\min}(\mathcal V_{\mathcal W}(\mathcal X))
\ge\sqrt{m(1-\rho)}\,C(d,n,n^\star,\beta)(L\Delta_1)^{n^\star-1}
$$

with probability at least $1-\epsilon$, under

$$
1\le m\le(L+1)^d,\qquad
m\ge\frac3{\rho^2}\left(\sum_a n_a^{2d}\right)\log\frac n\epsilon.
$$

The manuscript places the proof and its translation and row-selection lemmas
in Appendix C; the corresponding Lean declarations retain their stable names.

No leverage, thickness, arrangement, comparable-spacing, or norming
hypothesis appears in this theorem. Unit amplitudes are internal witnesses
for its node-only statement. There is no upper singular-value conclusion.

The two independent uniform samples for MUSIC use $n\le M_1,M_2\le(L+1)^d$
and the same rate with $\log(2n/\epsilon)$. This rate implies $n<M_i$;
the deterministic noise-space proof derives the strict row count internally.
[RandomClumpMUSIC.lean](RandomClumpMUSIC.lean) proves the noiseless GHM lower
bound and, when

$$
2\sigma<m_{\min}(1-\rho)C(d,n,n^\star,\beta)^2
(L\Delta_1)^{2n^\star-2},
$$

the uniform correlation bound with probability at least $1-\epsilon$:

$$
\|R_\sigma-R\|_\infty\le
\frac{2\sigma}{m_{\min}(1-\rho)C(d,n,n^\star,\beta)^2
(L\Delta_1)^{2n^\star-2}}.
$$

The same factor event proves exactly $n$ measured singular values above
$\sigma\sqrt{M_1M_2}$. The source tuple is fixed; the noise need not be
independent of the sample. No location-distance conclusion is asserted.
[RandomClumpMUSICAudit.lean](RandomClumpMUSICAudit.lean) audits the geometry,
weight construction, unchanged sampling distribution, normalization,
noise, correlation and number-detection chain.

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
