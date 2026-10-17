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
| Definition `def:generalized-hankel-toeplitz` | Generalized Hankel and Toeplitz matrices | [Preliminaries/Matrices.lean](Preliminaries/Matrices.lean): `generalizedHankelOn`, `generalizedToeplitzOn` | **Equivalent**. |
| Definition `generalized vandermonde` | Generalized Vandermonde matrix and steering vector | [Preliminaries/Matrices.lean](Preliminaries/Matrices.lean): `generalizedVandermonde`, `steeringVector` | **Equivalent**. |
| Definition `def:generalized-vandermonde-decomposition` | Hankel/Toeplitz type Vandermonde decomposition | [Preliminaries/Matrices.lean](Preliminaries/Matrices.lean): `AdmitsGeneralizedVandermondeDecomposition` | **Equivalent**. |
| Definition `def:sigma-admissible-measure` | $\sigma$-admissible and positive $\sigma$-admissible measures | [Preliminaries/Basic.lean](Preliminaries/Basic.lean): `IsAdmissible`, `IsPositiveAdmissible` | **Equivalent**. |
| Definition `def:crl-number` | General and positive number-detection CRL | [CRL/Definitions.lean](CRL/Definitions.lean): `numberDetectionCRL`, `positiveNumberDetectionCRL`; [CRL/Bounds.lean](CRL/Bounds.lean): `numberDetectionCRL_isSmallest`, `positiveNumberDetectionCRL_isSmallest` | **Equivalent**. |
| Theorem `thm:li-resolution` | Exclusion of admissible measures with fewer supports | [Uniform/NumberDetection.lean](Uniform/NumberDetection.lean): `noAdmissibleMeasureWithFewerSupports` | **Equivalent**. |
| Lemma `lem:uniform-Vandermonde` | Contiguous-grid minimum singular value | [Uniform/Vandermonde.lean](Uniform/Vandermonde.lean): `uniformVandermonde_minimumSingularValue` | **Equivalent**. |
| Theorem `liuthm5.1v2` | Contiguous-grid singular-value threshold | [Uniform/NumberDetection.lean](Uniform/NumberDetection.lean): `uniformGHM_singularValueThreshold` | **Equivalent**. |
| Definition `defi:metric_separation` | Periodic distance and minimum separation | [Preliminaries/Basic.lean](Preliminaries/Basic.lean): `periodicDistance`, `extendedPeriodicMinimumSeparation` | **Equivalent**. |
| Definition `defi:local_sparsity` | Local neighborhood and sparsity | [Preliminaries/Basic.lean](Preliminaries/Basic.lean): `localNeighborhood`, `localSparsity` | **Equivalent**. |
| Definition `defi:high_dim_clumps` | Multidimensional clump structure | [Preliminaries/Basic.lean](Preliminaries/Basic.lean): `IsAngularClumpStructure` | **Equivalent**. |
| Theorem `thm:segmented-vandermonde` | Segmented-grid minimum singular value | [Segmented/Main.lean](Segmented/Main.lean): `segmentedVandermonde_minimumSingularValue` | **Equivalent**. |
| Theorem `thm:segmented_threshold` | Segmented-grid singular-value threshold | [Segmented/Main.lean](Segmented/Main.lean): `segmentedGHM_singularValueThreshold` | **Equivalent**. |
| Theorem `thm:random-cube-multiclump` | Unnormalized multi-clump random cube Vandermonde minimum singular-value lower bound | [Random/ClumpVandermonde.lean](Random/ClumpVandermonde.lean): `positiveCubeClumpVandermonde_lower_highProbability` | **Equivalent**. |
| Corollary `cor:random-ghm-number-detection-multiclump` | Random-GHM number detection under multi-clump geometry | [Random/ClumpMUSIC.lean](Random/ClumpMUSIC.lean): `positiveCubeClumpGHM_numberDetection_highProbability` | **Equivalent**. |
| Lemma `lem:stability_ghm_music` | General GHM-MUSIC perturbation | [MUSIC/Stability.lean](MUSIC/Stability.lean): `ghmMUSIC_correlation_stability` | **Equivalent**. |
| Corollary `cor:stability_multidim_segmented` | Segmented-grid MUSIC perturbation | [Segmented/MUSICStability.lean](Segmented/MUSICStability.lean): `segmentedMUSIC_correlation_stability` | **Equivalent**. |
| Corollary `cor:random-ghm-music-multiclump` | Fixed-source high-probability random-GHM MUSIC correlation stability under the original multi-clump geometry | [Random/ClumpMUSIC.lean](Random/ClumpMUSIC.lean): `positiveCubeClumpMUSIC_correlation_stability_highProbability` | **Equivalent**. |
| Lemma `lem:nonnegative_to_centered` | Unitary conversion from nonnegative to centered frequency grid | [Uniform/Centering.lean](Uniform/Centering.lean): `uniformVandermonde_centering` | **Equivalent**. |
| Lemma `lem2:uniform-Vandermonde` | Centered interpolation polynomial with a neighbor-product bound | [Uniform/Interpolation.lean](Uniform/Interpolation.lean): `CenteredPacket.exists_centeredUnitTorusInterpolation` | **Equivalent**. |
| Definition `defi:high_dim_uniform_poly` | Multivariate segmented trigonometric polynomials | [Segmented/Polynomial.lean](Segmented/Polynomial.lean): `SegmentedPolynomial`, `SegmentedPolynomial.eval` | **Equivalent**. |
| Definition `defi:high_dim_lagrange` | Lagrange interpolant family | [Segmented/Polynomial.lean](Segmented/Polynomial.lean): `SegmentedPolynomial.IsLagrangeFamily` | **Equivalent**. |
| Lemma `lem:minsvd_bound_by_lagInterp_high_dim` | Interpolants bound inverse minimum singular value | [Segmented/Interpolation.lean](Segmented/Interpolation.lean): `segmentedPolynomial_lagrange_minimumSingularValue` | **Equivalent**. |
| Lemma `lem:interpolation_via_svd` | Full-rank interpolation and $L^2/L^\infty$ bounds | [Segmented/Interpolation.lean](Segmented/Interpolation.lean): `segmentedPolynomial_interpolation_of_fullColumnRank` | **Equivalent**. |
| Theorem `thm:well_separated_segmented` | Two-sided singular-value estimate for separated nodes | [Segmented/WellSeparated.lean](Segmented/WellSeparated.lean): `wellSeparatedSegmented_singularValue_bounds` | **Equivalent**. |
| Proposition `prop:decomposition` | Partition of a subset into separated classes | [Segmented/ClumpBasics.lean](Segmented/ClumpBasics.lean): `angularClump_decomposition` | **Equivalent**. |
| Lemma `lem:localization` | Polynomial vanishing outside an anchor neighborhood | [Segmented/ClumpBounds.lean](Segmented/ClumpBounds.lean): `localizationPolynomial_of_angularClumpStructure` | **Equivalent**. |
| Lemma `lem:freq_quantization` | Quantized integer frequency with phase separation | [Segmented/NeighborFactors.lean](Segmented/NeighborFactors.lean): `frequency_quantization_manuscript` | **Equivalent**. |
| Lemma `lem:neighborset_segmented` | Neighbor-set interpolation polynomial and $L^2$ bound | [Segmented/Interpolation.lean](Segmented/Interpolation.lean): `neighborSetSegmented_polynomial_finiteSet` | **Equivalent**. |
| Lemma `lem:cube-vandermonde-translations` (Appendix C) | Normalized Fourier rows, integer translations, inverses, and operator norm bound | [Random/NormalizedRows.lean](Random/NormalizedRows.lean): `cubeNormalizedFourier_translations` | **Equivalent**. |
| Lemma `lem:cube-row-selection` (Appendix C) | Independent rows with the coordinate maximum and coefficient bounds | [Random/NormalizedRows.lean](Random/NormalizedRows.lean): `cubeNormalizedFourierRow_connectedBasis` | **Equivalent**. |
| Lemma `lem:cube-logdet-mean` (Appendix C) | Logarithmic determinant average for the normalized Fourier cube | [Random/LogDetMean.lean](Random/LogDetMean.lean): `cubeNormalizedFourierRow_logDetMean_lower` | **Equivalent**. |
| Lemma `lem:chernoff-without-replacement` (Appendix C) | Matrix Chernoff lower tail for the minimum eigenvalue of a uniform sample average | [General/Probability/MatrixChernoff.lean](../General/Probability/MatrixChernoff.lean): `LeanNumDetect.FiniteMatrixSampling.matrixChernoff_sampleMean_minimumEigenvalue_lower` | **Equivalent**. |

## Retained earlier results

Import [Retained/Main.lean](Retained/Main.lean) for the following declarations,
which no longer correspond to active statements in `main.tex`. The current random-GHM number-detection corollary uses
uniform random subsets and a probability bound. The earlier results apply to
fixed realized frequency families, with the one-dimensional signal estimate
requiring a sampling-spread condition; the new corollary does not include every
such deterministic family.

| Former manuscript result | Retained Lean declaration |
| --- | --- |
| Theorem `thm:resolutionrandghmnumber1`: noise tail for fixed realized draws and the one-dimensional signal threshold | [Retained/RealizedRandomGHM.lean](Retained/RealizedRandomGHM.lean): `realizedRandomGHM_tail_singularValue_lt`, `randomGHM_signalThreshold_of_separation` |
| Theorem `thm:nonuniform_vdm_scaling`: one-dimensional nonuniform Vandermonde scaling | [RandSamp/NonuniformVandermonde.lean](../RandSamp/NonuniformVandermonde.lean): `RandSamp.nonuniformVandermonde_minimumSingularValue` |
| Order-$n$ sampling spread used by those results | [RandSamp/NonuniformVandermonde.lean](../RandSamp/NonuniformVandermonde.lean): `RandSamp.finiteFamilySamplingSpread` |

The well-separated random bounds and the MUSIC location and peak-selection
modules also remain independent fully proved results. They are not active
statements in the current manuscript.

## Organization and conventions

Only [Main.lean](Main.lean) is a Lean module at the directory root. It imports
current manuscript results. Declaration names and the namespace
`LeanNumDetect.NumDetect` are unchanged by the directory organization.

| Directory | Contents |
| --- | --- |
| [MUSIC/](MUSIC/) | MUSIC definitions, noise spaces, and general GHM perturbation stability |
| [Segmented/](Segmented/) | Segmented GHM definitions, interpolation, Vandermonde singular-value bounds, number detection, and MUSIC stability |
| [Random/](Random/) | Random GHM definitions and multi-clump sampling, number detection, and MUSIC stability; Appendix C interfaces and the proof audit |
| [Uniform/](Uniform/) | Uniform GHM definitions, interpolation, Vandermonde singular-value bounds, and number detection |
| [Preliminaries/](Preliminaries/) | Atomic measures, Fourier observations, common GHM/GTM/VDM objects, periodic geometry, and general matrix estimates |
| [Retained/](Retained/) | Earlier realized-frequency and separated random results, MUSIC location and peak-selection results, and their supporting lemmas |
| [CRL/](CRL/) | Computational resolution limit definitions, upper and lower bounds, feasibility, and attainment |

The active modules do not import `Retained`. Its optional aggregate import is
[Retained/Main.lean](Retained/Main.lean); each earlier theorem also remains
available from its own module.

The equation-only CRL bounds are in [CRL/Bounds.lean](CRL/Bounds.lean) and
[CRL/LowerBound.lean](CRL/LowerBound.lean). The latter proves the constant-$2$
lower bound by a direct finite-difference construction.

## Multi-clump random-GHM number detection and MUSIC

[Random/ClumpModel.lean](Random/ClumpModel.lean) identifies the manuscript's
periodic metrics and preserves its exact nonempty clump partition and sizes.
[Random/CubeClumpBounds.lean](Random/CubeClumpBounds.lean) specializes the proved
deterministic full-cube interpolation bound to the fixed numerical frame
constant. Its `CubeClumpGeometry` uses precisely

$$
L\text{ even},\quad L\ge8n,\quad
\frac{8\pi d n^\star}{L}\le\tau\le\eta,\quad
\tau\le\frac\pi{2d},\quad
\Delta_1\le\frac{4\pi n^\star}{L},
$$

together with the original $(A,\infty,\tau,\eta,n^\star)$ clump predicate.
The inequality $\tau\le\eta$ is a field of that predicate. The parameter
$\tau$ is a selectable diameter
upper bound. Li's published cube corollary is stated for $d\ge2$; the
formalization also proves the interval case in $d=1$ from the same
localization and interpolation constructions. The general frame-parameter
proof remains in [CubeClumpBounds.lean](../General/Fourier/CubeClumpBounds.lean)
for other callers; the manuscript interfaces expose no auxiliary parameter
or admissibility hypothesis.

The Appendix C interfaces in [Random/NormalizedRows.lean](Random/NormalizedRows.lean)
and [Random/LogDetMean.lean](Random/LogDetMean.lean) use the manuscript's definitions
of $\mathbf G$, $\mathbf f$, and $\mathbf T$. Their hypotheses are the angular
node domain, positive dimensions, $L\ge2n$, and full column rank of the original
Fourier matrix. The logarithmic determinant estimate is
`cubeNormalizedFourierRow_logDetMean_lower`, proved from
`cubeFrameRow_logDetMean_lower` in
[CubeFrameLogDet.lean](../General/Fourier/CubeFrameLogDet.lean) and the Hadamard
estimate in [FrameLogDetMean.lean](../General/MatrixAnalysis/FrameLogDetMean.lean).
The Chernoff interface `matrixChernoff_sampleMean_minimumEigenvalue_lower` in
[MatrixChernoff.lean](../General/Probability/MatrixChernoff.lean) states the
sample-average minimum-eigenvalue event and the manuscript's exact exponential
bound. The required coordinate and spectral identities are proved internally.
[CubeWeakLowerSampling.lean](../RandSamp/CubeWeakLowerSampling.lean)
constructs auxiliary weights and proves the unchanged uniform subset
sampling event. These weights are internal to the proof; neither the
sampling distribution nor either algorithm is modified. The exact public
coefficient is

$$
C(d,n,n^\star)=\sqrt{\delta(d,n)/2}\,
\frac{(2-e^{1/2})^{n^\star/2}}
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
result in [Random/ClumpVandermonde.lean](Random/ClumpVandermonde.lean) proves

$$
\sigma_{\min}(\mathcal V_{\mathcal W}(\mathcal X))
\ge\sqrt{m(1-\rho)}\,C(d,n,n^\star)(L\Delta_1)^{n^\star-1}
$$

with probability at least $1-\epsilon$, under

$$
1\le m\le(L+1)^d,\qquad
m\ge\frac{3n}{\rho^2}\log\frac n\epsilon.
$$

The smooth potential uses this logarithmic average directly, without
subspace threshold counting or layer integration. The stationary covariance
has minimum eigenvalue at least $\delta$ through a direct eigenvalue bound.
Each normalized weighted rank-one row has norm at most $12n/5\le(5/2)n$,
so the sample count is proportional to the total node count $n$.

Standalone subspace-thickness, capped-iteration, and smooth-thickness results
remain available in the [Fourier](../General/Fourier/README.md),
[matrix-analysis](../General/MatrixAnalysis/README.md), and
[probability](../General/Probability/README.md) libraries. The current
manuscript-facing proof retains the direct logarithmic-average route.
[Random/ClumpAudit.lean](Random/ClumpAudit.lean) checks both the reusable alternative results and the
actual dependencies of the public theorem.


The manuscript places the proof and its translation and row-selection lemmas
in Appendix C; the corresponding Lean declarations retain their stable names.

No leverage, thickness, arrangement, comparable-spacing, or norming
hypothesis appears in this theorem. Unit amplitudes are internal witnesses
for its node-only statement. There is no upper singular-value conclusion.

The two independent uniform samples for number detection and MUSIC use
$n\le M_1,M_2\le(L+1)^d$ and the rate
$M_i\ge3n\rho^{-2}\log(2n/\epsilon)$. Applying the random Vandermonde theorem
to each factor with failure probability $\epsilon/2$ gives a common event of
probability at least $1-\epsilon$. The noiseless GHM bound on this event is
proved by `positiveCubeClumpGHM_signalSingularValue_lower_highProbability` in
[Random/ClumpMUSIC.lean](Random/ClumpMUSIC.lean):

$$
\sigma_n(\mathbf{GH}_0)\ge
m_{\min}\sqrt{M_1M_2}(1-\rho)C(d,n,n^\star)^2
(L\Delta_1)^{2n^\star-2}.
$$

The rate implies $n<M_i$; the deterministic noise-space proof derives this
strict row count internally. The measurement assumptions are $2L\le\Omega$
and $|W(\boldsymbol\omega)|<\sigma$ throughout the frequency band. When

$$
2\sigma<m_{\min}(1-\rho)C(d,n,n^\star)^2
(L\Delta_1)^{2n^\star-2},
$$

the public declaration `positiveCubeClumpGHM_numberDetection_highProbability`
proves the new corollary `cor:random-ghm-number-detection-multiclump`:

$$
\sigma_n(\mathbf{GH})>\sigma\sqrt{M_1M_2},\qquad
\sigma_j(\mathbf{GH})<\sigma\sqrt{M_1M_2}
\quad(n<j\le\min\{M_1,M_2\}),
$$

with probability at least $1-\epsilon$. Exactly $n$ singular values exceed
the algorithm's threshold. The tail estimate follows from the measurement
bound for every sample; the common factor event supplies the signal estimate.

Under the same assumptions,
`positiveCubeClumpMUSIC_correlation_stability_highProbability` proves the
corollary `cor:random-ghm-music-multiclump`, with probability at least
$1-\epsilon$:

$$
\|R_\sigma-R\|_\infty\le
\frac{2\sigma}{m_{\min}(1-\rho)C(d,n,n^\star)^2
(L\Delta_1)^{2n^\star-2}}.
$$

Both public declarations use the same factor event. The source tuple is
fixed; the noise need not be
independent of the sample. No location-distance conclusion is asserted.
[Random/ClumpAudit.lean](Random/ClumpAudit.lean) audits the geometry,
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
