# MultiTuran

This directory formalizes selected results of the MultiTuran manuscript, including complete proofs of `lem:multidim-turan` and `lem:sv-md-array`, together with both multi-clump supplements and the definitions and estimates used by their proofs. The correspondence tables below record the covered cases and statements that are not yet formalized. Import [MultiTuran.Main](Main.lean) for the convex-body Turán theorem and the main-text single-clump interface. Import [MultiTuran.MultiClump.Results](MultiClump/Results.lean) for the Riemann-condition multi-clump results, or [MultiTuran.ConsecutiveWindow.Results](ConsecutiveWindow/Results.lean) for the consecutive-window results. The [Riemann guide](MultiClump/README.md) and [consecutive-window guide](ConsecutiveWindow/README.md) give their respective models, exact coefficients, and proof correspondence.

- `exponentialSum_convexBody_supNorm_le` is the convex-body Turán estimate.
  `exponentialSum_convexBody_eLpNorm_top_le` gives the literal essential
  $L^\infty$ formulation, including arbitrary null exceptional subsets.
- `segmentedArray_minimumSingularValue_lower` displays the exact coefficient
  in `eq:sv-md-array`. Its only hypotheses are the article's open-cube
  localization after a common translation, aperture, block condition and
  $n\ge4$.
- `segmentedArrayLowerBound_le_minimumSingularValue` is the same final theorem
  using the named coefficient.

The Turán constant is the explicit positive absolute number
`multidimensionalTuranConstant`, independent of dimension, term count and
frequencies. The sufficient discretization constant in the main-text single-clump theorem is $80d4^d$. No norming,
derivative, energy lower bound or Turán comparison is an extra hypothesis of
the final theorem. There are no admitted proofs or project axioms in this
development. Fully proved results are not registered in `External`.

## Organization and public interfaces

Only [Main.lean](Main.lean) and this README are files at the directory root. `Main.lean` imports the Turán and main-text single-clump results. The multi-clump public interfaces are [MultiClump/Results.lean](MultiClump/Results.lean) and [ConsecutiveWindow/Results.lean](ConsecutiveWindow/Results.lean); import their respective modules explicitly. Supporting modules are grouped by their mathematical role, as in `NumDetect`. The declaration namespaces are `LeanNumDetect.MultiTuran`, `LeanNumDetect.MultiTuran.MultiClump`, and `LeanNumDetect.MultiTuran.ConsecutiveWindow`.

| Directory | Contents and entry modules |
| --- | --- |
| [Preliminaries/](Preliminaries/) | Torus geometry, segmented grids, volume, energy, translations, interpolation, cardinal packets, polynomial coefficient energy, Riemann convergence, and the single-clump bound formula |
| [Nikolskii/](Nikolskii/) | Exact unit-interval, interval-union, and product-set estimates; entry modules [Nikolskii.lean](Nikolskii/Nikolskii.lean), [NikolskiiIntervals.lean](Nikolskii/NikolskiiIntervals.lean), and [ProductNikolskii.lean](Nikolskii/ProductNikolskii.lean) |
| [Bernstein/](Bernstein/) | Restricted exponential spaces, their integral Hilbert norms, derivative matrices and operators, and squared-modulus variation; entry [Bernstein.lean](Bernstein/Bernstein.lean) |
| [FullAperture/](FullAperture/) | Full-cube interpolation and lower bounds, residue-cube decomposition, and actual full-aperture energy bounds; entry [FullAperture.lean](FullAperture/FullAperture.lean) |
| [Norming/](Norming/) | Measured-cell discretization, product norming, constants, and continuous product restriction; entry modules [ProductNorming.lean](Norming/ProductNorming.lean) and [ProductRestriction.lean](Norming/ProductRestriction.lean) |
| [Turan/](Turan/README.md) | The complete one-dimensional measurable-set Turán proof and its extension to multidimensional convex bodies; entry [Main.lean](Turan/Main.lean) |
| [SingleClump/](SingleClump/) | Scaling, restriction assembly, and the exact single-clump manuscript conclusion; entry [SegmentedArray.lean](SingleClump/SegmentedArray.lean) |
| [MultiClump/](MultiClump/README.md) | Clump geometry, reconstruction, norming, and arbitrary product-row results with row offsets, independent enclosing apertures, and actual largest-clump size; entry [Results.lean](MultiClump/Results.lean) |
| [ConsecutiveWindow/](ConsecutiveWindow/README.md) | Short torus charts, proved sector/Newton interpolation, complete window counting, actual block/product norming, unrestricted-clump cube interpolation, and literal supplement bounds; entry [Results.lean](ConsecutiveWindow/Results.lean), audit [Audit.lean](ConsecutiveWindow/Audit.lean) |
| [Verification/](Verification/) | [Audit.lean](Verification/Audit.lean) checks project admissions, project axioms, and the standard logical-axiom boundary; the multi-clump audit remains [MultiClump/Audit.lean](MultiClump/Audit.lean) |

Module paths describe this file organization; they do not introduce new
components into the declaration namespaces. Within `Turan/`, filenames omit
the repeated `Turan` prefix: for example, import
`MultiTuran.Turan.GeometryTransfer` for [GeometryTransfer.lean](Turan/GeometryTransfer.lean).

## Mathematical objects

`SegmentedGrid d` records all consecutive integer blocks separately in each
coordinate, including the initial block starting at zero. The constructor
`SegmentedGrid.ofConsecutive` accepts the manuscript's adjacent-block order
condition. `length` is the manuscript's $l_{q,m}$, and `thickLength` is
$L_{q,m}=l_{q,m}+1$. `aperture` is exactly the last endpoint plus one.
The row type is the Cartesian product of the actual finite coordinate sets.

`torusCoordinateDistance` is the quotient distance modulo $2\pi$, with a proved
attaining winding integer. `nodeSeparation` and `nodeDiameter` are the actual
minimum separation and maximum diameter in the torus $\ell_\infty$ metric.
`InOpenCube` is the article's literal open cube, defined by
`‖x - center‖ < r`; `InCube` is the closed coordinate bound used in stronger
intermediate results.
`vandermondeMatrix` accepts arbitrary real frequency vectors and uses the
entry $\exp(i\,\gamma_k\cdot y_j)$. Its segmented specialization is
`generalizedVandermonde`.

`continuousEnergy` is the Lebesgue integral of $|P|^2$ over the actual
thickening. `discreteEnergy` is the sum over actual measured rows. Their
definitions do not replace the thickening by an abstract energy variable.
`ContinuousNorming` is precisely the inequality in `ass:norming`.

## Manuscript correspondence

The following table lists all 44 active `definition`, `theorem`, `lemma`,
`corollary`, and `proposition` environments in `MultiTuran/main.tex`, in
manuscript order. Commented statements and equation-only labels are omitted.
Every active statement has a label. Assumptions are not included in this table.

Names without an explicit namespace are in `LeanNumDetect.MultiTuran`.
Declarations in the `MultiTuran` files listed below are exported by
`MultiTuran.Main`. Names beginning `LeanNumDetect.NumDetect` belong to the
neighboring development and require their own imports; none is imported by
`MultiTuran.Main`. “Not formalized” means that no direct declaration for the
complete displayed manuscript statement was found. Mentioned proved
components do not constitute a claim that their missing assembly has already
been formalized.

| TeX type and label | Subject | Direct Lean declaration | Relationship |
| --- | --- | --- | --- |
| Definition `def:generalized-vandermonde` | Generalized Vandermonde matrix and steering vector | [Preliminaries/Geometry.lean](Preliminaries/Geometry.lean): `vandermondeMatrix`; [NumDetect/Preliminaries/Matrices.lean](../NumDetect/Preliminaries/Matrices.lean): `LeanNumDetect.NumDetect.generalizedVandermonde`, `LeanNumDetect.NumDetect.steeringVector` | **Equivalent**. Arbitrary ordered real frequency and node families, with the same angular exponential convention. The `MultiTuran` definition is exported here; the two `NumDetect` definitions require a separate import. |
| Definition `def:generalized-hankel-toeplitz` | Generalized Hankel and Toeplitz matrices on an arbitrary domain | [NumDetect/Preliminaries/Matrices.lean](../NumDetect/Preliminaries/Matrices.lean): `LeanNumDetect.NumDetect.generalizedHankelOn`, `LeanNumDetect.NumDetect.generalizedToeplitzOn` | **Equivalent**, in `NumDetect`; not exported by `MultiTuran.Main`. The domain-containment hypotheses are explicit. |
| Definition `def:generalized-vandermonde-decomposition` | Hankel-type or Toeplitz-type Vandermonde factorization | [NumDetect/Preliminaries/Matrices.lean](../NumDetect/Preliminaries/Matrices.lean): `LeanNumDetect.NumDetect.AdmitsGeneralizedVandermondeDecomposition` | **Equivalent**, in `NumDetect`; not exported by `MultiTuran.Main`. The witnessing reduced atomic measure has distinct nodes and nonzero complex coefficients. |
| Theorem `thm:turan-nazarov-1d` | One-dimensional measurable-set Turán–Nazarov comparison | [Turan/Main.lean](Turan/Main.lean): `oneDimensional_turan_comparison`; [Turan/GeometryTransfer.lean](Turan/GeometryTransfer.lean): `OneDimensionalTuranComparison` specifies the statement | **Equivalent**. Every bounded nondegenerate interval and arbitrary positive-measure measurable subset, with unrestricted real frequencies and an explicit absolute constant. |
| Lemma `lem:nikolskii-unit` | Exact unit-interval $L^2$–$L^\infty$ estimate | [Nikolskii/Nikolskii.lean](Nikolskii/Nikolskii.lean): `exponentialSum_unitSupNorm_le` | **Equivalent**, with the exact coefficient $\pi n/2$. |
| Lemma `lem:nikolskii-interval` | Exact estimate on an arbitrary interval | [Nikolskii/NikolskiiIntervals.lean](Nikolskii/NikolskiiIntervals.lean): `exponentialSum_interval_norm_sq_le`, `exponentialSum_intervalUnion_supNorm_le` specialized to one interval | **Equivalent**, in pointwise squared-energy form and in the one-interval supremum specialization, with coefficient $\pi n/(2\sqrt L)$. |
| Theorem `thm:nikolskii-union` | General $L^q$–$L^p$ estimate on interval unions | [Nikolskii/NikolskiiIntervals.lean](Nikolskii/NikolskiiIntervals.lean): `exponentialSum_intervalUnion_supNorm_le` | **Special case**: only $q=2$, $p=\infty$ is directly formalized; this case also permits overlapping intervals. The general range $0<q<p\le\infty$, $q\le2$ is not formalized. |
| Lemma `lem:zygmund-lower` | Separated-frequency continuous coefficient-energy lower bound | — | **Not formalized**. The full-cube and full-aperture bounds below do not provide this separation-independent absolute $C_{\mathrm Z}/\theta_{\min}$ coefficient. |
| Lemma `lem:bernstein-unit` | General frequency-dependent Bernstein estimate with the $n^{5/2}$ term | [Bernstein/Bernstein.lean](Bernstein/Bernstein.lean): related `exponentialSum_derivative_energy_norm_le`, `exponentialSum_unit_derivative_norm_le` | **Not formalized as stated**. The proved alternative is a frequency-bounded cubic estimate, $20n^3\lVert P\rVert _\infty$ for $\lvert y_j\rvert \le2\pi$, and an energy estimate. These are not the displayed general $C_{\mathrm B}(108n^5+\sum_j y_j^2)^{1/2}$ theorem. |
| Lemma `lem:bernstein-union` | General Bernstein estimate on a union of intervals | [Bernstein/Bernstein.lean](Bernstein/Bernstein.lean): related `exponentialSum_interval_derivative_norm_le` | **Not formalized as stated**. The interval alternative requires $\lvert y_j\rvert \lvert I\rvert \le2\pi$ and gives $20n^3/\lvert I\rvert $; it is not the manuscript's sharper unrestricted union estimate. |
| Corollary `cor:restriction-1d` | Continuous one-dimensional restriction with the exact displayed coefficient | [Turan/Main.lean](Turan/Main.lean) and [Nikolskii/NikolskiiIntervals.lean](Nikolskii/NikolskiiIntervals.lean) provide the Turán and Nikolskii components | **Not formalized as a complete statement**. No declaration assembles this coefficient for the manuscript's one-dimensional $E_\Lambda$. |
| Corollary `cor:continuous-1d` | One-dimensional restriction lower bound in terms of the coefficient norm | — | **Not formalized**. In particular, the continuous Zygmund input and this exact assembly are not present. |
| Proposition `prop:norming-1d` | Half-norming from the one-dimensional block-length condition | [Norming/Discretization.lean](Norming/Discretization.lean) and [Norming/ProductNorming.lean](Norming/ProductNorming.lean) provide related Riemann and product-norming components | **Not formalized as stated**. The article uses the left thickening $[k-1,k]\cap[0,\infty)$ and maximum row $N$; the existing segmented product interfaces use right thickening $[k,k+1]$ and an aperture one past the last row. Their $d=1$ instances are not the literal statement. |
| Theorem `thm:sv-missing-1d` | Minimum singular value for an arbitrary one-dimensional row set | — | **Not formalized**. No direct theorem has this arbitrary-row geometry and the displayed constants $C_2,C_3$. |
| Lemma `lem:multidim-turan` | Multidimensional convex-body Turán estimate | [Turan/Main.lean](Turan/Main.lean): `exponentialSum_convexBody_supNorm_le`, `exponentialSum_convexBody_eLpNorm_top_le`, `exists_multidimensionalTuranConstant` | **Equivalent**. Ordinary supremum and literal essential $L^\infty$ formulations are both proved. The explicit absolute constant is $2C_0$, from the one-dimensional theorem and the ray reduction. |
| Lemma `lem:nikolskii-cube` | $L^2$–$L^\infty$ estimate on an arbitrary finite union of measured unit cubes | [Nikolskii/ProductNikolskii.lean](Nikolskii/ProductNikolskii.lean): related `pi_coordinate_evaluation_bound`, `exponentialSum_product_supNorm_le` | **Not formalized in the stated arbitrary-row generality**. The current public exponential-sum interface is for represented segmented product sets; there is no direct arbitrary finite union-of-cubes declaration. |
| Theorem `thm:nikolskii-multivariate` | General product-set $L^\rho$–$L^p$ estimate | [Nikolskii/ProductNikolskii.lean](Nikolskii/ProductNikolskii.lean): `exponentialSum_product_supNorm_le` | **Special case**: $\rho=2$, $p=\infty$ on represented segmented product sets. The full exponent range and arbitrary real interval products are not directly formalized. |
| Lemma `lem:interp-sv` | Cardinal interpolation bounds the reciprocal least singular value | [Preliminaries/Interpolation.lean](Preliminaries/Interpolation.lean): `reciprocal_minimumSingularValue_le_of_interpolation`, `interpolationCoefficientNorm` | **Stronger**. The theorem works for any finite complex matrix $A$ and coefficient matrix $F$ with $FA=I$, and preserves the exact reciprocal conclusion and coefficient norm. |
| Lemma `lem:nikolskii-product` | Exact long-block product $L^2$–$L^\infty$ estimate | [Nikolskii/ProductNikolskii.lean](Nikolskii/ProductNikolskii.lean): `exponentialSum_product_supNorm_le` | **Special case**. The exact coefficient and actual product integral are proved for `SegmentedGrid` sets, with initial zero blocks and the grid's aperture convention. A direct wrapper for every product-row representation of the earlier general setting is not present. |
| Lemma `lem:no-wrap` | Exact separation scaling under the no-aliasing condition | [Preliminaries/Geometry.lean](Preliminaries/Geometry.lean): `nodeSeparation_mul_nat` | **Equivalent**. Uses the genuine torus $\ell^\infty$ separation and diameter. |
| Theorem `thm:elementary-fullcube` | Elementary dilated full-cube singular-value bound, with and without no wrap | [FullAperture/FullCube.lean](FullAperture/FullCube.lean): `elementary_fullCube_lower`, `elementary_fullCube_no_wrap_lower` | **Equivalent**, with the literal angular coefficient $1/\sqrt n$ and exponent $n-1$. |
| Theorem `thm:decimated-fullcube` | Residue-class improvement by $q^{d/2}$ and the maximum over decimation scales | — | **Not formalized**. The elementary $q=1$ case is proved, but the $q^d$ discrete residue-class decomposition and maximum over $q$ are not exported by a corresponding theorem. |
| Definition `def:admissible-pair` | Full-aperture admissible pair and residue width $h_{M,s}$ | [FullAperture/FullAperture.lean](FullAperture/FullAperture.lean): `FullApertureAdmissible`, `fullApertureWidth` | **Equivalent**. The aperture is encoded by `G`; positivity of $M$ is explicit. Any positive integer aperture box can be represented by a single full block in each coordinate. |
| Theorem `thm:universal-full-aperture` | Full-aperture continuous lower bound with the exact $h_{M,s}^{d/2}$ factor | [FullAperture/FullAperture.lean](FullAperture/FullAperture.lean): `fullAperture_L2_lower`, `fullAperture_L2_lower_full_residue`, `fullApertureWidth_eq_dilation` | **Equivalent**. Although parameterized by `SegmentedGrid`, the conclusion depends only on its aperture box, not on its measured rows; a full-block grid represents every positive integer box. Includes the full-residue $M^{d/2}$ specialization. |
| Corollary `cor:full-aperture-elementary` | Full-aperture elementary lower bound, with and without no wrap | [FullAperture/FullAperture.lean](FullAperture/FullAperture.lean): `fullAperture_elementary_L2_lower`, `fullAperture_elementary_no_wrap_L2_lower`, `fullApertureWidth_eq_dilation` | **Equivalent**, under the same aperture encoding, with all displayed constants and residue-width factors. |
| Theorem `thm:continuous-general` | Continuous restriction lower bound for arbitrary row sets and every admissible pair | [Norming/ProductRestriction.lean](Norming/ProductRestriction.lean): related `apertureL2_le_of_supNorm_restriction`; [FullAperture/FullAperture.lean](FullAperture/FullAperture.lean): full-aperture input | **Not formalized as stated**. The restriction interface is for segmented product sets and takes a supplied supremum comparison; no complete arbitrary-row theorem is present. |
| Corollary `cor:continuous-product` | Improved continuous product restriction with the factor $\rho_L$ | [Norming/ProductRestriction.lean](Norming/ProductRestriction.lean): `apertureL2_le_of_supNorm_restriction`; [Turan/Main.lean](Turan/Main.lean): `aperture_supNorm_turan`; [FullAperture/FullAperture.lean](FullAperture/FullAperture.lean): `fullAperture_L2_lower` | **Not formalized as a complete standalone statement**. The product restriction, unconditional comparison, and aperture lower bound are proved separately; the exact general-pair coefficient is not assembled in a named theorem. |
| Corollary `cor:continuous-elementary` | Arbitrary-row continuous bound using elementary full-cube separation | — | **Not formalized as stated**. The full-aperture elementary bound is proved, but the arbitrary-row continuous restriction assembly is absent. |
| Theorem `thm:main-discrete` | Arbitrary-row discrete singular-value bound under norming | [Preliminaries/Energy.lean](Preliminaries/Energy.lean): related `minimumSingularValue_ge_of_continuousNorming` | **Not formalized in the stated generality**. The proved transfer takes an explicit continuous lower bound and uses a represented segmented product grid; it is not the complete arbitrary-row formula. |
| Corollary `cor:main-product` | Product-row discrete bound for every admissible pair | [Preliminaries/Energy.lean](Preliminaries/Energy.lean): `minimumSingularValue_ge_of_continuousNorming`; [Norming/ProductRestriction.lean](Norming/ProductRestriction.lean): product restriction component | **Not formalized as a complete standalone statement**. The norming-to-spectrum transfer and product restriction components exist; this exact arbitrary-pair formula is not directly exported. |
| Corollary `cor:main-elementary` | Arbitrary-row discrete elementary bound and no-wrap specialization | — | **Not formalized as stated**. The complete arbitrary-row assembly is absent. |
| Corollary `cor:subrayleigh-scaled` | Aperture-scaled arbitrary-row bound under a uniform norming constant | [SingleClump/Scaling.lean](SingleClump/Scaling.lean): related `aperture_quotient_lower`, `aperture_scaled_factors_lower` | **Not formalized as stated**. The floor and half-power arithmetic is proved, but no complete arbitrary-row theorem with general $\eta_0$ is present. |
| Corollary `cor:subrayleigh-scaled-product` | Aperture-scaled product bound under a uniform norming constant | [SingleClump/Scaling.lean](SingleClump/Scaling.lean): `aperture_scaled_factors_lower`; [SingleClump/ScaledRestriction.lean](SingleClump/ScaledRestriction.lean): related `segmentedArrayLowerBound_le_of_supNorm_comparison` | **Not formalized in this generality**. The internal final-theorem assembly fixes half-norming and adds the final localized block hypotheses; it is not the general $\eta_0$ corollary. |
| Proposition `prop:discretization` | Half-norming under the multidimensional block-length threshold | [Norming/ProductNorming.lean](Norming/ProductNorming.lean): `continuousNorming_half_of_blockCondition`, `continuousNorming_half_of_localized_blockCondition`, `discretizationConstant` | **Special case**. The proved public interface uses represented segmented products and the stronger integer-degree condition on $l_*=L_*-1$, whereas this proposition is stated using thickened block length $L_*$. It supplies the same conclusion with the explicit sufficient constant $80d4^d$; it does not directly formalize the full $L_*$ statement. |
| Lemma `lem:sv-1d-array` | One-dimensional distributed-array least singular value | — | **Not formalized**. No direct theorem uses this array model and its exact coefficient; the neighboring `NumDetect` segmented geometry is different. |
| Lemma `lem:signal-1d-array` | One-dimensional noiseless GHM signal singular-value lower bound | [NumDetect/MUSIC/Perturbation.lean](../NumDetect/MUSIC/Perturbation.lean): related `LeanNumDetect.NumDetect.vandermondeFactor_signalSingularValue_lower` | **Not formalized as stated**. A general factor-product component is proved in `NumDetect`, but the required one-dimensional array lower bound and displayed coefficient are not assembled. Not exported by `MultiTuran.Main`. |
| Theorem `thm:threshold-1d` | One-dimensional GHM singular-value threshold for source detection | [NumDetect/Preliminaries/MatrixFacts.lean](../NumDetect/Preliminaries/MatrixFacts.lean): related `LeanNumDetect.NumDetect.matrixSingularValue_three_mul_eq_zero_of_card_le`, `LeanNumDetect.NumDetect.matrixSingularValue_sub_spectralNorm_le_add`, `LeanNumDetect.NumDetect.matrixSingularValue_add_le_add_spectralNorm` | **Not formalized as stated**. General rank and Weyl ingredients are proved, but this array threshold and its explicit separation condition are not. These `NumDetect` components require separate imports. |
| Lemma `lem:sv-md-array` | Exact multidimensional segmented-array least singular-value estimate | [SingleClump/SegmentedArray.lean](SingleClump/SegmentedArray.lean): `segmentedArray_minimumSingularValue_lower`, `segmentedArrayLowerBound_le_minimumSingularValue` | **Equivalent**. The actual open-cube localization after a common translation, $N_{\min}\ge2n$, $n\ge4$, integer block condition on $l_*$, and literal displayed coefficient are preserved. The proof has no extra norming, derivative, energy, or Turán premise. |
| Lemma `lem:signal-md-array` | Exact multidimensional noiseless GHM signal lower bound | [SingleClump/SegmentedArray.lean](SingleClump/SegmentedArray.lean): proved Vandermonde input; [NumDetect/MUSIC/Perturbation.lean](../NumDetect/MUSIC/Perturbation.lean): `LeanNumDetect.NumDetect.vandermondeFactor_signalSingularValue_lower` | **Not formalized as a complete statement**. The numerical Vandermonde bound and general matrix-product theorem exist, but no direct declaration assembles this paper's GHM factorization and displayed coefficient. The latter component is not exported by `MultiTuran.Main`. |
| Theorem `thm:threshold-md` | Multidimensional GHM singular-value threshold and explicit separation condition | [NumDetect/Preliminaries/MatrixFacts.lean](../NumDetect/Preliminaries/MatrixFacts.lean): general rank, entrywise-noise, and Weyl components | **Not formalized as stated**. No direct theorem combines the new arbitrary-block coefficient with this measurement model and threshold. The existing `NumDetect.Segmented` thresholds use a different grid and bound. |
| Proposition `prop:detector-guarantee` | Threshold detector never overestimates and is exact under separation | — | **Not formalized as stated**. No direct implementation or theorem for this manuscript's Algorithm `alg:ghm-svt` was found; general rank and perturbation facts are only components. |
| Lemma `lem:stab-ghm-music` | GHM MUSIC noise-space correlation stability | [NumDetect/MUSIC/Stability.lean](../NumDetect/MUSIC/Stability.lean): `LeanNumDetect.NumDetect.ghmMUSIC_correlation_stability` | **Stronger**, in `NumDetect`; not exported by `MultiTuran.Main`. The theorem allows distinct row and column frequency families and rectangular factors. Taking both families equal gives the square denominator $m_{\min}\sigma_{\min}(V_1)^2$ and the stated $M>n$ case. |
| Corollary `cor:stab-1d` | One-dimensional MUSIC stability with the explicit array coefficient $B_1$ | [NumDetect/MUSIC/Stability.lean](../NumDetect/MUSIC/Stability.lean): general `LeanNumDetect.NumDetect.ghmMUSIC_correlation_stability` | **Not formalized as stated**. The general stability theorem exists, but the one-dimensional array coefficient and noise-budget specialization are not assembled into this corollary. Not exported by `MultiTuran.Main`. |
| Corollary `cor:stab-md` | Multidimensional MUSIC stability with the explicit array coefficient $B_d$ | [SingleClump/SegmentedArray.lean](SingleClump/SegmentedArray.lean): proved $B_d$ input; [NumDetect/MUSIC/Stability.lean](../NumDetect/MUSIC/Stability.lean): `LeanNumDetect.NumDetect.ghmMUSIC_correlation_stability` | **Not formalized as a complete statement**. The array bound and general stability theorem are proved separately, but no direct corollary combines this coefficient, factorization, and $\lvert \Lambda\rvert \sigma$ noise budget. The `NumDetect` component requires its own import. |

## Draft correspondence

The two draft files reuse labels, including `thm:main`, so identify every row by both its file and label. There are 12 active theorem/lemma/proposition statements in `MultiTuranMultiClump.tex` and 6 in `MultiTuranMultiClumpV2.tex`; neither draft declares a `definition` environment. The constants in the Riemann draft's `eq:B-choice` and `eq:eta-choice` are exactly `multiClumpBlockConstant` and `multiClumpNormingConstant` in [MultiClump/BoundFormula](MultiClump/BoundFormula.lean).

Both multi-clump supplements have complete public interfaces. [MultiClump.Results](MultiClump/Results.lean) proves the Riemann draft with its literal $B_d$ condition, displayed Riemann $\eta_0$, and gap at $L_*$. [ConsecutiveWindow.Results](ConsecutiveWindow/Results.lean) proves V2 with $\eta_0=[18n(3n)^{2n}]^{-d}$, block condition $L_{q,\min}\ge n$, gap at $N_{\min}$, and unrestricted within-clump geometry. Their shared final factorization uses the norming coefficient and gap scale of the respective proof. See the [consecutive-window guide](ConsecutiveWindow/README.md) for its complete model and proof interfaces.

### [MultiTuranMultiClump.tex](../../drafts/MultiTuranMultiClump.tex): Riemann version

Unless a row gives another namespace, local declarations are in `LeanNumDetect.MultiTuran.MultiClump`.

| TeX type and label | Subject | Direct Lean declaration | Relationship |
| --- | --- | --- | --- |
| Theorem `thm:main` | Multi-clump lower bound with the literal $B_d$ condition | [MultiClump/ProductResult](MultiClump/ProductResult.lean): `multiClumpProduct_minimumSingularValue_lower`; [MultiClump/GeneralProduct](MultiClump/GeneralProduct.lean): `generalProductArray_minimumSingularValue_lower` | **Equivalent**. Exact Riemann coefficient and hypotheses, including actual largest clump size in the first interface. Product rows are represented by a normalized grid plus an offset, with an independently chosen enclosing box. [MultiClump/RowShift](MultiClump/RowShift.lean): `normalizedProductGrid`, `enclosingBoxGrid`, `mem_normalizedProductGrid_rows`, and `normalizedProductGrid_le_enclosingBoxGrid` bridge the draft's original ordered blocks and box. |
| Lemma `lem:clump-lifts` | Real representatives of each clump and preservation of integer-frequency entries | [MultiClump/ClumpLifts](MultiClump/ClumpLifts.lean): `exists_simultaneous_clump_lifts`, `clump_shortness_of_dimension_bound`; [MultiClump/Lifting](MultiClump/Lifting.lean): `generalizedVandermonde_liftNodes` | **Stronger**. The lift theorem is stronger: it needs $3\tau<2\pi$ rather than the draft's dimensional upper bound. The second declaration derives this premise from the draft. |
| Lemma `lem:separated-interpolation` | Fine-cube interpolation with coefficient mass bounded by the frame constant | [General/Fourier/BartonCubeFrame](../General/Fourier/BartonCubeFrame.lean): `LeanNumDetect.BartonCubeFrame.hasFineCubeFrame_of_translatedCube`; [SegmentedVDM/UniformInterpolation](../SegmentedVDM/UniformInterpolation.lean): `SegmentedVDM.interpolation_coefficients_of_fullColumnRank_coefficientNorms`; [NumDetect/Segmented/ClumpBasics](../NumDetect/Segmented/ClumpBasics.lean): `LeanNumDetect.NumDetect.fineCube_cardinalPolynomial` | **Special case**. Proved by the general frame and minimum-norm interpolation interfaces; no single local declaration repeats the draft's arbitrary unit-data statement. The last declaration directly packages the cardinal-data case used by the anchor construction. The frame threshold $4\pi\beta d/(K+1)$ is weaker than the draft's $4\pi\beta d/K$. |
| Lemma `lem:selector-width` | Feasibility, even bandwidth $K$, and $W\le3L_*/8$ | [MultiClump/BlockFeasibility](MultiClump/BlockFeasibility.lean): `blockCondition_minimumLength_power_lower`, `blockCondition_minimumLength_lower`; [MultiClump/LinearGapParameters](MultiClump/LinearGapParameters.lean): `linearGap_blockCondition_minimumLength_lower`, `linearGapSeparationThreshold_le_pi`, `linearGapSelectorWidthParameter_lower`, `linearGapSelectorWidthParameter_eight_mul_le`, `linearGapSelectorWidthParameter_fits_blocks` | **Equivalent**. Same bandwidth formula and displayed bounds; the feasibility helper even proves $16d(n^\star)^2\le L_*$. |
| Lemma `lem:anchor-localization` | Low-bandwidth clump anchors with $\beta=7/5$ | [MultiClump/Selectors](MultiClump/Selectors.lean): `anchor_selector_of_torus_separated_clumps_beta`; [MultiClump/LinearNorming](MultiClump/LinearNorming.lean): its specialization inside `continuousNorming_of_linear_multiclump_blocks` | **Stronger**. General arbitrary-$\beta$ selector theorem, specialized using the proved bandwidth and frame parameters. It proves interpolation and the actual coefficient mass; the polynomial support is encoded by its type. |
| Lemma `lem:clump-riemann` | Half norming on shortened blocks for every clump | [MultiClump/ClumpRiemann](MultiClump/ClumpRiemann.lean): `continuousNorming_half_of_centered_frequency_bound`; [MultiClump/ClumpSums](MultiClump/ClumpSums.lean): `filtered_clump_norming_half`; [MultiClump/BlockParameters](MultiClump/BlockParameters.lean): `shortenedGrid_riemann_threshold` | **Special case**. The conclusion is proved in squared energy form at the chosen bandwidth, from the same $B_d$ condition. The shortened-grid API assumes $2W<L_*$; the draft allows equality in this intermediate lemma, but its chosen bandwidth satisfies the strict bound. Lean uses a proved frequency-dependent cubic derivative bound instead of reproducing the draft's sharper intermediate derivative estimate; the sufficient final condition is unchanged. |
| Lemma `lem:anchor-measurement` | Measured control of a localized clump | [MultiClump/Convolution](MultiClump/Convolution.lean): `finite_shift_energy_le`, `selectorAction_energy_le`, `selectorAction_exponentialSum`; [MultiClump/LinearNorming](MultiClump/LinearNorming.lean): combination with `filtered_clump_norming_half` | **Special case**. The exact squared convolution estimate and the half-norming step prove the stated $\sqrt2$ bound in the uniform-norming proof, where $2W<L_*$; the inclusive endpoint $2W=L_*$ in the standalone draft lemma is not separately exported. The finite-shift theorem is more general and has no support-cardinality factor. |
| Lemma `lem:swept-volume` | Volume of a rectangle swept along a segment | [MultiClump/ConvexSweep](MultiClump/ConvexSweep.lean): `coordinateBoxSweep_volume_le` | **Equivalent**. Exact volume inequality; Lean states it using `ENNReal.ofReal`. |
| Lemma `lem:block-restoration` | Restore every continuous translation of a shortened block | [MultiClump/TranslatedBlockRestoration](MultiClump/TranslatedBlockRestoration.lean): `continuousEnergy_translated_le_shortenedGrid_of_cardinality_le`; [MultiClump/BlockRestoration](MultiClump/BlockRestoration.lean): `continuousEnergy_le_shortenedGrid` | **Equivalent**. Exact squared-energy form for at most $n^\star$ frequencies when $n^\star\ge2$; the second theorem covers the zero-shift singleton branch. |
| Lemma `lem:translation-constant` | The improved frame pays the translation cost | [MultiClump/LinearGapConstants](MultiClump/LinearGapConstants.lean): `linearGap_mass_budget` | **Equivalent**. Exact scalar inequality, with `clumpSelectorBound` abbreviating the right-hand side and inverse square-root powers replacing equivalent real-power notation. |
| Proposition `prop:uniform-norming` | Uniform norming over all measured product blocks | [MultiClump/LinearNorming](MultiClump/LinearNorming.lean): `continuousNorming_of_linear_multiclump_blocks`; [MultiClump/NormingConstants](MultiClump/NormingConstants.lean): `multiClumpNormingConstant_mul_energy_loss` | **Equivalent**. Exact displayed $\eta_0$ in `ContinuousNorming` energy form, for the short real representatives fixed after `lem:clump-lifts`; all selectors and reconstruction identities are proved internally. The public final theorem constructs the representatives itself. |
| Lemma `lem:clump-fullcube` | Full-cube lower bound from cross-clump separation | [MultiClump/FullCube](MultiClump/FullCube.lean): `fullCube_clump_fullAperture_lower`, `multiClumpCubeLowerBound_le`; [MultiClump/BlockParameters](MultiClump/BlockParameters.lean): `fullApertureCubeSide_properties`, `fullApertureCubeSide_large`, `fullApertureCubeSide_gap` | **Equivalent**. Exact factored cube coefficient and chosen even cube side, with the proved torus-representative and clipped-spacing conversions. The general-product enclosing-box gap conversion is `fullApertureCubeSide_enclosing_gap` in [MultiClump/GeneralProduct](MultiClump/GeneralProduct.lean). |

### [MultiTuranMultiClumpV2.tex](../../drafts/MultiTuranMultiClumpV2.tex): consecutive-window version

Declarations in this table are in `LeanNumDetect.MultiTuran.ConsecutiveWindow`.

| TeX type and label | Subject | Direct Lean declaration | Relationship |
| --- | --- | --- | --- |
| Theorem `thm:main` | Complete multi-clump product-row bound with consecutive-window norming | [ConsecutiveWindow/Main.lean](ConsecutiveWindow/Main.lean): `consecutiveWindowArray_minimumSingularValue_lower`, `consecutiveWindowProductArray_minimumSingularValue_lower`, `consecutiveWindowRawProduct_minimumSingularValue_lower` | **Equivalent**. Exact coefficient and actual largest clump size. The first theorem is the literal same-aperture statement; the other interfaces retain independently specified enclosing boxes and original block starts. Chart, norming, and full-cube inputs are constructed internally. |
| Proposition `prop:norming` | Consecutive-window norming after a common torus chart choice | [ConsecutiveWindow/Norming.lean](ConsecutiveWindow/Norming.lean): `exists_chart_continuousNorming`; [ConsecutiveWindow/ProductNorming.lean](ConsecutiveWindow/ProductNorming.lean): `continuousNorming_of_long_consecutive_blocks` | **Equivalent**. Constructs the closed short chart and proves actual norming with $\eta_0=[18n(3n)^{2n}]^{-d}$ from $L_{q,\min}\ge n$. The sector/Cauchy/Newton interpolation, repeated coordinate values, complete $2n-1$ window count, block integrals, and product iteration are proved. |
| Lemma `lem:restriction` | Product restriction for every full-aperture admissible $(M,s)$ | [ConsecutiveWindow/Norming.lean](ConsecutiveWindow/Norming.lean): `window_restriction_lower_of_norming`; [ConsecutiveWindow/Restriction.lean](ConsecutiveWindow/Restriction.lean): `product_restriction_lower` | **Equivalent**. The first declaration is the literal lemma with its fixed window coefficient and stated norming premise. `window_product_restriction_lower` derives that premise from the chart and block lengths; the generic enclosing-box restriction is also proved. |
| Lemma `lem:elementary` | Elementary full-cube bound and exact no-wrap scaling | [ConsecutiveWindow/Elementary.lean](ConsecutiveWindow/Elementary.lean): `fullCube_elementary_bound`, `fullCube_no_wrap_separation`, `fullCube_elementary_no_wrap_bound` | **Equivalent**. Direct applications of the main text's proved full-cube and no-wrap interfaces, preserving $1/\sqrt n$ and exponent $n-1$. |
| Corollary `cor:single-clump` | Localized single-clump bound with the consecutive-window coefficient | [ConsecutiveWindow/SingleClump.lean](ConsecutiveWindow/SingleClump.lean): `singleClump_minimumSingularValue_lower` | **Equivalent**. Literal open-cube localization after a common translation, $l_{q,m}\ge n-1$, $N_{\min}\ge2n$, $n\ge4$, and the exact window coefficient. Norming and restriction are constructed internally. |
| Lemma `lem:aperture` | Selected full-cube bound with gap at $N_{\min}$ and unrestricted within-clump geometry | [ConsecutiveWindow/Aperture.lean](ConsecutiveWindow/Aperture.lean): `fullAperture_clump_minimumSingularValue_lower`; [ConsecutiveWindow/CubeBounds.lean](ConsecutiveWindow/CubeBounds.lean): `selected_fullAperture_unrestricted_clump_lower` | **Equivalent**. Exact even cube side, actual largest clump size, displayed coefficient, and spacing minimum. The unrestricted torus neighbor construction replaces the short-clump factor step while reusing the original NumDetect interpolation-to-SVD argument. |

## Supporting definitions and proof interfaces

These equations and internal constructions support the statements above;
they are separate from the active-statement correspondence tables.

| Manuscript formula or proof step | Module and content |
| --- | --- |
| `eq:torus-distance`, `eq:separation-diameter` | [Preliminaries/Geometry](Preliminaries/Geometry.lean): quotient metric and `nodeSeparation_mul_nat` |
| `subsec:app-md`, `eq:product-thickening`, `eq:rhoL` | [Preliminaries/SegmentedGrid](Preliminaries/SegmentedGrid.lean): all finite row sets and exact geometric parameters |
| `eq:general-filling-ratio` | [Preliminaries/Volume](Preliminaries/Volume.lean): `coordinateThickening_volume`, `thickening_volume`, `fillingRatio_eq_volume_ratio` |
| `eq:minsv-characterization` | [Preliminaries/Energy](Preliminaries/Energy.lean): `minimumSingularValue_characterization`, including attainment on the unit sphere |
| Elementary full-cube interpolation | [Preliminaries/CardinalPackets](Preliminaries/CardinalPackets.lean), [FullAperture/FullCube](FullAperture/FullCube.lean): finite coefficient presentations and cardinal products with precisely $n-1$ factors |
| Derivative control sufficient for discretization | [Bernstein/BernsteinSpace](Bernstein/BernsteinSpace.lean), [Bernstein/BernsteinEnergy](Bernstein/BernsteinEnergy.lean), [Bernstein/BernsteinInner](Bernstein/BernsteinInner.lean), [Bernstein/BernsteinOperator](Bernstein/BernsteinOperator.lean), [Bernstein/Bernstein](Bernstein/Bernstein.lean): the actual restricted exponential space, its actual integral inner product, actual differentiation, integration by parts, and `exponentialSum_interval_derivative_norm_le`; this uses a proved cubic bound rather than asserting the manuscript's sharper general $n^{5/2}$ Bernstein estimate |
| Common translation convention | [Preliminaries/Translation](Preliminaries/Translation.lean): invariance of continuous and discrete energy, norming, separation, diameter, and all generalized Vandermonde singular values |
| Geometric and arithmetic discretization steps | [Norming/Discretization](Norming/Discretization.lean), [Norming/ProductDiscretization](Norming/ProductDiscretization.lean), [Norming/NormingConstants](Norming/NormingConstants.lean), [Preliminaries/BoundFormula](Preliminaries/BoundFormula.lean): actual block integrals, exact measured-cell cover, coordinate oscillation telescoping, relative-error transfer, and real-root threshold conversion |
| Continuous product restriction | [Turan/Main](Turan/Main.lean): `aperture_supNorm_turan` discharges the actual supremum premise of `apertureL2_le_of_supNorm_restriction` in [Norming/ProductRestriction](Norming/ProductRestriction.lean) |
| Reusable restriction and singular-value assembly | [SingleClump/ScaledRestriction](SingleClump/ScaledRestriction.lean): `segmentedArrayLowerBound_le_of_supNorm_comparison`, an internal generalization with an explicit supplied comparison |
| Floor and normalization steps | [SingleClump/Scaling](SingleClump/Scaling.lean): `aperture_quotient_lower`, `aperture_scaled_factors_lower`, `half_norming_sqrt_normalization` |
| Numerical expression `eq:sv-md-array` and condition `eq:md-block-condition` | [Preliminaries/BoundFormula](Preliminaries/BoundFormula.lean): the literal definitions `segmentedArrayLowerBound` and `SegmentedBlockCondition`; the corresponding inequality is proved in [SingleClump/SegmentedArray](SingleClump/SegmentedArray.lean) |

Declaration names in this supporting table are relative to
`LeanNumDetect.MultiTuran` except where a subnamespace is explicitly
included.

## Proof structure

The one-dimensional Turán proof is self-contained over mathlib. A recurrence
for sampled exponential sums gives interval extrapolation and complex disk
growth with degree exactly $n-1$. The actual analytic divisor supplies the
finite zero family with multiplicities. Finite Blaschke factors, the maximum
principle and Harnack's inequality give a bounded zero-free quotient and a
quantitative logarithmic derivative estimate. Harmonic circle averages and
Fatou's lemma prove the weak distribution estimate for arbitrary finite
Cauchy sums. An actual effective root potential has integral at most
$\alpha(2N+(n-1)\log(1/\alpha))$. This proves the bounded-spectrum geometric
mean bound. Pruning at the extreme frequencies handles large spectra by
induction on the number of terms while retaining the original measurable
set. The zero function, repeated frequencies and zero prunings are explicit
branches. Affine scaling then gives every bounded interval.

[Turan/GeometryRay](Turan/GeometryRay.lean),
[Turan/GeometryPolar](Turan/GeometryPolar.lean), and
[Turan/GeometryDensity](Turan/GeometryDensity.lean) prove convex-body ray
selection and volume disintegration. The multidimensional argument applies
the proved one-dimensional measurable-set comparison to the exponential sum
restricted to the selected ray; the geometric transfer contributes precisely
$2d$. [Turan/Main](Turan/Main.lean) supplies that scalar comparison to
[Turan/GeometryTransfer](Turan/GeometryTransfer.lean) and
[Turan/EssentialTransfer](Turan/EssentialTransfer.lean), exporting both ordinary
supremum and essential $L^\infty$ bounds. See the [Turán guide](Turan/README.md)
for the four proof lines and their points of assembly.

The exact unit-interval Nikolskii estimate is proved from an explicit
two-component unitary polynomial recurrence, finite DFT Parseval and right
endpoint Riemann convergence. Its interval and product versions use actual
integrals and suprema. The norming proof uses actual differentiation on the
finite exponential function space, its integral Hilbert norm, integration by
parts and finite-dimensional matrix estimates. The proved cubic Bernstein
bound suffices for the article's literal block threshold. The broader
$(p,\rho)$ Nikolskii statements and sharper general Bernstein estimates are
not needed in this dependency chain and are not asserted here.

[SingleClump/SegmentedArray](SingleClump/SegmentedArray.lean) finally
instantiates the reusable restriction and singular-value assembly with the
proved Turán comparison and uniform norming
constant $1/2$. The resulting coefficient is exactly the article's formula.

The discretization arithmetic distinguishes the error coefficient $K$ from
the sufficient-condition coefficient $2K$. This gives an error at most one
half; using the same coefficient in both places would only give an error at
most one.

## Verification

Run `lake build MultiTuran` or the repository-wide `lake build`.
Run `lake build +MultiTuran.Verification.Audit` for the
[Turán and single-clump audit](Verification/Audit.lean), or
`lake build +MultiTuran.MultiClump.Audit` for the independent
[multi-clump audit](MultiClump/Audit.lean). These inspect all imported project
declarations, including private proofs, for admissions and project axioms,
and check the standard-axiom boundary of the listed public results.
The repository-wide admission checker
also includes this directory; run `python3 .github/ci/check.py` for its full
source-token and private-proof-body checks across the repository.
