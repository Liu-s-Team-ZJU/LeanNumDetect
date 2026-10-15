# MultiTuran

This directory proves the MultiTuran manuscript's `lem:multidim-turan` and
`lem:sv-md-array`, together with the definitions and estimates used by their
formal proofs. Import [MultiTuran.Main](Main.lean) for the single-clump public
interface. Import [MultiTuran.MultiClump.Results](MultiClump/Results.lean) for
the multi-clump product-row results; see the [multi-clump guide](MultiClump/README.md)
for its model, exact coefficient, and proof correspondence.

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
frequencies. The sufficient discretization constant is $80d4^d$. No norming,
derivative, energy lower bound or Turán comparison is an extra hypothesis of
the final theorem. There are no admitted proofs or project axioms in this
development. Fully proved results are not registered in `External`.

## Module map

| Area | Entry modules and role |
| --- | --- |
| Geometry and sampling model | [Geometry](Geometry.lean), [SegmentedGrid](SegmentedGrid.lean), [Volume](Volume.lean), [Translation](Translation.lean): actual torus distances, measured rows, thickening, and common translations |
| Full-aperture lower bounds | [Interpolation](Interpolation.lean), [FullCube](FullCube.lean), [FullAperture](FullAperture.lean): cardinal packets, coefficient norms, and actual energy lower bounds |
| Nikolskii estimates | [Nikolskii](Nikolskii.lean), [NikolskiiIntervals](NikolskiiIntervals.lean), [ProductNikolskii](ProductNikolskii.lean): exact interval constants and product-set bounds |
| Derivatives and norming | [Bernstein](Bernstein.lean), [Discretization](Discretization.lean), [ProductNorming](ProductNorming.lean): actual derivatives, Riemann comparison, and the proved uniform norming constant |
| Turán estimates | [Turan](Turan.lean): scalar measurable-set comparison, convex-body supremum and essential-supremum bounds; the `Turan*` modules contain the analytic and geometric proof |
| Single-clump theorem | [SegmentedArray](SegmentedArray.lean): the literal manuscript conclusion, assembled from [ScaledRestriction](ScaledRestriction.lean) and the proved estimates |
| Multi-clump theorem | [MultiClump/Results](MultiClump/Results.lean): arbitrary product rows, row offsets, independent enclosing apertures, and actual largest-clump size |
| Verification | [Audit](Audit.lean), [MultiClump/Audit](MultiClump/Audit.lean): project admissions, project axioms, and the standard logical-axiom boundary |

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

## Source correspondence

| Manuscript item | Module and result |
| --- | --- |
| `eq:torus-distance`, `eq:separation-diameter`, `lem:no-wrap` | `Geometry`: quotient metric and `nodeSeparation_mul_nat` |
| `subsec:app-md`, `eq:product-thickening`, `eq:rhoL` | `SegmentedGrid`: all finite row sets and exact geometric parameters |
| `eq:general-filling-ratio` | `Volume`: `coordinateThickening_volume`, `thickening_volume`, `fillingRatio_eq_volume_ratio` |
| `lem:interp-sv` | `Interpolation`: `reciprocal_minimumSingularValue_le_of_interpolation`, with the original reciprocal conclusion and coefficient norm |
| `eq:minsv-characterization` | `Energy`: `minimumSingularValue_characterization`, including attainment on the unit sphere |
| Elementary full-cube interpolation | `CardinalPackets`, `FullCube`: finite coefficient presentations and cardinal products with precisely $n-1$ factors |
| `thm:elementary-fullcube` | `FullCube`: `elementary_fullCube_lower`, `elementary_fullCube_no_wrap_lower`, with the literal angular constants |
| `thm:universal-full-aperture`, `cor:full-aperture-elementary` | `FullAperture`: `fullAperture_L2_lower`, `fullAperture_elementary_no_wrap_L2_lower`, with actual integrals and the precise $h^{d/2}$ factor |
| `lem:nikolskii-unit` | `Nikolskii`: `exponentialSum_unitSupNorm_le`, with the exact coefficient $\pi n/2$, arbitrary real frequencies and repeated frequencies allowed |
| `lem:nikolskii-interval`, the $L^2$--$L^\infty$ part of `thm:nikolskii-union` | `NikolskiiIntervals`: exact bounds on actual intervals and finite interval unions; the union bound also permits overlapping intervals |
| `lem:nikolskii-product` | `ProductNikolskii`: `exponentialSum_product_supNorm_le`, with the exact product of coordinate coefficients, actual supremum, and actual product-set integral |
| Derivative control sufficient for discretization | `BernsteinSpace`, `BernsteinEnergy`, `BernsteinInner`, `BernsteinOperator`, `Bernstein`: the actual restricted exponential space, its actual integral inner product, actual differentiation, integration by parts, and `exponentialSum_interval_derivative_norm_le`; this uses a proved cubic bound rather than asserting the manuscript's sharper general $n^{5/2}$ Bernstein estimate |
| Common translation convention | `Translation`: invariance of continuous and discrete energy, norming, separation, diameter, and all generalized Vandermonde singular values |
| `prop:discretization`, uniform norming for localized segmented rows | `ProductNorming`: `continuousNorming_half_of_blockCondition`, `continuousNorming_half_of_localized_blockCondition`, with the literal block condition and explicit $C_{d,\mathrm{disc}}=80d4^d$, actual integrals, actual samples, and no norming or derivative premise |
| Geometric and arithmetic discretization steps | `Discretization`, `ProductDiscretization`, `NormingConstants`, `BoundFormula`: actual block integrals, exact measured-cell cover, coordinate oscillation telescoping, relative-error transfer, and real-root threshold conversion |
| `thm:turan-nazarov-1d` | `TuranUnit`, `TuranAffineTransfer`, `Turan`: `oneDimensional_turan_comparison`, for arbitrary positive-measure subsets of every bounded interval and unrestricted real frequencies |
| `lem:multidim-turan` | `Turan`: `exponentialSum_convexBody_supNorm_le`, `exponentialSum_convexBody_eLpNorm_top_le`, `exists_multidimensionalTuranConstant`; the geometric reduction loses precisely $2d$ |
| Continuous product restriction | `Turan`: `aperture_supNorm_turan` discharges the actual supremum premise of `apertureL2_le_of_supNorm_restriction` in `ProductRestriction` |
| Reusable restriction and singular-value assembly | `ScaledRestriction`: `segmentedArrayLowerBound_le_of_supNorm_comparison`, an internal generalization with an explicit supplied comparison |
| `lem:sv-md-array` | `SegmentedArray`: `segmentedArray_minimumSingularValue_lower`, `segmentedArrayLowerBound_le_minimumSingularValue`, with no additional analytic hypotheses |
| Floor and normalization steps in `cor:subrayleigh-scaled-product` | `Scaling`: `aperture_quotient_lower`, `aperture_scaled_factors_lower`, `half_norming_sqrt_normalization` |
| No-wrap implication in `lem:sv-md-array` | `SegmentedGrid.noWrap_of_localized_nodes`, `SegmentedGrid.noWrap_of_nodes_in_open_cube` |
| Numerical expression `eq:sv-md-array` and condition `eq:md-block-condition` | `BoundFormula`: the literal definitions `segmentedArrayLowerBound` and `SegmentedBlockCondition`; the corresponding inequality is proved in `SegmentedArray` |

Declaration names in this table are relative to `LeanNumDetect.MultiTuran`
except where a subnamespace is explicitly included.

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

`TuranGeometryRay`, `TuranGeometryPolar` and `TuranGeometryDensity` prove the
convex-body ray selection and volume disintegration used by the multi-variable
estimate. Both ordinary supremum and essential $L^\infty$ interfaces are
exported in `Turan`.

The exact unit-interval Nikolskii estimate is proved from an explicit
two-component unitary polynomial recurrence, finite DFT Parseval and right
endpoint Riemann convergence. Its interval and product versions use actual
integrals and suprema. The norming proof uses actual differentiation on the
finite exponential function space, its integral Hilbert norm, integration by
parts and finite-dimensional matrix estimates. The proved cubic Bernstein
bound suffices for the article's literal block threshold. The broader
$(p,\rho)$ Nikolskii statements and sharper general Bernstein estimates are
not needed in this dependency chain and are not asserted here.

`SegmentedArray` finally instantiates the reusable restriction and
singular-value assembly with the proved Turán comparison and uniform norming
constant $1/2$. The resulting coefficient is exactly the article's formula.

The discretization arithmetic distinguishes the error coefficient $K$ from
the sufficient-condition coefficient $2K$. This gives an error at most one
half; using the same coefficient in both places would only give an error at
most one.

## Verification

Run `lake build MultiTuran` or the repository-wide `lake build`.
`MultiTuran.Audit` inspects all imported project declarations, including private
proofs, for admissions and project axioms, and checks the standard-axiom
boundary of the listed public results. The repository-wide admission checker
also includes this directory; run `python3 .github/ci/check.py` for its full
source-token and private-proof-body checks across the repository.
