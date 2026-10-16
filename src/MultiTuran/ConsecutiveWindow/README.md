# Consecutive-window multi-clump block bounds

This directory proves all six statements of [MultiTuranMultiClumpV2.tex](../../../drafts/MultiTuranMultiClumpV2.tex). The proof constructs a common torus chart, consecutive-window interpolation, actual continuous norming, and unrestricted-clump full-cube interpolation before assembling the displayed singular-value bound.

```lean
import MultiTuran.ConsecutiveWindow.Results
```

The declaration namespace is `LeanNumDetect.MultiTuran.ConsecutiveWindow`. The shared definitions remain in `LeanNumDetect.MultiTuran`; shared clump and enclosing-box interfaces remain in `LeanNumDetect.MultiTuran.MultiClump`. Import `MultiTuran.ConsecutiveWindow.Audit` to check the kernel dependencies of the public results.

## Public interfaces

- `consecutiveWindowArray_minimumSingularValue_lower` is the literal same-aperture multi-clump theorem, with the complete displayed coefficient and actual largest clump size.
- `consecutiveWindowProductArray_minimumSingularValue_lower` retains an independently specified enclosing aperture.
- `consecutiveWindowRawProduct_minimumSingularValue_lower` accepts the original integer block starts, degrees, and enclosing-box endpoints. It restores every measured row after normalizing the first starts.
- `exists_chart_continuousNorming` constructs the representatives and the norming inequality. `continuousNorming_of_long_consecutive_blocks` is the direct norming statement for representatives already in the short chart.
- `window_restriction_lower_of_norming` is the literal restriction lemma with the supplement's fixed norming coefficient and arbitrary admissible $(M,s)$.
- `fullCube_elementary_bound` and `fullCube_no_wrap_separation` are the elementary full-cube estimate and no-wrap identity.
- `singleClump_minimumSingularValue_lower` is the supplement's localized single-clump corollary.
- `fullAperture_clump_minimumSingularValue_lower` is its unrestricted-clump full-cube lemma.

## Sampling model and parameters

The measured rows form the Cartesian product of consecutive integer blocks:

$$
\boldsymbol\Lambda=\prod_{q=1}^d\Lambda_q,\qquad \Lambda_q=\bigcup_m\{a_{q,m},\ldots,a_{q,m}+l_{q,m}\},\qquad L_{q,m}=l_{q,m}+1.
$$

`SegmentedGrid.length` is $l_{q,m}$; `thickLength` is $L_{q,m}$. The coordinate minimum is `coordinateMinLength`, and the actual measured row count is `rowCount`. The right thickening uses every measured cell:

$$
E_{\boldsymbol\Lambda}=\prod_{q=1}^d E_q,\qquad E_q=\bigcup_m[a_{q,m},a_{q,m}+L_{q,m}].
$$

`continuousEnergy` is the Lebesgue integral of $|P|^2$ on this set. `discreteEnergy` is the sum on the actual measured product rows. Both are the existing mathematical definitions, rather than supplied abstract energies.

The nodes are indexed by `Fin n`. Their pairwise positive torus distances are the main text's distinct-node condition. A surjective label map describes a partition into nonempty clumps. Its actual largest fiber cardinality is `largestClumpSize label`:

$$
n^\star=\max_a|C_a|,\qquad 1\le n^\star\le n,\qquad \theta_{\min}=\min_{i\ne j}\|\boldsymbol y_i-\boldsymbol y_j\|_{\mathbb T,\infty}>0.
$$

`ClumpSlots` is the internal finite-capacity representation constructed from this partition. The public partition theorem uses the actual maximum cardinality, not an independent replacement parameter.

For the general product interface, `G` records the measured normalized blocks, while `H` records the chosen enclosing aperture $N_q$. Thus

$$
N_{\min}=\min_q N_q,\qquad \rho_{\boldsymbol\Lambda}=\frac{|\boldsymbol\Lambda|}{\prod_qN_q},\qquad \rho_L=\left(\frac{\prod_q L_{q,\min}}{\prod_qN_q}\right)^{1/2}.
$$

These are `H.minAperture`, `enclosingFillingRatio G H`, and `enclosingLongBlockFactor G H`. The same-aperture specialization has `H = G`, yielding `G.fillingRatio` and `G.rhoL`. `normalizedProductGrid`, `enclosingBoxGrid`, and their proved row identities cover arbitrary first starts and nonminimal enclosing boxes. The raw theorem restores the original frequency vectors by `generalizedVandermonde_rowShift_minimumSingularValue`.

## Complete hypotheses and exact coefficient

The multi-clump public theorem assumes $d\ge2$, $n\ge2$, the distinct-node partition setting above, and

$$
L_{q,\min}\ge n\quad\text{for every }q,\qquad N_{\min}\ge\max\{16n,32d^2n^\star\}.
$$

Its cross-clump condition is

$$
\|\boldsymbol y_i-\boldsymbol y_j\|_{\mathbb T,\infty}>\frac{16\pi dn^\star}{N_{\min}}\qquad(\boldsymbol y_i\in C_a,\ \boldsymbol y_j\in C_b,\ a\ne b).
$$

Within-clump diameters are unrestricted. The final theorem constructs its chart, interpolation polynomials, and norming inequality from these hypotheses; it has no $B_d$, clump-diameter, interpolation, norming, derivative, or cube-bound premise.

`windowNormingLoss d n` and `windowNormingConstant d n` distinguish the energy loss from its reciprocal:

$$
\operatorname{windowNormingLoss}(d,n)=\bigl[18n(3n)^{2n}\bigr]^d,\qquad \eta_0=\operatorname{windowNormingConstant}(d,n)=\bigl[18n(3n)^{2n}\bigr]^{-d}.
$$

The final coefficient is `consecutiveWindowProductArrayLowerBound G H Y nStar`:

$$
\sigma_{\min}(\mathcal V_1)\ge\sqrt{\frac{\eta_0}{n8^{n^\star}}}\left(\frac2{\pi n}\right)^d\rho_L\left(\frac{\rho_{\boldsymbol\Lambda}}{C_{\mathrm T}d}\right)^{n-1}\left(\frac{N_{\min}}{6n^\star}\right)^{d/2}\min\left\{1,\frac{N_{\min}\theta_{\min}}{8\pi n^\star}\right\}^{n^\star-1}.
$$

Here $C_{\mathrm T}$ is the existing proved absolute `multidimensionalTuranConstant`. The Riemann supplement in [MultiClump/](../MultiClump/README.md) has its own norming coefficient, $B_d$ condition, and $L_*$ separation scale; its constants are documented in that guide.

## Consecutive-window norming proof

[ChartIntervals.lean](ChartIntervals.lean) proves the largest-gap chart construction, including repeated coordinate values. [Chart.lean](Chart.lean) combines the coordinate charts and proves integer-frequency singular-value and torus-distance invariance. The chosen representatives satisfy $|y_{j,q}|\le\pi-\pi/n$.

The analytic construction uses the sector angle $\pi-\pi/(4n)$. [InterpolationGeometry.lean](InterpolationGeometry.lean) proves wrapped angle at least $3\pi/(4n)$, unit-circle chord at least $3/(2n)$, and radial distance at least $1/n$. [InterpolationContourData.lean](InterpolationContourData.lean) combines this with the circular reverse-triangle bound and proves the actual Newton kernels are continuous and boundary integrable.

[RectangleCauchy.lean](RectangleCauchy.lean) proves Cauchy's formula for an axis-parallel rectangle. [InterpolationKernel.lean](InterpolationKernel.lean) constructs the analytic divided-slope regularization; [InterpolationPullback.lean](InterpolationPullback.lean) uses it to reproduce the value at each node. The pullback retains the Jacobian $\exp w$. [InterpolationCoefficientBounds.lean](InterpolationCoefficientBounds.lean) bounds the weighted boundary contribution by $3\log3+4(\pi-\pi/(4n))\le6\pi$ and obtains the exact Newton coefficient bound.

[InterpolationAlgebra.lean](InterpolationAlgebra.lean) proves the finite resolvent identity with its general evaluation variable and remainder, the polynomial mass bounds, and the coefficient-to-exponential conversion. [Interpolation.lean](Interpolation.lean) specializes the resolvent to each node and combines it with the proved Cauchy formula. A repeated node causes no division by a node difference. The formal proof directly establishes the node reproduction used by norming, in place of first packaging the manuscript's stronger general-$z$ integral remainder as a standalone declaration.

The resulting public interpolation interface is

$$
P(t)=\sum_{k=0}^{n-1}a_kP(k),\qquad \sum_{k=0}^{n-1}|a_k|\le3(3n)^n\qquad(0\le t\le n).
$$

For a block with $L=b-a+1\ge n$, the cell at $k$ uses the first sample $a_k=\min\{k,b-n+1\}$. [WindowCounting.lean](WindowCounting.lean) implements the relative start as `min k (L-n)` and proves the complete weighted overlap and explicit multiplicity bound $2n-1$, including the repeated rightmost window. [BlockNorming.lean](BlockNorming.lean) translates only the source coefficients, bounds the cell energy by $9(3n)^{2n}$ times its window energy, and integrates every cell:

$$
\int_a^{b+1}|P(t)|^2\,dt\le9(3n)^{2n}(2n-1)\sum_{m=a}^b|P(m)|^2\le18n(3n)^{2n}\sum_{m=a}^b|P(m)|^2.
$$

The block interface `scalar_grid_block_energy_le` uses the original measured integer block. `scalar_coordinate_energy_le` sums all coordinate blocks and preserves exactly their original finite row set. [ProductNorming.lean](ProductNorming.lean) proves Tonelli tensorization with finite sampling, then applies it to the actual energies. This yields `continuousEnergy_le_windowNormingLoss` and the coefficient-uniform `continuousNorming_of_long_consecutive_blocks`.

## Unrestricted-clump cube proof and shared interfaces

[CubeNeighbors.lean](CubeNeighbors.lean) chooses the integer frequency $k=\lfloor\min\{T,\pi/|u|\}\rfloor$ for a shortest nonzero torus representative $|u|\le\pi$. The argument of the floor is at least one; its floor is at least half that argument. The resulting chord is at least $\sqrt2\,T\Delta/\pi$. Thus [CubeFactors.lean](CubeFactors.lean) constructs an actual two-point factor with mass at most $\sqrt2/(T\Delta/\pi)$ for unrestricted torus geometry.

[CubeWithinClump.lean](CubeWithinClump.lean) takes $T=M/n^\star$ and spacing $\Delta/2$. At most $n^\star-1$ factors fit within degree $M-\lfloor M/n^\star\rfloor$. [CubeInterpolation.lean](CubeInterpolation.lean) combines these factors with the existing color-frame localization polynomial and smoothing bandwidth to obtain the exact total degree $2M=s$.

The shared [NumDetect/Random/CubeClumpBounds.lean](../../NumDetect/Random/CubeClumpBounds.lean) interfaces `liCubeClump_raw_ratio_of_interpolation` and `liCubeClump_raw_coefficient_le_of_ratio` perform the original interpolation-to-singular-value and coefficient conversions. Their inputs concern genuine cardinal polynomials, their coefficient masses, and the corresponding actual matrix; they do not prescribe how the within-clump factors were constructed. This preserves the original cube SVD argument and all its constants.

[CubeBounds.lean](CubeBounds.lean) sets $\Delta=\min\{\theta_{\min},4\pi n^\star/s\}$, so the raw spacing factor is exactly $\min\{1,s\theta_{\min}/(4\pi n^\star)\}$. It then chooses $s=2\lfloor(N_{\min}-1)/2\rfloor$, uses $N_{\min}\le2s$, and derives the displayed aperture factor and minimum with scale $8\pi n^\star$. The required gap satisfies $8\pi dn^\star/s\le16\pi dn^\star/N_{\min}$. [Aperture.lean](Aperture.lean) constructs the actual largest-clump capacity from the supplied partition.

[Restriction.lean](Restriction.lean) reuses the proved enclosing-box restriction and full-aperture machinery from [MultiClump/GeneralProduct.lean](../MultiClump/GeneralProduct.lean) and [FullAperture/FullAperture.lean](../FullAperture/FullAperture.lean). [BoundFormula.lean](BoundFormula.lean) assembles the coefficient with the window norming constant. [Main.lean](Main.lean) constructs the chart and both analytic inputs internally and transports the resulting integer-frequency singular value back to the original nodes.

## Statement correspondence

All local names in the following tables are in `LeanNumDetect.MultiTuran.ConsecutiveWindow`.

| Manuscript statement | Direct Lean declaration | Relationship |
| --- | --- | --- |
| `thm:main` | [Main.lean](Main.lean): `consecutiveWindowArray_minimumSingularValue_lower`; general and raw interfaces `consecutiveWindowProductArray_minimumSingularValue_lower`, `consecutiveWindowRawProduct_minimumSingularValue_lower` | Exact coefficient, actual largest clump cardinality, and complete hypotheses; the latter interfaces preserve independently specified apertures and original block starts. |
| `prop:norming` | [Norming.lean](Norming.lean): `exists_chart_continuousNorming`; [ProductNorming.lean](ProductNorming.lean): `continuousNorming_of_long_consecutive_blocks` | Constructs the chart and proves actual norming with the exact $\eta_0$. |
| `lem:restriction` | [Norming.lean](Norming.lean): `window_restriction_lower_of_norming` | Literal fixed-window-coefficient statement for every admissible pair. `window_product_restriction_lower` supplies norming from the short chart and block lengths. |
| `lem:elementary` | [Elementary.lean](Elementary.lean): `fullCube_elementary_bound`, `fullCube_no_wrap_separation`, `fullCube_elementary_no_wrap_bound` | Direct applications of the main text's proved full-cube theorem and no-wrap identity. |
| `cor:single-clump` | [SingleClump.lean](SingleClump.lean): `singleClump_minimumSingularValue_lower` | Literal open-cube localization, $l_{q,m}\ge n-1$, $N_{\min}\ge2n$, $n\ge4$, and the window coefficient. |
| `lem:aperture` | [Aperture.lean](Aperture.lean): `fullAperture_clump_minimumSingularValue_lower` | Exact selected even cube, aperture coefficient, and unrestricted within-clump geometry. |

## Equation and intermediate-proof correspondence

| Manuscript equation or step | Proved interface |
| --- | --- |
| `eq:main-hyp`, `eq:clump-gap` | The `hblocks`, `hN`, and `hcross` parameters in the public `Main` and `Aperture` statements |
| `eq:main` | `consecutiveWindowArray_minimumSingularValue_lower`; `consecutiveWindowProductArrayLowerBound` stores the same complete coefficient |
| `eq:eta-choice` | `windowNormingLoss`, `windowNormingConstant`, and their positive-constant lemmas |
| `eq:chart` and integer-phase invariance | `exists_short_chart_of_ordered_points`, `exists_translated_short_chart`, `matrixSingularValue_chartNodes`, `torusLInfDistance_chartNodes`, `nodeSeparation_chartNodes` |
| `eq:norming` | `continuousNorming_of_long_consecutive_blocks`, `exists_chart_continuousNorming` |
| `eq:contour-bounds` | `window_radial_chord_lower`, `window_radial_distance_lower`, `windowBoundary_distance_lower`, `windowNewtonKernel_norm_le` |
| Rectangular Cauchy formula and pullback | `rectangle_cauchy_of_analyticOnNhd`, `windowPullbackRegular_analyticAt`, `windowPullback_cauchy` |
| Newton basis, finite resolvent, repeated-node reproduction | `newtonBasis_mass_le`, `newtonPolynomial_natDegree_le`, `newton_resolvent_identity`, `newton_resolvent_at_node`, `windowNewtonPolynomial_eval` |
| `eq:interpolation-coefficients` | `windowNewtonCoefficient_norm_le`, `newtonPolynomial_mass_le_window_constant`, `exists_window_coefficients_of_polynomial`, `exists_window_interpolation_coefficients` |
| `eq:local-interpolation` | `scalar_exponentialSum_interpolation`, `scalar_exponentialSum_translate`, together with `exists_window_interpolation_coefficients` |
| Cell Cauchy--Schwarz and full overlap $2n-1$ | `norm_combination_sq_le`, `cell_offset_mem_window`, `window_weighted_sum_le`, `window_multiplicity_le` |
| `eq:block-norming` | `block_integral_le_of_cell_bound`, `scalar_block_energy_le`, `scalar_grid_block_energy_le` |
| Summing blocks and product iteration | `coordinate_integral_le_of_block_bound`, `scalar_coordinate_energy_le`, `pi_coordinate_integral_bound`, `continuousEnergy_le_windowNormingLoss` |
| `eq:restriction-bound` | `window_restriction_lower_of_norming` |
| `eq:elementary` and separation scaling | `fullCube_elementary_bound`, `fullCube_no_wrap_separation` |
| `eq:single-clump` | `singleClump_minimumSingularValue_lower` |
| Unrestricted neighbor factors and full-cube cardinal interpolation | `exists_quantized_torus_chord`, `torus_neighbor_factor`, `withinClumpPolynomial_unrestricted`, `liInterpolationPolynomial_unrestricted`, `cube_raw_ratio_unrestricted` |
| Spacing clipping, selected side, and `eq:aperture` | `fullCube_unrestricted_clump_clipped_lower`, `selected_fullAperture_unrestricted_clump_lower`, `fullAperture_clump_minimumSingularValue_lower`; shared `fullApertureCubeSide_properties`, `fullApertureCubeSide_large` |
| `eq:product-bound` and final assembly | `window_product_restriction_lower`, `consecutiveWindowProductArrayLowerBound_le_of_norming_cube`, `consecutiveWindowArray_minimumSingularValue_lower` |

The helper restriction and interpolation transfer theorems accept their mathematical inputs explicitly. The public final theorems construct those inputs and retain only the supplement's sampling, partition, distinct-node, aperture, and cross-clump hypotheses.

## Verification

```text
lake build MultiTuran.ConsecutiveWindow.Results MultiTuran.ConsecutiveWindow.Audit
```

[Audit.lean](Audit.lean) checks every imported project declaration for admissions and project axioms. It also verifies that the public chart, interpolation, norming, restriction, single-clump, full-aperture, and complete multi-clump results depend only on `propext`, `Classical.choice`, and `Quot.sound`. The development introduces no project axioms or admitted literature results.
