# Multi-clump block sampling with the Riemann condition

This directory formalizes Version I of `MultiTuran/notes/multiclump-block-bound-riemann.tex`. Version II is outside its scope. Import `MultiTuran.MultiClump.Results` for the public results, or `MultiTuran.MultiClump.Audit` to check their kernel dependencies.

All declarations are in `LeanNumDetect.MultiTuran.MultiClump`. The single-clump infrastructure and unconditional Turán theorem are imported from the parent directory; no literature theorem is admitted in this proof.

## Public theorem interfaces

In `ProductResult.lean`, `multiClumpProduct_minimumSingularValue_lower` is the general product-row result. Here `G` describes the measured blocks after translating each coordinate's first start to zero, `offset` restores their actual starting positions, and `H` supplies only the chosen enclosing-box dimensions. The conclusion is about the actual shifted Vandermonde matrix. Its coefficient `generalProductArrayLowerBound` uses the original measured row count and minimum block lengths from `G`, and the original chosen aperture and box volume from `H`.

The partition is supplied by a surjective finite labeling, so its clumps are nonempty. `largestClumpSize label` is the actual maximum fiber cardinality, rather than an independent bound. The node-distinctness premise is pairwise positive torus distance. In `DistinctNodes.lean`, `nodeSeparation_pos_iff_pairwise_torusDistance_pos` proves that this is exactly equivalent to positive minimum separation when $n\ge2$; it adds no numerical separation threshold.

In `GeneralProduct.lean`, `generalProductArray_minimumSingularValue_lower` displays the full factored formula for an arbitrary largest-clump upper bound $n^\star\le n$. In `Main.lean`, `multiClumpArray_minimumSingularValue_lower` is its specialization to the original segmented-array aperture convention, with the complete displayed coefficient. The helper interfaces with `ClumpSlots` construct every selector internally and have no interpolation, norming, derivative, cube-bound, or Turán premise.

The module names above identify files, not additional namespace components.

## Clump geometry with the single scale $\tau$

The parameter $\tau$ bounds each clump's periodic $\ell^\infty$ diameter. The public results assume $0<\tau\le\pi/(2d)$ and

$$
\|\boldsymbol y-\boldsymbol z\|_{\mathbb T,\infty}\le\tau\quad(\boldsymbol y,\boldsymbol z\in C_a),\qquad
\|\boldsymbol y-\boldsymbol z\|_{\mathbb T,\infty}>\max\left\{\tau,\frac{16\pi d(n^\star)^2}{L_*}\right\}\quad(\boldsymbol y\in C_a,\boldsymbol z\in C_b,\ a\ne b).
$$

The second inequality applies to every pair of nodes in different clumps, using the periodic coordinatewise maximum distance. It is strict and is vacuous for a single clump. Thus the closed $\tau$-neighborhood of a node contains exactly its own clump. There is no independent gap parameter and no lower bound on $\tau L_*$.

`BlockFeasibility.lean` proves directly from the displayed $B_d$ condition that

$$
B_d(n^\star)^{4d+5}\le L_*,\qquad 16d(n^\star)^2\le L_*,\qquad \frac{16\pi d(n^\star)^2}{L_*}\le\pi.
$$

These are consequences of the existing Riemann hypothesis, not additional geometric premises. The proof uses $|\boldsymbol\Lambda|\ge L_*^d$ and the explicit bound $B_d\ge16d$ when $C_{\mathrm B}\ge24$. The internal selector construction uses the explicit threshold $16\pi d(n^\star)^2/L_*$.

## Exact constants and sampling factors

`multiClumpBlockConstant d C_B` is

$$
B_d=2^{d+2}dC_{\mathrm B}(\sqrt{108}+1)(\pi/2)^{2d}.
$$

The absolute Bernstein constant is enlarged, if necessary, to $C_{\mathrm B}\ge24$, as stated in the note. This is a choice of the absolute constant, not an additional geometric assumption. `multiClumpNormingConstant d n nStar C_T` is precisely

$$
\eta_0=\frac1{2n^2}\left(\frac2{\pi^2(n^\star)^2}\right)^d\left(\frac1{2^dC_{\mathrm T}d}\right)^{2(n^\star-1)}\left[1+\left(1+(2-\sqrt{\mathrm e})^{-n^\star/2}\right)^{n^\star}\right]^{-2}.
$$

The final coefficient is

$$
\sqrt{\frac{\eta_0}{n8^{n^\star}}}\left(\frac2{\pi n}\right)^d\rho_L\left(\frac{\rho_{\boldsymbol\Lambda}}{C_{\mathrm T}d}\right)^{n-1}\left(\frac{N_{\min}}{6n^\star}\right)^{d/2}\min\left\{1,\frac{N_{\min}\theta_{\min}}{8\pi n^\star}\right\}^{n^\star-1}.
$$

The scale $8\pi n^\star$ stays inside the minimum. There is no selector-support-cardinality loss. The constant $C_{\mathrm T}$ is the same proved absolute `multidimensionalTuranConstant` as in the single-clump result.

`normalizedProductGrid` constructs the normalized measured grid from arbitrary ordered natural block starts and lengths. `mem_normalizedProductGrid_rows` proves its exact translated row-set identity; no rows are added, removed, or merged. `enclosingBoxGrid` represents any positive chosen integer aperture. `normalizedProductGrid_le_enclosingBoxGrid` derives the enclosing-box premise from the last-endpoint bounds. Thus the general theorem covers both nonzero first starts and nonminimal enclosing apertures in the note. Choosing maximal runs recovers exactly the note's minimum block lengths; allowing a finer declared partition is a further valid, potentially weaker specialization.

## Proof correspondence

| Manuscript label | Lean modules and principal content |
| --- | --- |
| `lem:clump-lifts` | `ClumpLifts`, `ClumpGeometry`, `Lifting`: independent clump cuts, true torus distances, and exact integer-phase invariance |
| `lem:selector-width` | `BlockFeasibility`, `BlockParameters`: the original $B_d$ condition implies threshold feasibility and the selector width fits every block |
| `lem:clump-selectors` | `Selectors`: separated frames, cardinal localizers, clump indicators, and their coefficient-mass bound |
| `lem:block-restoration` | `ShortenedGrid`, `BlockRestoration`: shorten every block, restore the full rectangle energies, and account for null boundary overlaps |
| `lem:clump-riemann` | `ClumpDerivative`, `ClumpRiemann`: genuine derivatives, coordinate variation, product Nikolskii, and the uniform half-norming inequality |
| `lem:selector-cancellation` | `Convolution`: finite weighted Cauchy–Schwarz, injective row shifts, and exact extraction of each clump |
| `prop:uniform-norming` | `ClumpSums`, `BlockParameters`, `NormingConstants`, `Norming`: actual clump cardinalities, the original $B_d$ condition, and exact cancellation of the displayed $\eta_0$ |
| `lem:clump-fullcube` | `FullCube`: genuine clump interpolation, arbitrary positive pair-distance lower bounds, clipping, and the exact displayed cube coefficient |
| `lem:aperture-transport` | Parent `FullAperture`: integer cube shifts, integration over disjoint unit cells, and the full-aperture energy bound |

The final proof of `thm:main` combines these eight lemmas and the uniform-norming proposition with the parent `Turan` restriction theorem. `BoundFormula`, `Main`, `GeneralProduct`, `RowShift`, and `ProductResult` assemble the exact coefficient and transfer it to the actual measured product rows and the chosen enclosing box.

For `lem:clump-riemann`, Lean uses the proved frequency-dependent cubic derivative estimate on the local sum, followed by squared-modulus variation. Its intermediate powers are $2d+3$ and $2d+2$, which are dominated by the note's $4d+5$ and $4d+1$ for $d\ge2$. The resulting sufficient condition is the same displayed $B_d$ condition. The proof does not assume the sharper Bernstein inequality as an extra premise.

## Verification

Run `lake build` for the entire repository, `lake build +MultiTuran.MultiClump.Audit` for the independent imported-proof audit, and `python3 .github/ci/check.py` for the repository-wide source and private-proof-body audit. The audit rejects project axioms and admissions, and checks that the public theorem dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.
