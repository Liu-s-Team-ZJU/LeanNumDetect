# RandSamp

This directory formalizes fixed-support random Fourier sampling from the
RandSamp manuscript, together with the existing nonuniform Fourier--Vandermonde
estimate from the NumDetect manuscript. Import [Main.lean](Main.lean) for the
complete interface. Declarations are in `LeanNumDetect.RandSamp`.

## Fixed-support random sampling

| Manuscript result | Exact Lean location |
| --- | --- |
| Full consecutive-frequency bounds $M\pm2\pi/\Delta$ | [SeparatedFullGram.lean](SeparatedFullGram.lean): `separated_full_energy_bounds` |
| Normalized full Gram bound (`eq:fixed-separated-full-gram`) | [SeparatedGramBounds.lean](SeparatedGramBounds.lean): `separated_full_gram_bounds` |
| Fixed node-set lemma (`lem:fixed-support-singular-values`) | [FixedSupport.lean](FixedSupport.lean): `fixedSupport_singularValues` |
| Fixed well-separated node set (`thm:fixed-separated-singular-values`) | [FixedSeparated.lean](FixedSeparated.lean): `fixedSeparated_singularValues` |
| Strict positivity of the lower endpoint | [FixedSeparated.lean](FixedSeparated.lean): `fixedSeparated_lower_bound_pos` |

The main theorem retains $M\geq3$, $2\leq s<M$, $1\leq m\leq M+1$,
$0<\delta,\eta<1$, and $2\pi/M<\Delta\leq2\pi/s$. Its sample-size condition is

$$
m\geq \frac{3s(M+1)}{\delta^2(M-2\pi/\Delta)}
\log\!\left(\frac{2s}{\eta}\right).
$$

It proves that the probability of

$$
\sqrt{\frac{(1-\delta)(M-2\pi/\Delta)}{M+1}}
\leq\sigma_{\min}(A_\Omega(Y))
\leq\sigma_{\max}(A_\Omega(Y))
\leq\sqrt{\frac{(1+\delta)(M+2\pi/\Delta)}{M+1}}
$$

is at least $1-\eta$. The separate positivity theorem proves that the displayed
lower endpoint is strictly positive.

### Definitions and scope

- `Sample (M+1) m` is the finite type of all $m$-element subsets of
  $\{0,\ldots,M\}$; `probability` is exact uniform counting probability.
  [UniformCounting.lean](../General/Probability/UniformCounting.lean) proves its
  equality with Mathlib's `PMF.uniformOfFintype` event probability.
- `Y : Fin s → ℝ` gives real representatives of torus nodes. `AngularSeparated`
  quantifies over every integer period, so it expresses the non-strict circular
  separation condition. `Y` is fixed outside the random-subset event.
- `sampledVandermonde` has the selected frequencies as its row type and entries
  $m^{-1/2}e^{iky_j}$. `matrixSingularValue A 0` is the largest singular value;
  index `s-1` is the least column singular value, including zero for rank loss.
- `fullGram` is the normalized average of the Fourier rank-one matrices.
  The fixed-support hypothesis $aI\preceq G_M\preceq bI$ is expressed by the
  equivalent bounds on every Euclidean quadratic form. A positive node count
  is explicit, as required for the extreme singular values and $\log(2s/\eta)$.

The scope is the dependency chain of the fixed well-separated theorem.
The earlier uniform-over-all-node-sets theorem, random-kernel theorem,
pairwise-separation theorem, and later DFT-grid theorem are separate results
and are not formalized by this addition.

### Proof boundary

The deterministic large-sieve bound is proved from the repository's closed
Vaaler--Selberg construction, including equality at the separation threshold.
The Fourier rank-one bound, Gram normalization, singular-value conversion,
Chernoff-factor simplification, union bound, and sample-rate arithmetic are all
proved in Lean.

The two exact matrix Chernoff tails for uniform sampling without replacement
are fully proved in [General/Probability/MatrixChernoff.lean](../General/Probability/MatrixChernoff.lean).
The proof includes finite convex comparison, the Golden--Thompson inequality,
the Lie--Trotter product formula, spectral exponential bounds, and scalar
Laplace optimization. Their statements preserve the exact factors and full
parameter ranges of [Tropp (2011), Theorem 2.2](https://arxiv.org/pdf/1011.1595).

There are no admitted external results. Both final probability theorems and
their prerequisites depend only on `propext`, `Classical.choice`, and
`Quot.sound`. [Audit.lean](Audit.lean) rejects admissions and project axioms
throughout the imported project dependencies and checks the final theorems'
transitive axioms. Run `lake build` and `python3 .github/ci/check.py` for the
complete build and admission audit.

## Higher-dimensional fixed separated nodes

| Manuscript result | Exact Lean location |
| --- | --- |
| Full frequency-cube energy bounds | [CubeFullGram.lean](CubeFullGram.lean): `cube_separated_full_energy_bounds` |
| Normalized Gram bound (`eq:fixed-separated-higher-dimensional-full-gram`) | [CubeGramBounds.lean](CubeGramBounds.lean): `cube_separated_full_gram_bounds` |
| Fixed-support Chernoff argument for the cube | [CubeFixedSupport.lean](CubeFixedSupport.lean): `cubeFixedSupport_singularValues` |
| Main theorem (`thm:fixed-separated-singular-values-higher-dimensional`) | [FixedSeparatedCube.lean](FixedSeparatedCube.lean): `fixedSeparatedCube_singularValues` |
| Positivity and reduction of constants at $d=1$ | [CubeConstants.lean](CubeConstants.lean): `cubeSeparated_lower_bound_pos`, `cubeSeparatedLower_one`, `cubeSeparatedUpper_one` |

The theorem retains $d,M\geq1$, $s\geq2$, $1\leq m\leq(M+1)^d$,
$0<\rho,\eta<1$, and $2\pi(2d-1)/M<\Delta\leq\pi$. With $c=2\pi/\Delta$,
the definitions `cubeSeparatedLower` and `cubeSeparatedUpper` are exactly

$$
a_d=\frac{(M+c)^{d-1}(M-(2d-1)c)}{(M+1)^d},
\qquad b_d=\frac{(M+c)^d}{(M+1)^d}.
$$

Under the manuscript's condition $m\geq3s(a_d\rho^2)^{-1}\log(2s/\eta)$,
the event

$$
\sqrt{(1-\rho)a_d}\leq\sigma_{\min}(A_\Omega(Y))
\leq\sigma_{\max}(A_\Omega(Y))\leq\sqrt{(1+\rho)b_d}
$$

has probability at least $1-\eta$. The lower endpoint is strictly positive.
Both constants reduce exactly to the preceding one-dimensional constants when
$d=1$.

`CubeFrequency d M` is the actual grid `Fin d → Fin (M+1)`, and the event is
uniform on its $m$-element subsets. `CubeAngularSeparated` requires, for every
pair of distinct nodes, a coordinate whose circular distance is at least
$\Delta$. The chosen coordinate may depend on the pair; no Cartesian-product
condition is imposed on the node set. [CubeRandomModel.lean](CubeRandomModel.lean)
defines the phase $e^{ik\cdot y_j}$, proves that the grid has $(M+1)^d$ elements,
and verifies the $m^{-1/2}$ normalization and the dimension-independent row
bound $s$.

The deterministic proof reuses the fully proved Barton majorant/minorant
construction. Its lower mass $2M^d-(M+c)^d$ is at least the requested
$(M+c)^{d-1}(M-(2d-1)c)$; `cubeLower_le_bartonMass` proves this comparison by
Bernoulli's inequality. This proves the stated constants directly, including
non-strict separation, without additional analytic assumptions or limit
hypotheses. The probability proof uses the proved finite-population reindexing
interface and the fully proved Chernoff bounds used by the one-dimensional
theorem. The entire dependency chain is free of admissions and project axioms.

## Nonuniform VDM scaling

| Manuscript result | Exact Lean location |
| --- | --- |
| Nonuniform VDM scaling (`thm:nonuniform_vdm_scaling`) | [NonuniformVandermonde.lean](NonuniformVandermonde.lean): theorem `nonuniformVandermonde_minimumSingularValue` |

The theorem treats an arbitrary injective $M$-row frequency family and defines
its order-$n$ sampling spread as the largest minimum spacing among all $n$-row
selections. It gives an explicit $\varepsilon>0$ such that every cluster with
$0<\Delta<\varepsilon$ and $|y_j-y_0|\leq\tau\Delta/2$ satisfies

$$
\sigma_{\min}(V) \geq \frac12 c(n)(\gamma\Delta)^{n-1},
$$

where `nonuniformVandermondeConstant n` is positive and depends only on $n$.
Writing $\gamma$ for the order-$n$ sampling spread and $R_n$ for the proved
exponential-remainder coefficient, Lean takes

$$
\varepsilon
=\min\left\{
\frac{2}{W\tau},
\frac{\frac12 c(n)\gamma^{n-1}}
{n(W\tau/2)^nR_n}
\right\}.
$$

Thus the remainder estimate is discharged inside the proof rather than exposed
as a hypothesis of the manuscript-facing theorem.

## Nonuniform scaling proof organization

| Module | Role |
| --- | --- |
| [SquareVandermonde.lean](SquareVandermonde.lean) | Lagrange inverse and quantitative lower bound for normalized square power Vandermonde matrices |
| [TaylorFactorization.lean](TaylorFactorization.lean) | Frequency and source Taylor factors, exponential remainder, raw bound, and explicit $n$-dependent constant |
| [NonuniformVandermonde.lean](NonuniformVandermonde.lean) | Translation invariance, sampling spread and its maximizing row selection, and the manuscript-facing theorem |
| [Main.lean](Main.lean) | Aggregate public import |

All estimates are proved in Lean. In particular, the Lagrange coefficient
bound, Taylor remainder, row-selection monotonicity, and translation from a
centered cluster are not introduced as assumptions.
