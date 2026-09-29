# RandSamp

This directory formalizes uniform separated-node, fixed-support, and Cartesian DFT-grid random Fourier sampling from the
RandSamp manuscript, together with the existing nonuniform Fourier--Vandermonde
estimate from the NumDetect manuscript. Import [Main.lean](Main.lean) for the
complete interface. Declarations are in `LeanNumDetect.RandSamp`.

## Fixed-support random sampling

| Manuscript result | Exact Lean location |
| --- | --- |
| Full consecutive-frequency bounds $M\pm2\pi/\Delta$ | [SeparatedFullGram.lean](SeparatedFullGram.lean): `separated_full_energy_bounds` |
| One-dimensional normalized full Gram bound | [SeparatedGramBounds.lean](SeparatedGramBounds.lean): `separated_full_gram_bounds` |
| Fixed node-set lemma (`lem:fixed-support-singular-values`) | [FixedSupport.lean](FixedSupport.lean): `fixedSupport_singularValues` |
| One-dimensional corollary of `thm:fixed-separated-singular-values-higher-dimensional` | [FixedSeparated.lean](FixedSeparated.lean): `fixedSeparated_singularValues` |
| One-dimensional corollary for strict positivity of the lower endpoint | [FixedSeparated.lean](FixedSeparated.lean): `fixedSeparated_lower_bound_pos` |

The one-dimensional corollary retains $M\geq3$, $2\leq s<M$, $1\leq m\leq M+1$,
$0<\rho,\eta<1$, and $2\pi/M<\Delta\leq2\pi/s$. Its sample-size condition is

$$
m\geq \frac{3s(M+1)}{\rho^2(M-2\pi/\Delta)}
\log\!\left(\frac{2s}{\eta}\right).
$$

It proves that the probability of

$$
\sqrt{\frac{(1-\rho)(M-2\pi/\Delta)}{M+1}}
\leq\sigma_{\min}(A_\Omega(Y))
\leq\sigma_{\max}(A_\Omega(Y))
\leq\sqrt{\frac{(1+\rho)(M+2\pi/\Delta)}{M+1}}
$$

is at least $1-\eta$. The separate positivity theorem proves that the displayed
lower endpoint is strictly positive, also by specialization from the cube bound.

The proof of `fixedSeparated_singularValues` calls
`fixedSeparatedCube_singularValues` with $d=1$. The equivalence
`Equiv.funUnique` identifies `Fin 1 → Fin (M+1)` with `Fin (M+1)`;
`finiteSampleEquiv` and `probability_comp_equiv` transport the uniformly
sampled subsets and their event probabilities. The lemma
`cubeSampledVandermonde_one_singularValue` proves that this relabelling
preserves every singular value. The constants simplify using
`cubeSeparatedLower_one` and `cubeSeparatedUpper_one`, while $s\geq2$
turns the original bound $\Delta\leq2\pi/s$ into $\Delta\leq\pi$.
There is no separate concentration or full-Gram argument in the corollary.

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

The fixed-support development covers the dependency chain of the fixed
well-separated theorem. The uniform separated-node and Cartesian DFT-grid
theorems are formalized below.

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

There are no admitted external results. The final probability theorems and
their prerequisites depend only on `propext`, `Classical.choice`, and
`Quot.sound`. [Audit.lean](Audit.lean) rejects admissions and project axioms
throughout the imported project dependencies and checks the final theorems'
transitive axioms. Run `lake build` and `python3 .github/ci/check.py` for the
complete build and admission audit.

## Uniformly over separated nodes in arbitrary dimension

| Manuscript result | Exact Lean location |
| --- | --- |
| Improved full-Gram bound (`eq:uniform-separated-higher-dimensional-full-gram`) | [UniformCubeFullGram.lean](UniformCubeFullGram.lean): `uniform_cube_full_gram_bounds` |
| Exact constants and their one-dimensional reduction | [UniformCubeFullGram.lean](UniformCubeFullGram.lean): `uniformCubeLower`, `uniformCubeLower_pos`, `uniformCubeLower_one` |
| Phase, kernels, normalization, and Gram-entry identities | [UniformKernelModel.lean](UniformKernelModel.lean) |
| Uniform kernel concentration on the entire torus | [UniformKernel.lean](UniformKernel.lean): `uniformCubeKernel_probability` |
| Conversion of a single kernel event to singular-value bounds | [UniformSeparatedEvents.lean](UniformSeparatedEvents.lean): `cube_singularValues_of_uniform_kernel` |
| Main theorem (`thm:uniform-separated-singular-values-higher-dimensional`) | [UniformSeparatedCube.lean](UniformSeparatedCube.lean): `uniformSeparatedCube_singularValues`, `uniformCube_lower_bound_pos` |
| One-dimensional corollary (`thm:uniform-separated-singular-values`) | [UniformSeparated.lean](UniformSeparated.lean): `uniformSeparated_singularValues`, `uniformSeparated_lower_bound_pos` |

The theorem assumes $d\geq1$, $M\geq2$, $s\geq2$,
$1\leq m\leq(M+1)^d$, $0<\rho,\eta<1$, and

$$
\frac{2\pi(2d-1)}{M+\frac32d}<\Delta\leq\pi.
$$

With $c=2\pi/\Delta$, the constants are exactly

$$
a_d^{\mathrm u}=\frac{(M+c)^{d-1}(M+\frac32d-(2d-1)c)}{(M+1)^d},
\qquad b_d=\frac{(M+c)^d}{(M+1)^d}.
$$

The sufficient sample size is

$$
m\geq\frac{16(s-1)^2}{\rho^2(a_d^{\mathrm u})^2}
\log\!\left[\frac{4(1+8\pi dM(s-1)/(\rho a_d^{\mathrm u}))^d}{\eta}\right].
$$

The conclusion has probability at least $1-\eta$ and contains the quantifier
over **all** $Y : \mathrm{Fin}\ s\to\mathrm{Fin}\ d\to\mathbb R$
satisfying `CubeAngularSeparated Δ Y` inside the random event. On this event,

$$
\sqrt{(1-\rho)a_d^{\mathrm u}}\leq\sigma_{\min}(A_\Omega(Y))
\leq\sigma_{\max}(A_\Omega(Y))\leq\sqrt{b_d+\rho a_d^{\mathrm u}}.
$$

The deterministic proof uses Selberg's majorant for $[0,M]$ and minorant for
$(-1,M+1)$. The minorant's nonpositive endpoint values are proved explicitly,
so the lattice sandwich uses exactly $0,\ldots,M$. The tensor correction has
mass $(M+c)^{d-1}(M+2d-(2d-1)c)$, which implies the displayed lower constant.
Poisson summation and closed-band cancellation include separation exactly
$\Delta$. All analytic prerequisites are proved; the final theorem takes no
unproved full-Gram or concentration estimate as an assumption.

The random proof covers the torus with $n^d$ points,
$n=\lceil8\pi dM/\varepsilon\rceil$, and uses the exact centered complex
Hoeffding bound $4\exp(-mu^2/4)$ for uniform sampling without replacement.
The kernel error is $2M$-Lipschitz in coordinate sum distance. This gives the
uniform event at $\varepsilon=\rho a_d^{\mathrm u}/(s-1)$; the Gram
perturbation has zero diagonal and norm at most $(s-1)\varepsilon$.

At $d=1$, `uniformCubeLower_one` gives exactly
$(M+3/2-2\pi/\Delta)/(M+1)$. The one-dimensional corollary retains the original
condition $2\pi/(M+3/2)<\Delta\leq2\pi/s$, the identical sample-size formula,
and the identical singular-value endpoints. Its proof invokes the
higher-dimensional theorem and transports the actual subset distribution
through `Equiv.funUnique`; it contains no independent one-dimensional proof.

## Fixed separated nodes in arbitrary dimension

| Manuscript result | Exact Lean location |
| --- | --- |
| Full frequency-cube energy bounds | [CubeFullGram.lean](CubeFullGram.lean): `cube_separated_full_energy_bounds` |
| Normalized Gram bound (`eq:fixed-separated-higher-dimensional-full-gram`) | [CubeGramBounds.lean](CubeGramBounds.lean): `cube_separated_full_gram_bounds` |
| Fixed-support Chernoff argument for the cube | [CubeFixedSupport.lean](CubeFixedSupport.lean): `cubeFixedSupport_singularValues` |
| Main theorem (`thm:fixed-separated-singular-values-higher-dimensional`) | [FixedSeparatedCube.lean](FixedSeparatedCube.lean): `fixedSeparatedCube_singularValues` |
| Matrix identification at $d=1$ | [CubeRandomModel.lean](CubeRandomModel.lean): `cubeFourierRow_one`, `cubeSampledVandermonde_one_singularValue` |
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
interface and the fully proved Chernoff bounds. The one-dimensional probability
result is obtained only afterward as its $d=1$ corollary. The entire dependency
chain is free of admissions and project axioms.

## Cartesian DFT-grid RIP and its one-dimensional corollary

| Manuscript result | Exact Lean location |
| --- | --- |
| Cartesian grid, characters, and normalized sampled DFT matrix | [DFTGridModel.lean](DFTGridModel.lean): `DFTIndex`, `dftCharacter`, `dftSampledMatrix` |
| Literal Fourier entries and agreement with the existing cube matrix | [DFTGridModel.lean](DFTGridModel.lean): `dftSampledMatrix_apply_exp`, `dftSampledMatrix_eq_cubeSampledVandermonde` |
| Nonzero offsets have zero full mean; there are exactly $N^d-1$ of them | [DFTGridModel.lean](DFTGridModel.lean): `sum_dftCharacter_eq_zero`, `card_nonzero_dftIndex` |
| Uniform coherence probability and exact logarithmic threshold | [DFTGrid.lean](DFTGrid.lean): `dftGrid_coherence_probability`; [DFTGridSamplingRate.lean](DFTGridSamplingRate.lean): `dft_failure_bound_of_sample_size` |
| Arbitrary-dimensional theorem (`thm:dft-grid-rip-higher-dimensional`) | [DFTGrid.lean](DFTGrid.lean): `dftGrid_singularValues`, `dftGrid_restrictedIsometry` |
| Equivalence with the order-$r$ RIP energy formulation | [DFTGridEvents.lean](DFTGridEvents.lean): `dftGridSingularValueEvent_iff_energy` |
| One-dimensional corollary (`thm:dft-grid-rip`) | [DFTGridOne.lean](DFTGridOne.lean): `dftGridOne_singularValues`, `dftGridOne_restrictedIsometry` |
| Exact one-coordinate identification of matrices and support events | [DFTGridOne.lean](DFTGridOne.lean): `dftGridOneSingularValueEvent_iff`, `dftSupportMatrixOne_singularValue` |

The theorem assumes $d,M\geq1$, $N=M+1$, $L=N^d$,
$1\leq m\leq L$, $2\leq r\leq L$, and $0<\rho,\eta<1$.
Its sampling condition is exactly

$$
m\geq\frac{4(r-1)^2}{\rho^2}\log\!\left(\frac{4(L-1)}{\eta}\right).
$$

`DFTIndex d N` is `Fin d → ZMod N`, identified with
$\{0,\ldots,N-1\}^d$ through the canonical residue representatives.
`dftSampledMatrix` has entries $m^{-1/2}\exp(2\pi i k\cdot j/N)$,
and `FiniteSample` consists of the actual $m$-element frequency subsets.
The full matrix uses the Cartesian grid, while its support $S$ can be any
subset of columns; no Cartesian-product or separation restriction is imposed
on $S$.

The conclusion places the quantifier over every support $1\leq|S|\leq r$
inside a single event of probability at least $1-\eta$. Every such matrix has
extremal singular values in $[\sqrt{1-\rho},\sqrt{1+\rho}]$.
`DFTGridEnergyEvent` is the equivalent statement
$\rho_r(A_\Omega^{(d)})\leq\rho$, expressed by the usual energy bounds for
every vector on each support. The equivalence of these two events is proved.

The complex Hoeffding estimate used here is fully proved in
[FiniteScalarConcentration.lean](../General/Probability/FiniteScalarConcentration.lean).
The proof takes a union over $L-1$ nonzero offsets, then applies Gershgorin
to each support Gram matrix. All scalar constants, probability conversions,
and singular-value steps are verified in Lean.

At $d=1$, `dftOneIndexEquiv` and `finiteSampleEquiv` recover scalar frequency
subsets and supports in `Fin (M+1)`. The original `sampledVandermonde`
normalization is retained, and row/column bijections preserve every singular
value. Thus the corollary has the original $N-1$ logarithmic factor, the same
assumptions, and the same endpoints. Its proof invokes the higher-dimensional
theorem; there is no independent one-dimensional probability proof.

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
