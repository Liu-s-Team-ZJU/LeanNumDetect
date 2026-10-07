# Independent multidimensional multiclump consistency review

Source review completed on October 8, 2026. This reviewer did not author or edit the manuscript or Lean proofs. The review compares the final standalone [multidimensional draft](MultidimensionalMultiClumpRandomSampling.tex), the actual Lean declarations and their definitions, the retained [one-dimensional draft](MultiClumpRandomSampling.tex), and `/Users/wenchong/articles/NumDetect/main.tex:1285–1325`.

**Verdict: the primary multidimensional theorem agrees with its Lean statement, the model is the literal periodic infinity-metric NumDetect clump model, and the original one-dimensional theorem is an exact specialization with constant $3072$. No unresolved mathematical discrepancy remains. The complete project has zero admissions and zero project axioms.** The final repository-wide compilation and admission evidence is recorded below.

## Principal statement correspondence

The main declaration is `LeanNumDetect.RandSamp.multidimensionalMultiClump_random_row_sampling` in [MultidimensionalMultiClumpTheorem.lean](../src/RandSamp/MultidimensionalMultiClumpTheorem.lean). Its type is `MultidimensionalMultiClumpSamplingStatement`; expanding that proposition and its conclusion gives exactly manuscript `thm:multidimensional-multi-clump-random-sampling`.

| Item | Independent source check |
| --- | --- |
| Dimension and quantifiers | `MultidimensionalMultiClumpSamplingStatement` fixes every integer $d\ge1$ and $2\le n^\star\le n$ before choosing $c_0,C_0$. The explicit constant $C_d=3072\,512^{d-1}$ depends only on $d$. |
| Geometry constants | Both statements require $0<c_0<1$, $C_0\ge n$ and $M\ge C_0$. The constants precede the bandwidth, partition, nodes, spacing parameters, cardinality and probability parameters. No dependence on $K$ or $\Delta$ is introduced. |
| Partition and exact maximum | `ClumpPartition` is a surjective label map; its fibers partition every source index into nonempty clumps. `HasMaxClumpSize` includes both $n_a\le n^\star$ and an attaining clump. |
| Periodic metric | `multidimensionalAngularTorusDistance` is the finite maximum of coordinate angular winding distances. The minimum winding is attained in `MultiClumpModel.lean`. On canonical representatives the distance is precisely the coordinatewise minimum in NumDetect `defi:metric_separation`. Positive dimension is retained everywhere it is needed. |
| Literal NumDetect structure | `MultidimensionalClumpStructure` retains $0<\tau\le\eta$, attained maximum size, within-clump diameter at most $\tau$, and strict cross distance greater than $\eta$. `toGeometry` proves its conversion to the theorem when $\tau\le c_0/M$ and $\eta\ge C_0/M$. The theorem's closed cross boundary is an explicit extension of that source model. |
| Distinct nodes and arrangements | Distinctness is positivity of periodic infinity distance between different indices. No distinct-coordinate-projection, collinearity, general-position, Cartesian-node, or internal-arrangement premise occurs in the main theorem. |
| Matrices | `CubeFrequency d M` is exactly `Fin d → Fin (M+1)`, of cardinality $(M+1)^d$. `cubeFullVandermonde` has entries $(M+1)^{-d/2}e^{i\langle k,x_j\rangle}$; `cubeSampledVandermonde` has entries $m^{-1/2}e^{i\langle k,x_j\rangle}$ on the actual selected cube rows. The proved Gram and energy identities verify both normalizations. |
| Sampling law | `FiniteSample` consists of actual cardinality-$m$ subsets of the frequency cube. `probability` is uniform counting probability. The statement retains $1\le m\le(M+1)^d$ and $\rho,\delta\in(0,1)$. Sampling is without replacement. |
| Literal sampling rate | `sizePowerSum d` is $\sum_a n_a^{2d}$. The sufficient condition is exactly $m\ge3072\,512^{d-1}\rho^{-2}\sum_a n_a^{2d}\log(2n/\delta)$, and success probability is at least $1-\delta$. There is no inverse-gap factor or added full-sampling alternative. |
| Gram and all singular values | `CubeRelativeGramEvent` imposes the two quadratic-form inequalities for every complex coefficient vector. `CubeAllSingularValueEvent` compares all $n$ ordered column singular values with the exact factors $\sqrt{1\pm\rho}$. Lean index $j$ is manuscript index $j+1$; the least value has index $n-1$. |
| Comparable spacings and powers | `ComparableMultidimensionalClumpSpacing` constrains exactly distinct pairs within each clump by $\Delta\le d_\infty(x,y)\le K\Delta$. Singleton clumps add no condition. The lower power is always $n^\star-1$; the optional upper power is `multidimensionalClumpUpperExponent d nstar`, exactly the largest $q$ with $q^d<n^\star$. |
| Constants and one event | Positive functions `lower` and `upper` of $K$ are chosen before configurations and sampling. `MultidimensionalMultiClumpSuccess` quantifies over every admissible $K,\Delta$ inside the same event. Its proved equivalence to the relative Gram event supplies all these conclusions without a union bound over spacings or coefficient vectors. The node set remains fixed outside probability. |

The sufficient count can exceed the available population; then no cardinality satisfies the premise. The deterministic complete sample preserves the full Gram matrix. Neither manuscript nor Lean changes the conditional theorem to a different sampling hypothesis.

## Proof and lower-only spectrum check

The final theorem discharges positive definiteness, leverage and deterministic spectrum inside `multidimensionalMultiClump_deterministic_control`. None remains an additional hypothesis of the public theorem.

The common one-coordinate thresholds in [AngularClumpSectionBounds.lean](../src/General/Fourier/AngularClumpSectionBounds.lean) control actual coordinate sections even when projected frequencies coincide. The companion representation never inverts the frequency power matrix. The bound $512s^2$ iterates through [ProductEnergyBounds.lean](../src/General/Finite/ProductEnergyBounds.lean) to $512^d s^{2d}$. For a pair of clumps, their anchor infinity distance is attained in a coordinate; the cross-section estimate in that coordinate lifts by Cauchy–Schwarz to the whole cube. The coordinate may depend on the pair. Half-energy assembly loses exactly a factor two. Thus the row radius is

$$
R=2\,512^d\sum_a n_a^{2d}=1024\,512^{d-1}\sum_a n_a^{2d}.
$$

Whitening and the proved without-replacement Chernoff theorem multiply this radius by three, yielding exactly $3072\,512^{d-1}$.

The constructive lower bound in [MultidimensionalClumpSingularBounds.lean](../src/RandSamp/MultidimensionalClumpSingularBounds.lean) separates each pair through an attained coordinate. Integer bandwidth allocation $Q=\lfloor M/(4n)\rfloor$ permits all pair factors and leaves $L=\lfloor M/2\rfloor+1$ averaging frequencies per coordinate. Local chords scale with $M\Delta$; cross-clump chords are bounded below independently of the internal gap. Scaled cardinal factors have bounded coefficient mass. The averaging packet controls the coefficient norm after normalization, and its value at each node is a power determined solely by that node's clump size. Replacing each size by the attained maximum gives the required exponent $n^\star-1$.

`cube_multiclump_singular_lower_normalized` requires only an infinity-distance lower spacing bound. Its coefficient is

$$
c_\infty=\frac{1}{\sqrt n\,2^{n+d}(16\pi n)^{n^\star-1}}.
$$

`cube_multiclump_singular_lower` proves the periodic one-norm version with coefficient $c_\infty d^{-(n^\star-1)}$, using $d_1\le d\,d_\infty$. These conclusions have no upper spacing ratio or internal-arrangement assumption. `multidimensionalMultiClump_sampling_with_sharp_lower` returns the main sampling conclusion and the lower-only sampled estimate for the same $c_0,C_0$ and the same relative Gram event. It quantifies over all later lower spacing parameters. This checks the common-threshold claim in manuscript `prop:multidimensional-sharp-lower`.

The optional upper bound uses a unit kernel vector of the $q^d\times n^\star$ box-moment matrix. The inequality $q^d<n^\star$ alone supplies the kernel; no arrangement hypothesis is inserted. Short coordinate lifts, a tensor Taylor remainder, and zero extension outside the largest clump give precisely the weaker power stated in the manuscript. A generic upper bound with power $n^\star-1$ is not claimed.

## Sharpness and exact dimension-one recovery

[MultidimensionalClumpSharpness.lean](../src/RandSamp/MultidimensionalClumpSharpness.lean) proves that the arithmetic family $\{j\Delta e_1:0\le j<s\}$ is distinct, satisfies the literal strict NumDetect structure, has maximum size $s$, and has exact minimum step $\Delta$ in both periodic metrics. [MultidimensionalClumpSharpnessBounds.lean](../src/RandSamp/MultidimensionalClumpSharpnessBounds.lean) proves the common upper coefficient

$$
B_s=\frac{6\sqrt s\,(s-1)^{s-1}}{(s-1)!}
$$

for the full normalized matrix and every nonempty selected row set. This is the same moment-kernel bound used in the final draft. `arithmeticClump_lower_real_exponent_sharp` contradicts every real exponent $p<s-1$ and every positive proposed lower coefficient by a sufficiently small admissible step. Sharpness is over the allowed model, including its single-clump subfamily; it is not an assertion that every arrangement has the same asymptotic order.

The following is exact transport of the complete conclusion, rather than only rate arithmetic:

1. The dimension-one metric, spacing predicate, geometry and size sum specialize to their original one-dimensional definitions.
2. `Equiv.funUnique` identifies a one-coordinate cube frequency with its sole coordinate, and `finiteSampleEquiv` identifies their actual $m$-element subsets while preserving uniform counting probability.
3. The full and sampled matrices have exactly the same Gram matrices and all ordered singular values under this row reindexing.
4. `multidimensionalMultiClumpSuccess_one` specializes the entire event, including all $K,\Delta$ and both powers. `multiClumpSamplingConclusion_of_multidimensional_one` transports the full probability conclusion with the same constant and the same spectral functions.
5. [MultiClumpTheorem.lean](../src/RandSamp/MultiClumpTheorem.lean) now proves `multiClump_deterministic_control`, `multiClump_random_row_sampling` and `multiClump_sampling_statement` as dimension-one corollaries. Their statement definitions and quantifier order are preserved. The numerical identities are $N=M+1$, $S_1=\sum_a n_a^2$, $C_1=3072$, and $q(1,n^\star)=n^\star-1$.

The seven former independent project clump proof modules have been deleted, and a fresh import search found no surviving imports of them. The one-dimensional primary theorem has no independent analytic proof path remaining. Its current correspondence is also recorded in [MultiClumpConsistency.md](MultiClumpConsistency.md).

## Review corrections and verification evidence

Review observations have been resolved in the final draft: the section lemma now gives common cardinality and geometry quantifiers, its row index is restricted to $0,\ldots,M$, the phase multipliers are integers, the box-upper lemma explicitly retains geometry, and the sample-order remark records its dependence on fixed $\rho$. Real-exponent sharpness and the literal formal sharpness coefficient are now included. These corrections did not strengthen the primary theorem's hypotheses.

I independently ran the required final `.github/ci/check.py` once after the Lean source was frozen. It exited successfully with code 0. The regenerated [CI log](../build/ci-check.log) records a successful explicit-source build of **9013 jobs** and the result: **271 source modules, 4780 project declarations, zero admissions and zero project axioms**. The inspected [default build log](../build/full-build.log) separately records a successful build of **9017 jobs**, including the new cube theorem, one-dimensional corollaries, public entry point and strict multiclump audit.

I inspected both the completed logs and the checker implementation. The checker discovers every Lean source, including unused modules, builds each explicit source target, checks persisted admission warnings, lexes source code for admission or axiom tokens, imports every project module with `importAll` to load private declarations and proof bodies, and rejects admissions in declaration types and bodies as well as every project axiom. It also rejects Lean sources in `src/External`; that directory contains only its attribution README. The fresh evidence covers all new modules and does not reuse the previous 262-module baseline.

[MultiClumpAudit.lean](../src/RandSamp/MultiClumpAudit.lean) also verifies the complete imported project and the transitive axioms of the final cube theorem, joint lower-only conclusion, exact dimension-one corollary, deterministic row and spectral bounds, and real-exponent sharpness. The recorded dependencies are only `propext`, `Classical.choice` and `Quot.sound`; `sorryAx` is absent. The audit uses no exception for named project results or formerly external estimates.

The report's local links were checked to resolve, and the final whitespace check passed. No Lean source or manuscript proof was edited by the reviewer.
