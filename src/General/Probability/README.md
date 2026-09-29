# Finite matrix sampling

| Module | Content |
| --- | --- |
| [FiniteAverage.lean](FiniteAverage.lean) | Vector-valued finite averages, Jensen, and reindexing |
| [SamplingConvexOrder.lean](SamplingConvexOrder.lean) | Complete convex comparison of sampling with and without replacement |
| [FiniteLaplace.lean](FiniteLaplace.lean) | Finite Markov inequality and exact scalar Chernoff optimization |
| [MatrixLaplace.lean](MatrixLaplace.lean) | Iteration of one-step exponential-moment bounds and subset comparison |
| [MatrixChernoff.lean](MatrixChernoff.lean) | Fully proved exact lower and upper matrix Chernoff tails without replacement |
| [FiniteMatrixSampling.lean](FiniteMatrixSampling.lean) | Fixed-cardinality subsets, counting probability, quadratic forms, unit-sphere extrema, and elementary probability operations |
| [UniformCounting.lean](UniformCounting.lean) | Equality of counting probability with Mathlib's uniform PMF probability |
| [ChernoffFactors.lean](ChernoffFactors.lean) | Proofs that the exact Chernoff factors are bounded by the standard Gaussian-type exponentials |
| [MatrixChernoffBounds.lean](MatrixChernoffBounds.lean) | Simultaneous lower and upper sample-mean bounds, with normalization and the union bound proved |
| [FinitePopulationReindex.lean](FinitePopulationReindex.lean) | Transport of uniform subset probabilities and matrix means to any finite population, including multidimensional frequency cubes |
| [FiniteScalarConcentration.lean](FiniteScalarConcentration.lean) | Fully proved real and complex Hoeffding bounds for uniform sampling without replacement, via bounded exponential moments and convex comparison |
| [FiniteUnion.lean](FiniteUnion.lean) | Finite union bounds and simultaneous success events for uniform counting probability |
| [FiniteCenteredConcentration.lean](FiniteCenteredConcentration.lean) | Centered real and complex Hoeffding bounds with exact width-two constants, for populations with arbitrary mean |
| [FiniteUniformConcentration.lean](FiniteUniformConcentration.lean) | Finite-net extension of centered concentration and exact logarithmic sampling arithmetic |

Declarations are in `LeanNumDetect.FiniteMatrixSampling`. For a finite population
of $N$ matrices, `Sample N m` contains exactly the subsets of size $m$.
`sampleMean_bounds_probability` gives quadratic-form bounds with failure at most

$$
d\exp\!\left(-\frac{ma\delta^2}{2R}\right)
+d\exp\!\left(-\frac{ma\delta^2}{3R}\right),
$$

where $d$ is matrix dimension, each population matrix lies between $0$ and $RI$,
and the population mean lies between $aI$ and $bI$, with $a>0$.

Every proof in this directory is complete and independent of admitted external
results. [MatrixChernoff.lean](MatrixChernoff.lean) proves the exact lower and
upper tails from the matrix tools in
[MatrixAnalysis](../MatrixAnalysis/README.md), finite convex comparison,
and scalar Laplace optimization. Both exact tails and their final applications
use only standard Lean axioms.

`finiteSampleMean_bounds_probability` has the same bound for an arbitrary
finite index type. Its event is defined on `FiniteSample κ m`, the actual
subsets of that type. The proof transports the finite-dimensional theorem
through an equivalence and proves the invariance of both counting probability
and matrix means. It introduces no further external assumptions.

`finiteSample_complex_norm_probability_le` applies to any finite complex
population $f$ with $|f(k)|\leq1$ and $\sum_k f(k)=0$. For $u>0$ and
$1\leq m\leq|\kappa|$, it proves the exact without-replacement estimate

$$
\mathbb P\!\left(\left|\frac1m\sum_{k\in\Omega}f(k)\right|>u\right)
\leq 4\exp\!\left(-\frac{mu^2}{4}\right).
$$

The real moment bound, comparison of sampling schemes, Markov inequality,
and real/imaginary tail split are all proved; no concentration assumption is
added to its callers.

`finiteSample_complex_centered_norm_probability_le` allows a nonzero full
mean and bounds the deviation of the sample mean from it by the same
$4\exp(-mu^2/4)$. The proof applies the proved Hoeffding lemma using the
original coordinate interval width, before convex comparison and Markov.
`finiteSample_uniform_complex_probability_ge` turns a finite net with
extension error $\varepsilon/2$ into a simultaneous bound over an arbitrary
parameter type, with failure at most
$4|\mathcal G|\exp(-m\varepsilon^2/16)$.
