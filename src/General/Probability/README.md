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
| [ChernoffSamplingSlack.lean](ChernoffSamplingSlack.lean) | Exact lower-tail entropy with half the retained relative energy and the enlarged leverage budget $5S/2$ |
| [MatrixChernoffBounds.lean](MatrixChernoffBounds.lean) | Simultaneous lower and upper sample-mean bounds, with normalization and the union bound proved |
| [FinitePopulationReindex.lean](FinitePopulationReindex.lean) | Transport of uniform subset probabilities and matrix means to any finite population, including multidimensional frequency cubes |
| [FiniteScalarConcentration.lean](FiniteScalarConcentration.lean) | Fully proved real and complex Hoeffding bounds for uniform sampling without replacement, via bounded exponential moments and convex comparison |
| [FiniteUnion.lean](FiniteUnion.lean) | Finite union bounds and simultaneous success events for uniform counting probability |
| [FiniteCenteredConcentration.lean](FiniteCenteredConcentration.lean) | Centered real and complex Hoeffding bounds with exact width-two constants, for populations with arbitrary mean |
| [FiniteUniformConcentration.lean](FiniteUniformConcentration.lean) | Finite-net extension of centered concentration and exact logarithmic sampling arithmetic |
| [BoundedRowModel.lean](BoundedRowModel.lean) | Concrete bounded-row energies and covariance definitions, without an admitted concentration result |
| [BoundedRowEstimates.lean](BoundedRowEstimates.lean) | Arbitrary-law integrability, deterministic envelopes, continuity of row pairings and fourth-moment bounds |
| [BoundedRowContinuity.lean](BoundedRowContinuity.lean) | Uniform perturbations, arbitrary-target deviation continuity and arbitrary-law almost-everywhere measurability |
| [BoundedRowTrivialRegime.lean](BoundedRowTrivialRegime.lean) | Probability-one and strict success estimates for arbitrary identically distributed rows when $sK^2\le\delta$ |
| [FiniteSymmetrization.lean](FiniteSymmetrization.lean) | Ghost-sample Jensen and exact factor-two finite-law symmetrization for bounded infinite test classes |
| [FiniteBernoulliProcess.lean](FiniteBernoulliProcess.lean) | Signed-process exponential moments, expected finite maxima and maximal Gaussian tails |
| [ComplexL1WeakNet.lean](ComplexL1WeakNet.lean) | Maurey empirical nets of size $(4N+1)^L$ and a proved exponential exceptional-row count |
| [ComplexAtomicSimplex.lean](ComplexAtomicSimplex.lean) | Exact $4N+1$-atom simplex representation of every complex coordinate $\ell^1$-ball vector |
| [FiniteBernoulliChaining.lean](FiniteBernoulliChaining.lean) | An entropy-sum estimate from finite multiscale increments and a uniform residual |
| [AtomicEmpiricalApproximation.lean](AtomicEmpiricalApproximation.lean) | Weighted finite iid Hoeffding and exceptional-set selection |
| [FiniteBernoulliContraction.lean](FiniteBernoulliContraction.lean) | Scalar and absolute contraction for arbitrary bounded infinite classes |
| [FiniteProductConcentration.lean](FiniteProductConcentration.lean) | Boolean product bounded differences, centered exponential moments and optimized tails |
| [ClippedQuadraticProcesses.lean](ClippedQuadraticProcesses.lean) | Separable clipped-square contraction and localized coefficient-class expectation |
| [WeakShellDecomposition.lean](WeakShellDecomposition.lean) | Causal first-crossing shell decomposition with explicit exceptional-row energy errors |
| [EmpiricalProcessReplacementVariance.lean](EmpiricalProcessReplacementVariance.lean) | Linear-envelope delete-one and conditional replacement variance bounds |
| [FiniteEntropy.lean](FiniteEntropy.lean) | Gibbs variational inequality, entropy convexity and finite weighted product tensorization |
| [FiniteProductReplacement.lean](FiniteProductReplacement.lean) | Coordinate refresh identities and exchangeability under finite product laws |
| [FiniteExponentialEntropy.lean](FiniteExponentialEntropy.lean) | Full product replacement entropy inequality and affine variance-proxy conversion |
| [FiniteProcessSecondMoments.lean](FiniteProcessSecondMoments.lean) | Second moments of maxima from scalar subgaussian moment bounds |
| [FiniteCubeProcessMaxima.lean](FiniteCubeProcessMaxima.lean) | Maximal second moments for finite families of Boolean cube processes |
| [NormalizedClippedMasks.lean](NormalizedClippedMasks.lean) | Cardinality-normalized clipped processes and their finite-family second moments |
| [AtomicPrefixEntropy.lean](AtomicPrefixEntropy.lean) | Cardinality and logarithmic entropy of causal atomic-word prefixes |
| [CausalMaskChaining.lean](CausalMaskChaining.lean) | Path Cauchy--Schwarz and weighted square-root expectation estimates |
| [CausalShellProcesses.lean](CausalShellProcesses.lean) | Exact first-crossing mask expansion and stochastic shell bounds |
| [CausalWeakNetExpectation.lean](CausalWeakNetExpectation.lean) | Constructed atomic words, common exceptional sets and explicit bounded-row Bernoulli expectation |
| [CausalShellParameters.lean](CausalShellParameters.lean) | Logarithmic level counts, word lengths, residuals and squared-logarithm entropy budget |
| [BoundedRowSelfConsistency.lean](BoundedRowSelfConsistency.lean) | Scalar expectation bootstrap and exact sampling-budget arithmetic |
| [WeightedSymmetrization.lean](WeightedSymmetrization.lean) | Exact ghost-sample symmetrization for arbitrary finite probability weights |
| [HerbstBounds.lean](HerbstBounds.lean) | Differential entropy-to-moment conversion with a linear variance envelope |
| [FiniteProcessConcentration.lean](FiniteProcessConcentration.lean) | Subgamma moments and optimized tails from replacement entropy |
| [FiniteEmpiricalSupremumConcentration.lean](FiniteEmpiricalSupremumConcentration.lean) | Cardinality-free deviation tails for finite energy classes |
| [RelativeDeviationTailBounds.lean](RelativeDeviationTailBounds.lean) | Exact relative-error exponent and threshold arithmetic |
| [FiniteEmpiricalRelativeConcentration.lean](FiniteEmpiricalRelativeConcentration.lean) | Relative population-energy tails from an expected-deviation bound |
| [FiniteBoundedRowConcentration.lean](FiniteBoundedRowConcentration.lean) | Exact bounded-row normalization and finite-law tail reduction |
| [FiniteBoundedRowSymmetrization.lean](FiniteBoundedRowSymmetrization.lean) | Energy-specific symmetrization and empirical-energy expectation bootstrap |
| [FiniteBoundedRowZeroTarget.lean](FiniteBoundedRowZeroTarget.lean) | Adding the zero test preserves all nonnegative finite maxima exactly |
| [BoundedRowTargetApproximation.lean](BoundedRowTargetApproximation.lean) | Finite subsets of arbitrary coefficient classes with uniform energy errors |
| [BoundedRowDistributionApproximation.lean](BoundedRowDistributionApproximation.lean) | Uniform reference-law and sampled-row perturbation bounds |
| [BoundedRowQuantization.lean](BoundedRowQuantization.lean) | Finite measurable row quantization preserving the exact coordinate envelope |
| [FiniteWeightedLaw.lean](FiniteWeightedLaw.lean) | Exact finite-law integral and product-event identities, including zero weights |
| [IIDJointLaw.lean](IIDJointLaw.lean) | Exact product-law transport from arbitrary independent identically distributed rows |
| [BoundedRowsFiniteReduction.lean](BoundedRowsFiniteReduction.lean) | Concentration transfer to arbitrary laws, probability spaces and target sets |
| [FiniteBoundedRowExpectation.lean](FiniteBoundedRowExpectation.lean) | Sharp squared-logarithm expected deviation for every finite weighted law and target class |
| [BoundedRieszConcentration.lean](BoundedRieszConcentration.lean) | Complete original arbitrary-law bounded-row concentration theorem |

The finite matrix sampling declarations are in
`LeanNumDetect.FiniteMatrixSampling`; the bounded-row model and reductions are
in `LeanNumDetect.BoundedRieszConcentration`, and weighted entropy estimates
are in `LeanNumDetect.FiniteEntropy`. For a finite population
of $N$ matrices, `Sample N m` contains exactly the subsets of size $m$.
`sampleMean_bounds_probability` gives quadratic-form bounds with failure at most

$$
d\exp\!\left(-\frac{ma\delta^2}{2R}\right)
+d\exp\!\left(-\frac{ma\delta^2}{3R}\right),
$$

where $d$ is matrix dimension, each population matrix lies between $0$ and $RI$,
and the population mean lies between $aI$ and $bI$, with $a>0$.

Every local proof and every supporting project dependency is complete.
The bounded-row theorem preserves arbitrary complex laws, arbitrary
probability spaces, positive real sparsity radii, arbitrary target subsets,
the literal squared-logarithm sampling rate and the strict success-probability
bound. It constructs causal weak atomic shells, bounds their entropy and
exceptional energy, closes the weighted symmetrization bootstrap, proves a
replacement-entropy tail, and transfers the finite result to arbitrary laws
by measurable quantization. The universal constants can be chosen as
$\kappa=1$, $c_0=10^{12}$ and $c_1=178$.
The `BoundedAtomic` application chain imports this complete proof from
`General`; no external admitted theorem remains.
[MatrixChernoff.lean](MatrixChernoff.lean) proves the exact lower and
upper tails from the matrix tools in
[MatrixAnalysis](../MatrixAnalysis/README.md), finite convex comparison,
and scalar Laplace optimization. Both exact tails and their final applications
use only standard Lean axioms.

`sampleMean_lower_bound_probability` retains only the lower matrix-Chernoff
tail, with failure bound $d\exp(-ma\rho^2/(2R))$.
`sampleMean_relative_lower_bound_probability` whitens the actual population
mean and transports that same lower tail back to the original coordinates.
The lower-only event needs no upper-tail estimate or union bound, so its
scalar sample count contains $\log(d/\epsilon)$ rather than
$\log(2d/\epsilon)$.

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

## Half-energy lower sampling

[ChernoffSamplingSlack.lean](ChernoffSamplingSlack.lean) proves
`lower_log_bound_half_slack` and
`sampleMean_relative_half_lower_bound_probability` directly from the exact
Chernoff factor, including whitening. If the row leverage is at most
$5S/2$, the lower Gram event retains $(1-\rho)/2$ of the population energy
with failure at most $n\exp(-m\rho^2/(3S))$.

[WeightedLowerSampling.lean](WeightedLowerSampling.lean) transfers this
lower event from auxiliary weights bounded by one to the original sampled
Gram matrix. [CappedWeightEntropy.lean](CappedWeightEntropy.lean) and
[CappedWeightSpectralCoercivity.lean](CappedWeightSpectralCoercivity.lean)
prove scalar entropy and spectral layercake bounds. Together with the
finite monotone iteration in `General.MatrixAnalysis.CappedWeightSequence`,
[ThickFrameSampling.lean](ThickFrameSampling.lean) derives the required
weights from quantitative subspace thickness. No minimizer or limiting
covariance is assumed. The radius $12n/5$ and relative-update factor $24/25$
give row budget $5n/2$ and the explicit determinant floor
$\exp[-5n-6n\log((12n/5)/\theta^2)]$.

The actual Fourier rows satisfy this thickness condition by the proved
`General.Fourier.CubeFrameThickness` theorem; the final cube sampler exposes
no thickness or leverage assumption.
