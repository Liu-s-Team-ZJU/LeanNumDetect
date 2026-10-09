# Fourier analysis and sampling

This directory contains the proved Fourier dependency chains used by the
segmented Vandermonde and fixed multiclump random-sampling formalizations.
The separated-node entry point is `LeanNumDetect.separated_sampling_half`;
the quantitative clump modules supply the explicit geometry estimates used
by the public NumDetect sampling interface.

For $N\ge2$, arbitrary complex coefficients $c_j$, and periodic separation

$$
|x_i-x_j-2\pi p|\ge\frac{4\pi}{N}
\qquad(i\ne j,\ p\in\mathbb Z),
$$

`separated_sampling_half` proves

$$
\sum_{k=0}^{N-1}\left|\sum_j c_j e^{ikx_j}\right|^2
\ge\frac N2\sum_j|c_j|^2.
$$

The proof uses compact cosine-squared windows, their Fourier transforms and
derivatives, shifted Parseval identities, periodic orthogonality, and a limiting
argument at the critical separation.

| Proof component | Modules |
| --- | --- |
| Shifted Parseval and disjoint supports | [ShiftedParseval.lean](ShiftedParseval.lean), [DisjointParseval.lean](DisjointParseval.lean), [WeightedOrthogonality.lean](WeightedOrthogonality.lean) |
| Cosine windows and transforms | [CosineWindow.lean](CosineWindow.lean), [CosineWindowTransform.lean](CosineWindowTransform.lean), [CosineWindowParseval.lean](CosineWindowParseval.lean) |
| Derivative and weighted-energy estimates | [CosineWindowDerivative.lean](CosineWindowDerivative.lean), [CosineWindowDerivativeParseval.lean](CosineWindowDerivativeParseval.lean), [CosineWindowWeightedEnergy.lean](CosineWindowWeightedEnergy.lean) |
| Periodic orthogonality | [CosineWindowOrthogonality.lean](CosineWindowOrthogonality.lean), [ExponentialWindowOrthogonality.lean](ExponentialWindowOrthogonality.lean) |
| Exact lower bounds | [SineTailProduct.lean](SineTailProduct.lean), [NormalizedCosineIntegral.lean](NormalizedCosineIntegral.lean), [CosineGammaIntegral.lean](CosineGammaIntegral.lean), [CosineWindowFourierLower.lean](CosineWindowFourierLower.lean), [CosineSquaredEnergy.lean](CosineSquaredEnergy.lean) |
| Final sampling estimate | [SeparatedFourierEnergy.lean](SeparatedFourierEnergy.lean), [SeparatedSampling.lean](SeparatedSampling.lean) |
| Source-normalized centered-cube definitions | [SeparatedCubeFourier.lean](SeparatedCubeFourier.lean) |
| Centered-cube algebra and signed-weight reduction | [SeparatedCubeFourierInternal.lean](SeparatedCubeFourierInternal.lean) |
| Continuous cube minorant/majorant reduction | [SeparatedCubeFourierContinuous.lean](SeparatedCubeFourierContinuous.lean) |
| Centered-to-one-sided cube conversion infrastructure | [FineCubeFrame.lean](FineCubeFrame.lean) |
| One-dimensional periodic-Hilbert reduction | [OneDimensionalFineCubeFrame.lean](OneDimensionalFineCubeFrame.lean) |
| Vaaler--Selberg translated-cube lower frame | [TranslatedCubeFourier.lean](TranslatedCubeFourier.lean) |
| Translated centered-cube conversion | [BartonCubeFrame.lean](BartonCubeFrame.lean) |
| Open-endpoint Selberg lattice minorants and tensor correction | [LatticeSelbergMinorant.lean](LatticeSelbergMinorant.lean) |
| Integer phase periodicity and exact Lipschitz bounds | [PhaseEstimates.lean](PhaseEstimates.lean) |
| Finite torus grids, covering radius, and cardinality bounds | [FiniteTorusGrid.lean](FiniteTorusGrid.lean) |
| Concrete angular Vandermonde and subspace definitions | [ClusteredVandermonde.lean](ClusteredVandermonde.lean) |
| Constructive single-clump singular-value lower bound | [SingleClumpVandermonde.lean](SingleClumpVandermonde.lean) |
| Continuous companion generators and the uniform collision limit | [ExponentialCompanion.lean](ExponentialCompanion.lean) |
| Polynomial Markov, point-evaluation and coefficient-energy bounds | [PolynomialEvaluationBounds.lean](PolynomialEvaluationBounds.lean) |
| Sharper derivative-direction projection and triangular energy integration | [SharperPolynomialEvaluation.lean](SharperPolynomialEvaluation.lean) |
| Sonin energy bound for the shifted Legendre equation | [LegendreIntervalBounds.lean](LegendreIntervalBounds.lean) |
| Exact shifted Legendre orthogonality, norms and sharp polynomial point evaluation | [SharpPolynomialEvaluation.lean](SharpPolynomialEvaluation.lean) |
| Explicit Legendre coefficient-to-energy constants as finite binomial sums | [QuantitativePolynomialBounds.lean](QuantitativePolynomialBounds.lean) |
| Endpoint-inclusive polynomial grid lower bound with half-cell error | [QuantitativePolynomialGridBounds.lean](QuantitativePolynomialGridBounds.lean) |
| Exact Legendre derivative norms and complex polynomial $L^2$ derivative bounds | [QuantitativePolynomialL2Derivative.lean](QuantitativePolynomialL2Derivative.lean) |
| Companion first-row perturbation with the factorial denominator retained | [QuantitativeCompanionBounds.lean](QuantitativeCompanionBounds.lean) |
| Polynomial cross correlation from supremum derivative estimates | [QuantitativePolynomialCrossCorrelation.lean](QuantitativePolynomialCrossCorrelation.lean) |
| Abel summation, integral variation and size-dependent polynomial energy correlation | [QuantitativePolynomialVariationCrossCorrelation.lean](QuantitativePolynomialVariationCrossCorrelation.lean) |
| Explicit local perturbation and grid budgets, with finite size minima and maxima | [QuantitativeClumpSectionBounds.lean](QuantitativeClumpSectionBounds.lean) |
| Explicit angular section row, approximation, supremum and continuous-energy bounds | [QuantitativeAngularSectionBounds.lean](QuantitativeAngularSectionBounds.lean) |
| Uniform and size-dependent angular clump cross bounds | [QuantitativeClumpCrossCorrelation.lean](QuantitativeClumpCrossCorrelation.lean) |
| Weighted quadratic cross estimates and aggregate clump energy | [WeightedClumpCrossBounds.lean](WeightedClumpCrossBounds.lean) |
| Stability of the polynomial evaluation bound under uniform perturbations | [JetPolynomialPerturbation.lean](JetPolynomialPerturbation.lean) |
| Integer monomial moments, polynomial cross inner products and perturbations | [PolynomialCrossCorrelation.lean](PolynomialCrossCorrelation.lean) |
| Complex exponential sums, unit norms and elementary calculus | [ExponentialSums.lean](ExponentialSums.lean) |
| Riemann rectangles, derivative bounds and discrete coefficient control | [UniformGridEvaluationBounds.lean](UniformGridEvaluationBounds.lean) |
| Gap-free small-frequency pointwise and grid bounds with arbitrarily small relative losses; retained constants $24s^2$ and $512s^2$ | [SmallFrequencyEvaluationBounds.lean](SmallFrequencyEvaluationBounds.lean) |
| Exact column-span representation and modulated jet polynomial approximation | [ClumpJetApproximation.lean](ClumpJetApproximation.lean) |
| Gap-free angular section thresholds, including repeated coordinate projections | [AngularClumpSectionBounds.lean](AngularClumpSectionBounds.lean) |
| Integer phase separation and short-representative chord estimates | [SeparatedAngularFrequency.lean](SeparatedAngularFrequency.lean) |
| Multidimensional cardinal packets, cube averaging and diagonal interpolation energy | [MultidimensionalTrigonometricInterpolation.lean](MultidimensionalTrigonometricInterpolation.lean) |
| Box moment kernels, tensor Taylor remainders and collinear row estimates | [MultidimensionalTaylorBounds.lean](MultidimensionalTaylorBounds.lean) |

All frequencies in this chain are angular frequencies with period $2\pi$ and
phase $e^{ikx_j}$.

`hasFineCubeFrame_of_translatedCube` converts the proved translated-cube
Fourier-frame theorem into the manuscript's angular one-sided cube. The real
frequency cube is centered at `(N - 1) / 2` with radius `N / 2`, whose integer
points are exactly `{0, ..., N - 1}` for both parities of `N`.
`TranslatedCubeFourier.lean` proves the Barton minorant estimate from the
vendored Vaaler--Selberg and Poisson-summation results; `BartonCubeFrame.lean`
proves the normalization, periodic-distance scaling, and phase conversion.

The current multiclump lower-sampling path uses
`jetPolynomial_unit_row_bound_sharp`, which proves the exact constant $s^2$
for every complex polynomial of degree below $s$. The proof establishes
the shifted Legendre equation, interval bound, orthogonality and exact norms,
then applies weighted Cauchy--Schwarz to the finite basis expansion.
The public quantitative path chooses the section row factor
$q=1+1/(16d)$ and retains $\gamma=3/4$ of the sum of clump energies.
Since $q^d\le16/15$, coordinate iteration and the energy comparison give
global leverage at most $\tfrac32\sum_a n_a^{2d}$. The lower Chernoff tail
then yields the manuscript sampling coefficient $3$. The width, bandwidth
and interclump separation thresholds are explicit and selected independently;
they depend only on $d,n,n^\star$. The public assembly is
`cubeClump_quantitative_leverage_energy` in
[RandSamp/CubeClumpLeverage.lean](../../RandSamp/CubeClumpLeverage.lean), followed
by `multidimensionalMultiClump_lower_sampling_explicit` in
[RandSamp/MultidimensionalMultiClumpLowerSampling.lean](../../RandSamp/MultidimensionalMultiClumpLowerSampling.lean).

The quantitative polynomial modules prove the explicit jet constant

$$
J_s^2=\max_{0\le j\le s}(j!)^2
\sum_{r=0}^{s-1}(2r+1)\binom rj^2\binom{r+j}{r}^2,
$$

including the extra zero row $j=s$. This controls the supremum norm of the
jet coefficient vector by $J_s$ times the square root of the continuous
polynomial energy. The companion first-row error is
$2(s+1)r\|a\|/s!$ for root radius $r\le1/(2s)$, and the endpoint-inclusive
polynomial grid lower bound is

$$
\sum_{k=0}^M|p(k/M)|^2
\ge [M-4(s-1)^2s^2]\int_0^1|p(t)|^2\,dt.
$$

For complex polynomials of degree below $s$, the exact Legendre derivative
norms also give

$$
\|p'\|_{L^2(0,1)}\le s\sqrt{s^2-1}\,\|p\|_{L^2(0,1)}.
$$

Abel summation bounds the modulated discrete polynomial cross inner product
by endpoint values and the integral variation of the product. For degrees
below $s,t$ and periodic angular separation $\eta$, its coefficient is
$\pi[st+(s^2+t^2)/2]/\eta$. The uniform coefficient for $s,t\le n^\star$ is
$\pi[(n^\star)^2+n^\star\sqrt{(n^\star)^2-1}]/\eta$.
`WeightedClumpCrossBounds.lean` retains the individual clump sizes in the
global estimate, whose moment coefficient is

$$
\sum_a n_a^2+\sqrt{A\sum_a n_a^4}
\le nn^\star+\sqrt{(n-n^\star+1)n(n^\star)^3}.
$$

The moment comparison is proved in
[RandSamp/ClumpMomentBounds.lean](../../RandSamp/ClumpMomentBounds.lean).
`quantitativeClumpSeparation` selects the smaller of the resulting pairwise
and weighted global thresholds. The single-clump separation threshold is
zero. `quantitativeClumpRadius` is a finite minimum of local companion
radii, and `quantitativeClumpBandwidth` is the maximum of $n$, $16n^\star$
and the finite local grid thresholds.

The stronger bandwidth estimate permits the public spectral lower bound to
retain `multidimensionalClumpOptimizedLowerConstant` with three-quarter clump
energy; this comparison is proved in
[RandSamp/MultidimensionalClumpQuantitativeSingularBounds.lean](../../RandSamp/MultidimensionalClumpQuantitativeSingularBounds.lean).
All polynomial, angular and cube conversions are fully proved. Earlier
existential geometry interfaces, the $9/10$ energy assembly, the polynomial
constant $12$ and the grid constant $24s^2$ remain available as separate
supporting results.
