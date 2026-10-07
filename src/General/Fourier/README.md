# Fourier analysis and sampling

This directory contains the proved Fourier dependency chain used by the
segmented Vandermonde formalization. Its main entry point is
`LeanNumDetect.separated_sampling_half`.

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
| Stability of the polynomial evaluation bound under uniform perturbations | [JetPolynomialPerturbation.lean](JetPolynomialPerturbation.lean) |
| Integer monomial moments, polynomial cross inner products and perturbations | [PolynomialCrossCorrelation.lean](PolynomialCrossCorrelation.lean) |

| Complex exponential sums, unit norms and elementary calculus | [ExponentialSums.lean](ExponentialSums.lean) |
| Riemann rectangles, derivative bounds and discrete coefficient control | [UniformGridEvaluationBounds.lean](UniformGridEvaluationBounds.lean) |
| Gap-free small-frequency pointwise and grid bounds with constant $512s^2$ | [SmallFrequencyEvaluationBounds.lean](SmallFrequencyEvaluationBounds.lean) |
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
