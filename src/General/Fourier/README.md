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

All frequencies in this chain are angular frequencies with period $2\pi$ and
phase $e^{ikx_j}$.

`hasFineCubeFrame_of_translatedCube` converts the proved translated-cube
Fourier-frame theorem into the manuscript's angular one-sided cube. The real
frequency cube is centered at `(N - 1) / 2` with radius `N / 2`, whose integer
points are exactly `{0, ..., N - 1}` for both parities of `N`.
`TranslatedCubeFourier.lean` proves the Barton minorant estimate from the
vendored Vaaler--Selberg and Poisson-summation results; `BartonCubeFrame.lean`
proves the normalization, periodic-distance scaling, and phase conversion.
