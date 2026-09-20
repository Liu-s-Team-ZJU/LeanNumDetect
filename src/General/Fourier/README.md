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
| Centered-cube algebra and signed-weight reduction | [SeparatedCubeFourierInternal.lean](SeparatedCubeFourierInternal.lean) |
| Continuous cube minorant/majorant reduction | [SeparatedCubeFourierContinuous.lean](SeparatedCubeFourierContinuous.lean) |
| Centered-to-one-sided cube conversion infrastructure | [FineCubeFrame.lean](FineCubeFrame.lean) |
| One-dimensional periodic-Hilbert reduction | [OneDimensionalFineCubeFrame.lean](OneDimensionalFineCubeFrame.lean) |
| Parity-free shifted-coset cube conversion | [BartonCubeFrame.lean](BartonCubeFrame.lean) |

All frequencies in this chain are angular frequencies with period $2\pi$ and
phase $e^{ikx_j}$.

The separated-cube reduction modules do not assume Li's Theorem 2.3. In one
dimension, `hasFineCubeFrame_oneDimensional` derives the full manuscript
constant and parameter range from `HasPeriodicHilbertSineBound`, the sharp
periodic Montgomery--Vaughan inequality used by Aubel--Bölcskei. In higher
dimensions, `hasFineCubeFrame_of_bartonShiftedCoset` handles every parity of
`K + 1` and isolates the remaining Barton--Fejer input as
`HasBartonShiftedCosetLowerFrame`.

These propositions are not asserted as axioms or admitted theorems. The sharp
periodic Hilbert inequality, the Beurling--Selberg/Barton extremal functions,
and the required multidimensional shifted Fejer--Poisson convergence theorem
are not available in Mathlib or in a public Lean formalization.
