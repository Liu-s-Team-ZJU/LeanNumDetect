# Matrix analysis

This directory contains finite-dimensional tools used by the segmented
Vandermonde proof and selected interfaces likely to support NumDetect's
thresholding and MUSIC arguments.

| Module | Main role |
| --- | --- |
| [MatrixReduction.lean](MatrixReduction.lean) | Gram quadratic forms, eigenvalue bounds, Vandermonde injectivity, and block Gram estimates |
| [RowDeletion.lean](RowDeletion.lean) | Singular values, Gram eigenvectors, and row/block deletion estimates |
| [GramFromBasis.lean](GramFromBasis.lean) | Positive-definite Gram matrices from orthonormal ranges |
| [MoorePenrose.lean](MoorePenrose.lean) | Moore-Penrose inverse at arbitrary rank, uniqueness, Gram formula, and unitary covariance |
| [HermitianVariational.lean](HermitianVariational.lean) | Finite-dimensional Courant-Fischer and Hermitian eigenvalue bounds |
| [SingularValueBounds.lean](SingularValueBounds.lean) | Singular-value product, perturbation, and variational estimates |
| [Coherence.lean](Coherence.lean) | Gershgorin bounds for all singular values and action energies from unit columns and bounded off-diagonal Gram entries |
| [GramPerturbation.lean](GramPerturbation.lean) | Exact additive singular-value and energy bounds from equal Gram diagonals and bounded off-diagonal differences |
| [SpectralInterval.lean](SpectralInterval.lean) | Exact equivalence between extremal singular-value intervals and uniform energy bounds for arbitrary finite row and column indices |
| [Reindex.lean](Reindex.lean) | Preservation of every singular value under row and column bijections |
| [MUSICSubspacePerturbation.lean](MUSICSubspacePerturbation.lean) | Proved fixed-rank perturbation bound for trailing left singular subspaces |
| [TraceExponential.lean](TraceExponential.lean) | Spectral expansion, Jensen, convexity, and detection of Rayleigh events by the trace exponential |
| [TraceExponentialBounds.lean](TraceExponentialBounds.lean) | PSD exponential chord and weighted trace bounds |
| [GoldenThompsonDyadic.lean](GoldenThompsonDyadic.lean) | Finite dyadic Hölder and Hermitian trace inequalities |
| [LieTrotter.lean](LieTrotter.lean) | Banach-algebra Lie--Trotter product formula |
| [GoldenThompson.lean](GoldenThompson.lean) | Complete Golden--Thompson trace inequality for finite complex Hermitian matrices |
| [FiniteFrameGram.lean](FiniteFrameGram.lean) | Rank-one frame populations, quadratic forms and weighted trace identities |
| [InverseMetric.lean](InverseMetric.lean) | Inverse order, whitening, and the metric Cauchy--Schwarz row bound |
| [PositiveDefiniteDeterminant.lean](PositiveDefiniteDeterminant.lean) | Real determinant, logarithmic spectral identities, whitening, and relative log-determinant bounds |
| [CappedRowLeverage.lean](CappedRowLeverage.lean) | Standalone inverse-metric row bounds in the capped-weight namespace |
| [CappedWeightIteration.lean](CappedWeightIteration.lean) | Determinant floors and a finite noncontracting update for capped covariance iteration |
| [CappedWeightMap.lean](CappedWeightMap.lean) | Monotone capped covariance and entropy descent |
| [CappedWeightSequence.lean](CappedWeightSequence.lean) | Standalone finite capped-weight construction from a determinant floor |
| [LogDetDirectionalDerivative.lean](LogDetDirectionalDerivative.lean) | Jacobi derivative of the determinant and real log determinant along affine matrix directions |
| [SmoothFrameStationarity.lean](SmoothFrameStationarity.lean) | First-order condition at a smooth frame-potential minimum and the resulting weighted covariance identity |
| [FrameLogDetMean.lean](FrameLogDetMean.lean) | Hadamard logarithmic determinant lower bounds from quantitatively independent rows and averaging over translated row sets |
| [ShiftedLogDetSpectrum.lean](ShiftedLogDetSpectrum.lean) | Spectral sum formula for the logarithmic determinant of a positive scalar shift of a positive-definite matrix |

`matrixSingularValue` uses zero-based indices, so index `n - 1` denotes the
smallest singular value of a full-column-rank matrix with `n` columns.

All declarations are fully proved and live under the `LeanNumDetect` namespace.
Frame Gram, inverse-metric and positive-definite determinant tools are in
`LeanNumDetect.FrameMatrixBounds`.

The capped-weight modules remain reusable alongside the direct smooth
variational construction. The current random-clump sampling theorem uses
`FrameMatrixBounds`, the logarithmic determinant average, and
`SmoothFrameStationarity`; its strict audit checks the actual dependency chain.
