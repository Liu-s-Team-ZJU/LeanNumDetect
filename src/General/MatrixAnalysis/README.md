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
| [MUSICSubspacePerturbation.lean](MUSICSubspacePerturbation.lean) | Proved fixed-rank perturbation bound for trailing left singular subspaces |
| [TraceExponential.lean](TraceExponential.lean) | Spectral expansion, Jensen, convexity, and detection of Rayleigh events by the trace exponential |
| [TraceExponentialBounds.lean](TraceExponentialBounds.lean) | PSD exponential chord and weighted trace bounds |
| [GoldenThompsonDyadic.lean](GoldenThompsonDyadic.lean) | Finite dyadic Hölder and Hermitian trace inequalities |
| [LieTrotter.lean](LieTrotter.lean) | Banach-algebra Lie--Trotter product formula |
| [GoldenThompson.lean](GoldenThompson.lean) | Complete Golden--Thompson trace inequality for finite complex Hermitian matrices |

`matrixSingularValue` uses zero-based indices, so index `n - 1` denotes the
smallest singular value of a full-column-rank matrix with `n` columns.

All declarations are fully proved and live in the `LeanNumDetect` namespace.
