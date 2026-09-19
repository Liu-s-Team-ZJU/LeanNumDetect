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

`matrixSingularValue` uses zero-based indices, so index `n - 1` denotes the
smallest singular value of a full-column-rank matrix with `n` columns.

All declarations are fully proved and live in the `LeanNumDetect` namespace.
