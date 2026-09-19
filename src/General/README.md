# General

Reusable analysis and algebra for the NumDetect formalization. These modules do
not import the theorem-specific `SegmentedVDM` directory.

## Library map

| Directory | Scope |
| --- | --- |
| [Finite](Finite/README.md) | Finite sums, node sorting, and periodic geometry |
| [Fourier](Fourier/README.md) | Parseval identities, cosine windows, and separated sampling |
| [MatrixAnalysis](MatrixAnalysis/README.md) | Gram matrices, singular values, pseudoinverses, and Hermitian variational tools |
| [SpectralPerturbation](SpectralPerturbation/README.md) | Eigenvalue enumeration, resolvent discs, and perturbation matching |

The initial import is deliberately scoped to the dependency closure of the
segmented Vandermonde proof plus matrix and spectral tools expected to support
the manuscript's thresholding and MUSIC arguments. Unrelated Two-Scale-specific
HCIZ, Schur, Haar, and representation-theory modules were not copied.

General declarations use the `LeanNumDetect` namespace:

```lean
import General.MatrixAnalysis.MoorePenrose
import General.SpectralPerturbation.SpectralVariation

open LeanNumDetect
```

All results in this directory are proved; `sorry` is not permitted. Future
unproved original external results must be registered under
[External](../External/README.md).
