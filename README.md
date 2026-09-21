# LeanNumDetect

Lean formalization of the generalized Hankel/Toeplitz, source-number detection,
segmented Vandermonde, and MUSIC results in the NumDetect manuscript.

## Current coverage

[NumDetect](src/NumDetect/README.md) contains the definitions and
principal theorem formalizations for generalized Hankel/Toeplitz matrices,
source-number detection, contiguous and segmented Vandermonde bounds, random
sampling, and MUSIC stability. Its aggregate import is
`NumDetect.Main`.

The repository also contains a proved one-dimensional specialization of the
manuscript's segmented Vandermonde bound. Its primary entry point is
`SegmentedVDM.small_clumps_singularValue` in
[PaperTheorem.lean](src/SegmentedVDM/PaperTheorem.lean).

The repository also carries the reusable dependency chain for this theorem and
selected matrix and spectral tools:

| Directory | Purpose |
| --- | --- |
| [SegmentedVDM](src/SegmentedVDM/README.md) | One-dimensional segmented Vandermonde construction and singular-value bound |
| [NumDetect](src/NumDetect/README.md) | Manuscript definitions and principal theorem statements, organized as flat, prefixed module groups |
| [General/Fourier](src/General/Fourier/README.md) | Cosine-window, Parseval, and separated-sampling estimates |
| [General/MatrixAnalysis](src/General/MatrixAnalysis/README.md) | Gram, singular-value, pseudoinverse, and variational tools |
| [General/SpectralPerturbation](src/General/SpectralPerturbation/README.md) | Eigenvalue enumeration and perturbation matching |
| [General/Finite](src/General/Finite/README.md) | Finite sorting, sums, and periodic geometry |
| [External](src/External/README.md) | Admission policy and the single translated-cube Fourier-frame input |

The imported formalization and repository infrastructure come from
`LeanTwoScale` commit `5b1241a`. The manuscript base currently audited by the
formalization is NumDetect commit `42c1be5`, including the translated-cube
correction in `main.tex`.

## Build and verify

The project pins Lean 4.32.0 and mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`. It reuses the shared mathlib
checkout at `~/.local/share/lean/mathlib4-v4.32.0`.

```sh
python3 .github/ci/setup_mathlib.py --verify
lake build
python3 .github/ci/check.py
```

The final command compiles every Lean source file and rejects proof admissions
outside `src/External/` as well as project axioms. Only registered original
results may remain admitted under `src/External/`; the current registry contains
the translated-cube Fourier-frame estimate used by the segmented theorem. See
[the CI guide](.github/ci/README.md) and [AGENTS.md](AGENTS.md) for details.
