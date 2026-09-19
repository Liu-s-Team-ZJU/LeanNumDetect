# LeanNumDetect

Lean formalization of the generalized Hankel/Toeplitz, source-number detection,
segmented Vandermonde, and MUSIC results in the NumDetect manuscript.

## Current coverage

[NumDetectMain](src/NumDetectMain/README.md) contains the definitions and
principal theorem formalizations for generalized Hankel/Toeplitz matrices,
source-number detection, contiguous and segmented Vandermonde bounds, random
sampling, and MUSIC stability. Its aggregate import is
`NumDetectMain.Main`.

The repository also contains a proved one-dimensional specialization of the
manuscript's segmented Vandermonde bound. Its primary entry point is
`SegmentedVDM.small_clumps_singularValue` in
[PaperTheorem.lean](src/SegmentedVDM/PaperTheorem.lean).

The repository also carries the reusable dependency chain for this theorem and
selected matrix and spectral tools likely to be needed next:

| Directory | Purpose |
| --- | --- |
| [SegmentedVDM](src/SegmentedVDM/README.md) | One-dimensional segmented Vandermonde construction and singular-value bound |
| [NumDetectMain](src/NumDetectMain/README.md) | Manuscript definitions and principal theorem statements |
| [General/Fourier](src/General/Fourier/README.md) | Cosine-window, Parseval, and separated-sampling estimates |
| [General/MatrixAnalysis](src/General/MatrixAnalysis/README.md) | Gram, singular-value, pseudoinverse, and variational tools |
| [General/SpectralPerturbation](src/General/SpectralPerturbation/README.md) | Eigenvalue enumeration and perturbation matching |
| [General/Finite](src/General/Finite/README.md) | Finite sorting, sums, and periodic geometry |
| [External](src/External/README.md) | Registry for original external results not yet formalized |

The imported formalization and repository infrastructure come from
`LeanTwoScale` commit `5b1241a`. The manuscript inspected during initialization
was NumDetect commit `a5046fc`.

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
results may remain admitted under `src/External/`. See
[the CI guide](.github/ci/README.md) and [AGENTS.md](AGENTS.md) for details.
