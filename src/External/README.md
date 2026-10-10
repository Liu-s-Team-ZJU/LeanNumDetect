# Source-attribution registry

This directory contains no Lean source files and no admitted results.
All required analytic and probabilistic proofs are in `src/General/`;
their project-specific conversions are in `src/RandSamp/`. Repository-wide
CI rejects every project admission or project axiom and rejects Lean source
files in this directory.

| Fully proved result and module | Original source and location | Lean declaration |
| --- | --- | --- |
| [Arbitrary-law bounded-row concentration](../General/Probability/BoundedRieszConcentration.lean) | S. Brugiapaglia, S. Dirksen, H. C. Jung and H. Rauhut, *Sparse recovery in bounded Riesz systems with applications to numerical methods for PDEs*, Applied and Computational Harmonic Analysis 53 (2021), 231–269; [Theorem 1.1, manuscript p. 2](https://arxiv.org/pdf/2005.06994) | `LeanNumDetect.BoundedRieszConcentration.boundedRows_concentration` |
| [Lower matrix Chernoff tail without replacement](../General/Probability/MatrixChernoff.lean) | J. A. Tropp, *Improved analysis of the subsampled randomized Hadamard transform* (2011), [Theorem 2.2, p. 4](https://arxiv.org/pdf/1011.1595) | `LeanNumDetect.FiniteMatrixSampling.matrixChernoff_withoutReplacement_lower` |
| [Upper matrix Chernoff tail without replacement](../General/Probability/MatrixChernoff.lean) | Same source, Theorem 2.2 | `LeanNumDetect.FiniteMatrixSampling.matrixChernoff_withoutReplacement_upper` |
| [Angular full-cube clump bound](../NumDetect/LiCubeClumpBounds.lean) | W. Li, *Nonharmonic multivariate Fourier transforms and matrices: condition numbers and hyperplane geometry*, ACHA 79 (2025), 101791; [Corollary 3.12](https://arxiv.org/html/2407.10313v2#S3), even-bandwidth angular specialization. The public source covers $d\ge2$; the proof in this project also covers $d=1$. | `LeanNumDetect.NumDetect.liCubeClumpVandermonde_normalized_lower` |

The bounded-row statement retains arbitrary complex bounded distributions,
independent identically distributed samples on arbitrary probability spaces,
arbitrary subsets of the coordinate $\ell^1$ ball, positive real sparsity
radii, the original literal sampling rate and deviation, and the strict
success-probability inequality. Its proof chooses universal constants
$\kappa=1$, $c_0=10^{12}$ and $c_1=178$. Causal weak atomic nets, explicit
exceptional-row energy, finite-prefix entropy, weighted symmetrization,
replacement entropy, finite coefficient approximation and measurable row
quantization are all proved. No finite-law or finite-target hypothesis
is inserted into the original theorem.

Both Chernoff statements preserve their exact factors, full parameter ranges,
labelled populations with repeated values, uniform sampling without
replacement, and extreme eigenvalues expressed through Rayleigh values.
The complete proof includes finite convex comparison, Golden--Thompson,
Lie--Trotter, spectral exponential bounds and scalar Laplace optimization.

The independent legacy two-sided multiclump cube theorem remains fully
proved in [RandSamp](../RandSamp/README.md), using the pointwise, integer-grid
and clump-subspace estimates in [General/Fourier](../General/Fourier/README.md).
It retains sampling constant $3072\,512^{d-1}$ and logarithm
$\log(2n/\epsilon)$; its exact dimension-one constant is 3072.
The former `ExponentialSumEstimates` and `ClusteredVandermonde` external
modules have been removed.

[RandSamp/Audit.lean](../RandSamp/Audit.lean),
[RandSamp/OffGridAudit.lean](../RandSamp/OffGridAudit.lean) and
[RandSamp/MultiClumpAudit.lean](../RandSamp/MultiClumpAudit.lean) reject imported
project admissions and project axioms. Their final results use only
`propext`, `Classical.choice` and `Quot.sound`.

Source-attribution requirements are also documented in
[AGENTS.md](../../AGENTS.md). The current user instruction and CI policy
require complete proofs everywhere, including formerly external results.

The Li specialization is proved in full from the existing localization,
within-clump interpolation, finite-cube frame, and singular-value tools.
It contains no admitted external statement. The exact geometric predicate
is `LiCubeClumpGeometry`; its diameter parameter is an adjustable upper
bound, rather than a required positive lower bound on the actual diameter.
The bandwidth-independent coefficient is proved in
`liCubeClumpVandermonde_normalized_uniform_lower`. The deterministic bound
is combined with the separate finite-frame sampling route in
[CubeWeakLowerSampling.lean](../RandSamp/CubeWeakLowerSampling.lean); no
random concentration assertion is attributed to Li's deterministic corollary.
