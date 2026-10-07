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

The fixed multiclump theorem's needed pointwise, integer-grid, clump-subspace
and smallest-singular-value estimates are proved directly in
[General/Fourier](../General/Fourier/README.md), with exact conversions in
[RandSamp](../RandSamp/README.md). Its absolute sampling constant is 3072.
These are sufficient consequences proved for the manuscript's geometry;
the unrestricted original literature theorems and their sharper constants
are not claimed as formalized. The former `ExponentialSumEstimates` and
`ClusteredVandermonde` external modules have been removed.

[RandSamp/Audit.lean](../RandSamp/Audit.lean),
[RandSamp/OffGridAudit.lean](../RandSamp/OffGridAudit.lean) and
[RandSamp/MultiClumpAudit.lean](../RandSamp/MultiClumpAudit.lean) reject imported
project admissions and project axioms. Their final results use only
`propext`, `Classical.choice` and `Quot.sound`.

Source-attribution requirements are also documented in
[AGENTS.md](../../AGENTS.md). The current user instruction and CI policy
require complete proofs everywhere, including formerly external results.
