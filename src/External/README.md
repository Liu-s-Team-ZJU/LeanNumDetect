# External result registry

The following original external result is admitted. Its reusable conversions
must be fully proved outside this directory.

| File | Original source and location | Lean declaration |
| --- | --- | --- |
| [BoundedRieszConcentration.lean](BoundedRieszConcentration.lean) | S. Brugiapaglia, S. Dirksen, H. C. Jung, and H. Rauhut, *Sparse recovery in bounded Riesz systems with applications to numerical methods for PDEs*, Applied and Computational Harmonic Analysis 53 (2021), 231–269; [Theorem 1.1, manuscript p. 2](https://arxiv.org/pdf/2005.06994) | `LeanNumDetect.BoundedRieszConcentration.boundedRows_concentration` |

The statement retains arbitrary complex bounded row distributions, independent
identically distributed random samples on arbitrary probability spaces, arbitrary
target subsets of an ℓ¹ ball, all three universal constants, and the original
sample rate, deviation, and strict success-probability inequality. It assumes no
Riesz bound, isotropy, orthogonality, finite population, or particular dictionary.

Both exact matrix Chernoff tails are fully proved in
[General/Probability/MatrixChernoff.lean](../General/Probability/MatrixChernoff.lean),
and the former `External.MatrixChernoff` module has been removed.

| Fully proved result | Original source | Lean declaration |
| --- | --- | --- |
| Lower matrix Chernoff tail, without replacement | J. A. Tropp, *Improved analysis of the subsampled randomized Hadamard transform* (2011), [Theorem 2.2, p. 4](https://arxiv.org/pdf/1011.1595) | `LeanNumDetect.FiniteMatrixSampling.matrixChernoff_withoutReplacement_lower` |
| Upper matrix Chernoff tail, without replacement | Same source, Theorem 2.2 | `LeanNumDetect.FiniteMatrixSampling.matrixChernoff_withoutReplacement_upper` |

The statements preserve the exact Chernoff factors, full parameter ranges,
labelled populations (including repeated values), uniform sampling without
replacement, and extreme eigenvalues expressed through Rayleigh values.

The complete proof includes finite convex comparison, the Golden--Thompson
inequality, the Lie--Trotter product formula, spectral exponential bounds,
and scalar Laplace optimization. These results and the earlier one-dimensional
and higher-dimensional RandSamp theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

[RandSamp/Audit.lean](../RandSamp/Audit.lean) rejects every admission or project
axiom in its imported project dependencies, including this directory. The
new off-grid probability results instead have an explicit dependency on the
original bounded-row theorem above. Their separate
[RandSamp/OffGridAudit.lean](../RandSamp/OffGridAudit.lean) permits that one named
direct admission and rejects every other imported project admission or axiom;
the deterministic steps and all conversions are proved without admissions.
The new final probability theorems have a transitive `sorryAx` dependency
through the registered original theorem.

The repository's general source-attribution requirements remain documented in
[AGENTS.md](../../AGENTS.md).
