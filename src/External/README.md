# External result registry

There are currently **no admitted external results**. Both exact matrix Chernoff
tails are fully proved in [General/Probability/MatrixChernoff.lean](../General/Probability/MatrixChernoff.lean),
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
and scalar Laplace optimization. These results and the final one-dimensional
and higher-dimensional RandSamp theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

[RandSamp/Audit.lean](../RandSamp/Audit.lean) rejects every admission or project
axiom in its imported project dependencies, including this directory. The
repository's general source-attribution requirements remain documented in
[AGENTS.md](../../AGENTS.md).
