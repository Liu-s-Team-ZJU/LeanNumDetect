# Spectral perturbation

This directory proves eigenvalue matching for an arbitrary complex perturbation of a diagonal matrix, retaining every eigenvalue's algebraic multiplicity. The entry point is `LeanNumDetect.diagonal_perturbation_spectral_matching` in [SpectralVariation.lean](SpectralVariation.lean).

For $a,z:\operatorname{Fin}n\to\mathbb C$, a complex matrix $G$, and an enumeration $z$ of the eigenvalues of $\operatorname{diag}(a)+G$, the theorem produces a permutation $\sigma$ such that

$$
\|a_i-z_{\sigma(i)}\|\le(2n-1)\|G\|\qquad\text{for every }i.
$$

The matrix norm is the Euclidean operator norm (`Matrix.Norms.L2Operator`). There is no separation assumption on $a$, no diagonalizability assumption on the perturbed matrix, and no restriction on the perturbation size. Repeated eigenvalues are included through `EigenvalueEnumeration`, which records equality with the characteristic polynomial's root multiset.

## Proof organization

| Module | Role |
| --- | --- |
| [PolynomialRootMatching.lean](PolynomialRootMatching.lean) | `rootProduct` and `rootProduct_homotopy_matching`: root multiplicities stay within separated groups along a continuous polynomial homotopy; equal finite root multisets give a permutation |
| [SpectralEnumeration.lean](SpectralEnumeration.lean) | `EigenvalueEnumeration`, existence for every complex square matrix, invariance under similarity, and characteristic-polynomial factorization over the complete eigenvalue list |
| [SpectralDiscs.lean](SpectralDiscs.lean) | `diagonal_perturbation_root_disc`: the diagonal resolvent and a Neumann-series argument put each perturbed root in a disc of radius $\|G\|$ |
| [SpectralDiscMatching.lean](SpectralDiscMatching.lean) | The intersection graph of equal-radius discs; simple paths have at most $n-1$ edges, giving the matching factor $2n-1$ |
| [SpectralVariation.lean](SpectralVariation.lean) | Applies the root-matching and disc results to the homotopy $\operatorname{diag}(a)+tG$, $0\le t\le1$ |

The source identifies the final estimate as the Euclidean-norm specialization of Stewart–Sun, *Matrix Perturbation Theory*, IV.3.3, using the spectral-disc grouping argument of IV.1.5. The intervening enumeration, continuity, disc containment, and multiplicity arguments are proved in these modules.

For related singular-value and Gram estimates, see [Matrix analysis](../MatrixAnalysis/README.md). Return to the [General index](../README.md).
