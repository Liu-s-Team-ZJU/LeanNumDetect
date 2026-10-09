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
| [Sharp unit-interval polynomial evaluation](../General/Fourier/SharpPolynomialEvaluation.lean) and [Legendre interval bound](../General/Fourier/LegendreIntervalBounds.lean) | NIST DLMF, [Table 18.3.1](https://dlmf.nist.gov/18.3#T1) (shifted Legendre orthogonality and norms), [18.14.1](https://dlmf.nist.gov/18.14.E1) (the Legendre interval bound, $\alpha=\beta=0$); the point-evaluation consequence follows by finite expansion and Cauchy--Schwarz | `LeanNumDetect.PolynomialEvaluationBounds.jetPolynomial_unit_row_bound_sharp` |

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

The fixed multiclump theorem's pointwise, integer-grid, clump-subspace and
smallest-singular-value estimates are proved directly in
[General/Fourier](../General/Fourier/README.md), with exact conversions in
[RandSamp](../RandSamp/README.md). The current public NumDetect interface is
`multidimensionalMultiClump_lower_sampling_explicit` in
[MultidimensionalMultiClumpLowerSampling.lean](../RandSamp/MultidimensionalMultiClumpLowerSampling.lean).
Its width, bandwidth and interclump separation thresholds are explicit
functions of $d,n,n^\star$, chosen independently. The section factor is
$q=1+1/(16d)$ and the clump energy factor is $\gamma=3/4$. The global
leverage radius is at most $\tfrac32\sum_a n_a^{2d}$, giving

$$
m\ge\frac{3}{\rho^2}\left(\sum_a n_a^{2d}\right)\log\frac n\epsilon.
$$

The exact complex Legendre polynomial estimate, finite binomial coefficient
energy bounds, factorial companion remainder and half-cell grid estimate
are fully proved in `General`. The additional proved modules are:

| Quantitative proof component | Module |
| --- | --- |
| Exact derivative energy and $\|p'\|_2\le s\sqrt{s^2-1}\|p\|_2$ | [QuantitativePolynomialL2Derivative.lean](../General/Fourier/QuantitativePolynomialL2Derivative.lean) |
| Abel summation and integral-variation cross estimates | [QuantitativePolynomialVariationCrossCorrelation.lean](../General/Fourier/QuantitativePolynomialVariationCrossCorrelation.lean) |
| Explicit local radii, grid budgets and independent geometry thresholds | [QuantitativeClumpSectionBounds.lean](../General/Fourier/QuantitativeClumpSectionBounds.lean) |
| Angular section and clump cross conversions | [QuantitativeAngularSectionBounds.lean](../General/Fourier/QuantitativeAngularSectionBounds.lean), [QuantitativeClumpCrossCorrelation.lean](../General/Fourier/QuantitativeClumpCrossCorrelation.lean) |
| Weighted global energy and clump moment bounds | [WeightedClumpCrossBounds.lean](../General/Fourier/WeightedClumpCrossBounds.lean), [ClumpMomentBounds.lean](../RandSamp/ClumpMomentBounds.lean) |
| Three-quarter energy spectral conversion retaining the original lower constant | [MultidimensionalClumpQuantitativeSingularBounds.lean](../RandSamp/MultidimensionalClumpQuantitativeSingularBounds.lean) |

The separation threshold is the minimum of the pairwise and weighted global
correlation thresholds; the single-clump threshold is zero. The additional
bandwidth preserves the public spectral coefficient

$$
C(d,n^\star)=\frac{3}{\sqrt{10n^\star}\,2^{n^\star-1}\sqrt{2^d}
(3n^\star d)^{n^\star-1}}.
$$

These refinements are proved consequences of the Legendre and elementary
Fourier identities above, with no additional external assumptions.
The earlier existential geometry and $9/10$ energy interfaces remain as
separate supporting results. The older independent two-sided
cube theorem retains constant $3072\,512^{d-1}$ and logarithm
$\log(2n/\epsilon)$; its exact dimension-one constant is 3072.
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
