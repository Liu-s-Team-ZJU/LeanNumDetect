# Finite sums and geometry

This directory collects finite-sum estimates, permutations that sort distinct
real nodes, and periodic-to-real lifts. Its `LeanNumDetect` interfaces supply
discrete steps used by the segmented Vandermonde proof and future geometric
reductions.

| Module | Entry points and role |
| --- | --- |
| [FiniteSums.lean](FiniteSums.lean) | `traceless_sum_sq_le`, `sum_sq_sq_le_card_mul_sum_fourth`, positivity of square sums, telescoping products, product-to-sum bounds, sums of odd integers, and `sum_endpoint_bound` |
| [FiniteSorting.lean](FiniteSorting.lean) | `exists_strictMono_reordering`: an injective finite real node family admits a strictly increasing permutation |
| [FiniteRealGeometry.lean](FiniteRealGeometry.lean) | `finite_nodes_enclosing_diameter` and the singleton case; `exists_periodic_gap_le_pi` and `periodic_separation_lt_half` for period $2\pi$ |
| [PeriodicClumpLift.lean](PeriodicClumpLift.lean) | `periodic_clump_lift`: choose real representatives of a sufficiently short periodic clump without increasing its diameter bound |

## Geometry and grid assumptions

`periodic_clump_lift` takes a nonempty family $x:\operatorname{Fin}q\to\mathbb R$, a width $w\ge0$ satisfying $3w<2\pi$, and a periodic distance bound

$$
\forall i,j,\quad\exists p\in\mathbb Z,\quad |x_i-x_j-2\pi p|\le w.
$$

It produces integers $p_j$ such that the real representatives $x_j-2\pi p_j$ have diameter at most $w$. The proof chooses representatives near one reference node and uses $3w<2\pi$ to rule out a nonzero wrap between any pair. The finite-diameter enclosure separately requires $q>0$; sorting requires injectivity.

These finite counting and geometric steps are proved in Lean. See
[Matrix analysis](../MatrixAnalysis/README.md) for related finite-dimensional
linear algebra, or return to the [General index](../README.md).
