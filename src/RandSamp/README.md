# RandSamp

This directory formalizes the nonuniform Fourier--Vandermonde estimate used in
the random-sampling section of the NumDetect manuscript. Import
[Main.lean](Main.lean) for the complete interface.

## Main result

| Manuscript result | Exact Lean location |
| --- | --- |
| Nonuniform VDM scaling (`thm:nonuniform_vdm_scaling`) | [NonuniformVandermonde.lean](NonuniformVandermonde.lean): theorem `nonuniformVandermonde_minimumSingularValue` |

The theorem treats an arbitrary injective $M$-row frequency family and defines
its order-$n$ sampling spread as the largest minimum spacing among all $n$-row
selections. For a cluster satisfying $|y_j-y_0|\leq\tau\Delta/2$, the explicit
remainder-control hypothesis yields

$$
\sigma_{\min}(V) \geq \frac12 c(n)(\gamma\Delta)^{n-1},
$$

where `nonuniformVandermondeConstant n` is positive and depends only on $n$.

## Proof organization

| Module | Role |
| --- | --- |
| [SquareVandermonde.lean](SquareVandermonde.lean) | Lagrange inverse and quantitative lower bound for normalized square power Vandermonde matrices |
| [TaylorFactorization.lean](TaylorFactorization.lean) | Frequency and source Taylor factors, exponential remainder, raw bound, and explicit $n$-dependent constant |
| [NonuniformVandermonde.lean](NonuniformVandermonde.lean) | Translation invariance, sampling spread and its maximizing row selection, and the manuscript-facing theorem |
| [Main.lean](Main.lean) | Aggregate public import |

All estimates are proved in Lean. In particular, the Lagrange coefficient
bound, Taylor remainder, row-selection monotonicity, and translation from a
centered cluster are not introduced as assumptions.
