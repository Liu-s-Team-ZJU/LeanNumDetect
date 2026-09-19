# SegmentedVDM

This directory proves a one-dimensional specialization of NumDetect's
`thm:segmented-vandermonde`. It does not formalize the manuscript's
arbitrary-dimensional theorem. Use the stable LaTeX label rather than a theorem
number to identify the result.

## Results and entry points

Import `SegmentedVDM.PaperTheorem` for `SegmentedVDM.small_clumps_singularValue`, which proves

$$
\sigma_n(\mathcal V_{m,M,D}(\mathcal X))\ge
(2-\sqrt e)^{s/2}\sqrt{\frac{M(\lfloor m/2\rfloor+1)}{ns}}
\left(\frac{\sqrt2 MD\delta}{s}\right)^{s-1}.
$$

The rows are indexed by
$(j,h)\in\{0,\ldots,M\}\times\{0,\ldots,m\}$, with entries
$e^{i(jD+h)x_k}$. Singular values use zero-based indices, so the smallest
column singular value is `matrixSingularValue V (n-1)`.

`Clumps n s` records a clump `label` and a within-clump `slot : Fin n → Fin s`. Injectivity of `(label, slot)` bounds each clump's size by $s$. The paper takes $s=n^\star$; the formalization allows any such upper bound, whether or not attained. [Partition.lean](Partition.lean), `Clumps.exists_of_label`, constructs this representation from any finite labeling with the size bound, without adding geometric assumptions.

[PaperTheorem.lean](PaperTheorem.lean) assumes $n>0$, $M\ge2s\ge4$, integer $D>m>0$, $\beta>4s/m$, $\tau\ge1$, $\tau D\delta\le1/4$, and $2\pi\delta\le d_{\min}\le\pi s/(MD)$. Its geometric inputs are

$$
\begin{aligned}
d_{\min}&\le |x_i-x_j-2\pi p| &&(i\ne j,\ p\in\mathbb Z),\\
|x_i-x_j|&\le2\pi\tau\delta &&(\text{same clump}),\\
2\pi\beta&<|x_i-x_j-2\pi p| &&(\text{different clumps},\ p\in\mathbb Z).
\end{aligned}
$$

Thus `dmin` need only be a lower bound for all periodic pair distances; the actual minimum recovers the paper's choice. No interpolation, polynomial, spectral, or ordering assumptions are inputs. The proof derives $\delta\ge0$ from the diameter condition and handles $\delta=0$ separately.

For independent localization and averaging degrees, import [ClumpBound.lean](ClumpBound.lean) and use `clump_singularValue_bound_of_split`. For natural numbers $m_1,b$, it proves

$$
\sigma_n(\mathcal V_{m_1+b,M,D}(\mathcal X))\ge
a^{s/2}\sqrt{\frac{M(b+1)}{ns}}
\left(\frac{MD\Delta}{\sqrt2\pi s}\right)^{s-1}.
$$

This interface assumes $n>0$, $s\ge1$, $M\ge2s$, real $D>0$, $\Delta>0$, $0<a\le1/2$, and $(M/s)D\Delta\le\pi$. Distinct nodes have real distance at least $\Delta$; same-clump distances are at most $\pi/(2D)$; different-clump distances satisfy

$$
\frac{4\pi}{\lfloor m_1/s\rfloor+1}\le |x_i-x_j-2\pi p|
\qquad(p\in\mathbb Z).
$$

The existing `clump_singularValue_bound` specializes this to $m_1=\lceil m/2\rceil$ and $b=\lfloor m/2\rfloor$. The paper theorem further sets $a=2-\sqrt e$ and $\Delta=2\pi\delta$.

## Proof organization

| Modules | Role |
| --- | --- |
| [Interpolation](Interpolation.lean), [UniformInterpolation](UniformInterpolation.lean) | Lagrange left inverses, coefficient energy, and minimum-norm cardinal coefficients from a uniform sampling bound. |
| [Separation](Separation.lean), [UniformFrame](UniformFrame.lean) | Periodic normalization, attainment of minimum separation, node counts, uniform sampling, and empty/single-node cases. |
| [Packets](Packets.lean) | Finite exponential sums, frequency budgets, products, translations, and coefficient $\ell^1$ norms. |
| [ClumpGeometry](ClumpGeometry.lean), [Localization](Localization.lean) | Clump coloring, interpolation on separated classes, and localization products. |
| [Quantization](Quantization.lean), [TwoPoint](TwoPoint.lean) | Integer frequency quantization and two-point vanishing factors. |
| [NeighborFactors](NeighborFactors.lean), [NeighborProduct](NeighborProduct.lean) | Vanishing at same-clump neighbors and product norm estimates. |
| [Smoothing](Smoothing.lean), [SingularBound](SingularBound.lean) | Averaged coefficients, Euclidean norms, and the sampling-matrix left inverse. |
| [Construction](Construction.lean), [ClumpBound](ClumpBound.lean) | Complete geometric construction and the general one-dimensional bound, including independent degree allocation. |
| [Bounds](Bounds.lean), [Constants](Constants.lean), [PaperTheorem](PaperTheorem.lean) | Integer bandwidth allocation, constant normalization, and substitution of the paper's parameters. |
| [Audit](Audit.lean) | Direct-admission checks and axiom dependencies of the construction and final theorem. |

The one-dimensional construction controls products through coefficient $\ell^1$ norms of finite exponential sums and then averages in the sampling row space. It follows the NumDetect construction without introducing continuous Fourier integrals or multidimensional function spaces at this stage. Localization uses a uniform sampling constant $1/2$ and then $0<2-\sqrt e\le1/2$ to recover the paper's constant.

The manuscript proof extends a same-clump product to a global
distance-threshold neighborhood, then bounds the number of factors by $s-1$.
This formalization keeps the product within the clump and applies its size bound
directly, with the same conclusion and constants.

## Dependencies and verification

The construction and final theorem have no unproved external dependencies. [General/Fourier/SeparatedSampling.lean](../General/Fourier/SeparatedSampling.lean) proves the uniform sampling estimate needed here: normalized wrap-around separation at least $2/N$ gives

$$
\|Vc\|_2^2\ge\frac N2\|c\|_2^2.
$$

This replaces the historical appeal to the Aubel–Bölcskei circular large sieve. The proof uses a compactly supported cosine-squared window, shifted Parseval identities for the function and its derivative, and vanishing cross terms under periodic separation. Letting the window width approach $4\pi/N$ from below includes the critical separation; empty and single-node configurations are handled separately. No general large-sieve upper bound is asserted.

`Audit.lean` rejects direct admissions and project axioms throughout the core
import closure. It checks that the window mass, uniform sampling bound,
construction, and `small_clumps_singularValue` depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

From the repository root, `lake build` builds the project and
`python3 .github/ci/check.py` checks all source modules and admission
boundaries. See the [repository guide](../../README.md) for project-wide
verification and provenance.

The result was imported from LeanTwoScale commit `5b1241a`.
