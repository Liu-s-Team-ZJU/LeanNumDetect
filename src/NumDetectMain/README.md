# NumDetect main statements

This directory formalizes the definitions and principal theorem statements of
the NumDetect manuscript at commit `a5046fc`. Import `NumDetectMain.Main` for
the complete interface.

## Files

| File | Contents |
| --- | --- |
| `Basic.lean` | Points, finite-dimensional norms, reduced atomic measures, Fourier measurements, admissibility, periodic geometry, clumps, sampling spread, and the CRLs |
| `Matrices.lean` | GHM/GTM, steering vectors, generalized Vandermonde decompositions, contiguous and segmented matrices, spectral norm, and MUSIC correlations |
| `Uniform.lean` | `lem:uniform-Vandermonde`, `liuthm5.1v2`, and `thm:li-resolution` |
| `CRL.lean` | `eq:crl-number-upper`, `eq:crl-number-twosided`, and their positive-amplitude counterparts |
| `Segmented.lean` | The proved ranges of `thm:segmented-vandermonde` and `thm:segmented_threshold` |
| `Random.lean` | Fixed-realization implications used in `thm:resolutionrandghmnumber1` |
| `MUSIC.lean` | `lem:stability_ghm_music` and `cor:stability_multidim_segmented` |
| `Main.lean` | Public aggregate import |

The Lean declarations use stable descriptive names; manuscript labels are
recorded in declaration comments. Paper singular values are one-based, whereas
`matrixSingularValue` is zero-based. Thus the paper's $\hat\sigma_n$ is
`matrixSingularValue A (n - 1)`, and the range $j=n+1,\ldots,L^d$ is represented
by `n ≤ j ∧ j < L ^ d`.

## Statement conventions

`AtomicMeasure d n` encodes the manuscript-wide reduced-form convention:
amplitudes are nonzero and nodes are pairwise distinct. `IsBandMeasurement`
contains both the Fourier observation equation and the strict pointwise noise
bound on $[-\Omega,\Omega]^d$. `IsAdmissible` uses the same strict inequality as
the paper. `LpIndex` represents the full manuscript range $p\in[1,\infty]$,
including a separate infinity case for the two CRL definitions.

`IsAngularClumpStructure` represents the partition by a surjective finite label.
Every cluster is nonempty, has at most $n^\star$ nodes, some cluster has exactly
$n^\star$ nodes, same-cluster periodic $\ell^\infty$ diameter is at most $\tau$,
and different clusters are separated by more than $\eta$.

The first, noise-tail part of the random-GHM theorem is proved for arbitrary
dimension and fixed realized frequency draws. The signal-threshold part is
proved in one dimension under the explicit lower bound on the two realized
Vandermonde factors that the manuscript proof actually uses. The manuscript's
phrases “sufficiently close” and “sufficiently small” do not specify usable
thresholds or a probability event. Its cited 2026 nonuniform-Vandermonde
preprint also has no stable identifier in the bibliography and could not be
located unambiguously, so no unverifiable external theorem is admitted here.

For MUSIC, the perturbed noise space is the fixed-rank trailing left singular
subspace. Using the kernel of the perturbed adjoint would make the manuscript
claim false for arbitrarily small full-rank perturbations. The required
fixed-rank perturbation estimate is proved in
[`General/MatrixAnalysis/MUSICSubspacePerturbation.lean`](../General/MatrixAnalysis/MUSICSubspacePerturbation.lean);
it is not an external admission.

The manuscript-shaped segmented theorems use an explicit `HasFineCubeFrame`
hypothesis, and a proved one-dimensional corollary covers the stated
half-frame range. The former automatic multivariate corollaries were removed:
they depended on an admitted combined version of Li's centered-cube theorem.
Source audit found that Li uses Euclidean separation for the continuous result
and torus separation for the discrete result, while the former Lean statement
used torus separation for both. The cited theorem is also stated only for
$d\ge2$, and its published discrete proof for arbitrary real radius replaces
$m$ by $\lfloor m\rfloor$ without preserving the separation hypothesis. The
unrestricted manuscript range therefore remains an analytic gap rather than an
admitted theorem.

The constant-$2$ CRL lower bound, including the positive-amplitude case, is
proved directly by a finite-difference construction. The Liu--Zhang result
cited by the manuscript gives a different constant,
$0.81e^{-3/2}$, for general complex amplitudes and does not establish the
paper's stated attribution. The Lean conclusion matches the displayed
constant-$2$ formula, but it does not rely on that citation.

## Proof status

All declarations in the repository are proved without admissions. The
separated-cube work records proved reductions to the missing Barton
extremal-function and sharp off-diagonal estimates, but does not assert those
inputs as axioms or admitted theorems.
