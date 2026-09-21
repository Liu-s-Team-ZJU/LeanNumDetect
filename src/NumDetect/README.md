# NumDetect definitions and main results

This directory formalizes the definitions and principal theorem statements of
the NumDetect manuscript based at commit `a5046fc`, together with the local
translated-cube correction in `main.tex`. All modules are kept directly in
this directory. Related files share a descriptive prefix, while each relatively
independent main result has one public entry module. Import `NumDetect.Main` for
the complete interface.

## Module groups

| Files | Contents |
| --- | --- |
| [`Basic.lean`](Basic.lean), [`Matrices.lean`](Matrices.lean), [`MatrixFacts.lean`](MatrixFacts.lean) | Observation-model definitions, matrix constructions, exact GHM/GTM Fourier factorizations, and shared matrix estimates |
| `Uniform*.lean` | Contiguous-grid interpolation, `lem:uniform-Vandermonde`, `liuthm5.1v2`, and `thm:li-resolution`; entry module: [`Uniform.lean`](Uniform.lean) |
| `Segmented*.lean` | Segmented interpolation, the proved ranges of `thm:segmented-vandermonde`, and `thm:segmented_threshold`; entry module: [`Segmented.lean`](Segmented.lean) |
| `Random*.lean` | Matrix estimates and fixed-realization implications used in `thm:resolutionrandghmnumber1`; entry module: [`Random.lean`](Random.lean) |
| `MUSIC*.lean` | Exact noiseless signal/noise-space characterization, fixed-rank perturbation adapters, `lem:stability_ghm_music`, and `cor:stability_multidim_segmented`; entry module: [`MUSIC.lean`](MUSIC.lean) |
| `CRL*.lean` | Finite-difference lower bounds, `eq:crl-number-upper`, `eq:crl-number-twosided`, and their positive-amplitude counterparts; entry module: [`CRL.lean`](CRL.lean) |
| [`Main.lean`](Main.lean) | Public aggregate import |

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
`localSparsity_eq_of_angularClumpStructure` proves the manuscript's stated
consequence $\nu_\infty(\tau,\mathcal X)=n^\star$.

The first, noise-tail part of the random-GHM theorem is proved for arbitrary
dimension and fixed realized frequency draws. The signal-threshold part is
proved in one dimension under the explicit lower bound on the two realized
Vandermonde factors that the manuscript proof actually uses. The manuscript's
phrases “sufficiently close” and “sufficiently small” do not specify usable
thresholds or a probability event. More fundamentally, its spread hypothesis
is imposed on the parent sets $\mathcal A,\mathcal B$, while the proof applies
the spread to the randomly selected realized frequency sets; the former does
not imply the latter. For example, with $n=2$, $L>2$, parent set
$\{0,1,2,L\}$, and a three-point draw, the parent spread is $L$, while
the positive-probability realization $\{0,1,2\}$ has spread only $2$.
Its cited 2026 nonuniform-Vandermonde preprint also has no stable identifier
in the bibliography and could not be located unambiguously, so no
unverifiable external theorem is admitted here.

For MUSIC, the perturbed noise space is the fixed-rank trailing left singular
subspace. Using the kernel of the perturbed adjoint would make the manuscript
claim false for arbitrarily small full-rank perturbations. The required
fixed-rank perturbation estimate is proved in
[`General/MatrixAnalysis/MUSICSubspacePerturbation.lean`](../General/MatrixAnalysis/MUSICSubspacePerturbation.lean);
it is not an external admission. For an exact rank-$n$ matrix,
`rankNoiseSpaceCorrelation_eq_zero_iff_mem_signalSpace` proves that the MUSIC
correlation vanishes exactly on steering vectors in the signal space, and
`noiselessMUSIC_correlation_eq_zero_iff_source` obtains the manuscript's exact
source-location statement from its identifiability hypothesis.

The manuscript-shaped segmented Vandermonde, threshold, and MUSIC theorems no
longer expose a `HasFineCubeFrame` hypothesis.  The discrete centered-cube
argument is stated in its translation-invariant form: the real frequency cube
is centered at `K / 2` with radius `(K + 1) / 2`, so its integer points are
exactly `{0, ..., K}^d`.  This preserves the manuscript denominator `K + 1`
and handles both parities without taking a floor of the cube radius.  The angular-to-unit
torus normalization, distance scaling, phase conversion, and all downstream
uses are proved in
[`General/Fourier/BartonCubeFrame.lean`](../General/Fourier/BartonCubeFrame.lean).
The underlying translated-cube Fourier-frame estimate is the single registered
external input.

The constant-$2$ CRL lower bound, including the positive-amplitude case, is
proved directly by a finite-difference construction. The Liu--Zhang result
cited by the manuscript gives a different constant,
$0.81e^{-3/2}$, for general complex amplitudes and does not establish the
paper's stated attribution. The Lean conclusion matches the displayed
constant-$2$ formula, but it does not rely on that citation.

The CRL definitions use `sInf`, the infimum of all guaranteed separations. The
manuscript says “smallest”, but its upper-bound proof establishes guarantees
only for separations strictly above the displayed threshold and does not prove
that the endpoint itself is admissible. Thus literal attainment of a smallest
value is not currently justified by the manuscript.

## Proof status

All project-specific conversions and manuscript results are proved.  The sole
admission is the registered translated-cube Fourier-frame theorem from the
Beurling--Selberg/Barton--Li argument; see
[`External/README.md`](../External/README.md).
