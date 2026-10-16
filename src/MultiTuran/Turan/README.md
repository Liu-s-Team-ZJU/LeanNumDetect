# Turán estimates

This directory contains the complete one-dimensional measurable-set Turán
proof and the geometric reduction that extends it to multidimensional convex
bodies. Import `MultiTuran.Turan.Main` for both results. The parent
`MultiTuran.Main` also exports this interface together with the single-clump
block-sampling theorem. Multi-clump block sampling has the separate public
entry `MultiTuran.MultiClump.Results`.

Filenames omit the repeated `Turan` prefix. For example,
[GeometryTransfer.lean](GeometryTransfer.lean) is the module
`MultiTuran.Turan.GeometryTransfer`. Public declaration names remain in
`LeanNumDetect.MultiTuran`; these module paths do not add a `Turan` component
to that namespace. The recurrence helpers retain their existing subnamespace
`LeanNumDetect.MultiTuran.TuranRecurrence`.

## Public results

| Module | Result and role |
| --- | --- |
| [Unit](Unit.lean) | `exponentialSum_unit_geometric_turan` and `exponentialSum_unit_norm_le_of_bound`: arbitrary real frequencies on the centered unit interval, including repeated frequencies, zero coefficients, and the zero function |
| [Main](Main.lean) | `oneDimensional_turan_comparison`: arbitrary positive-measure measurable subsets of every bounded interval |
| [Main](Main.lean) | `exponentialSum_convexBody_supNorm_le`: the convex-body supremum estimate in manuscript `lem:multidim-turan` |
| [Main](Main.lean) | `exponentialSum_convexBody_eLpNorm_top_le`: the essential $L^\infty$ formulation, including null exceptional subsets |
| [Main](Main.lean) | `aperture_supNorm_turan`: the filling-ratio specialization used in block sampling |
| [Main](Main.lean) | `exists_multidimensionalTuranConstant`: the absolute-constant existence statement, witnessed by the explicit positive `multidimensionalTuranConstant` |

The one-dimensional statement is proved first. If $C_0$ is its absolute
constant, the geometric reduction gives the factor

$$
\left(2C_0d\frac{|B|}{|Z|}\right)^{n-1}
$$

for a compact convex body $B$ and a positive-measure measurable subset
$Z\subseteq B$. In [Main](Main.lean), `multidimensionalTuranConstant` is
defined as `2*oneDimensionalTuranConstant`, so the final expression is
$(C_{\mathrm T}d|B|/|Z|)^{n-1}$. This constant is independent of dimension,
term count, and frequencies. No frequency-separation condition is required.

## Four proof lines

### 1. Recurrence and complex growth

[Recurrence](Recurrence.lean) and [RecurrenceBounds](RecurrenceBounds.lean)
prove the exact-degree $n-1$ extrapolation majorant for sampled exponential
sums; the sampled roots may coincide.
[Interval](Interval.lean) turns the recurrence into interval extrapolation.
[Complex](Complex.lean) then gives genuine complex-disk growth bounds for
the entire exponential sum. This growth input is used in the analytic
estimates below.

### 2. Actual zeros and the bounded-spectrum geometric mean

[BlaschkeFactors](BlaschkeFactors.lean),
[BlaschkeQuotient](BlaschkeQuotient.lean),
[BlaschkeZeroCount](BlaschkeZeroCount.lean),
[BlaschkeZeros](BlaschkeZeros.lean), and
[BlaschkeExtraction](BlaschkeExtraction.lean) construct the finite zero
family with actual analytic multiplicities and a bounded zero-free quotient.
The maximum principle and the quantitative estimates in
[Harnack](Harnack.lean) control this quotient.

[LogPotential](LogPotential.lean) and
[EffectiveRoots](EffectiveRoots.lean) bound the integral of the actual
effective root potential by
$\alpha(2N+(n-1)\log(1/\alpha))$.
[EffectiveProduct](EffectiveProduct.lean),
[EffectiveProductRoots](EffectiveProductRoots.lean),
[LocalProduct](LocalProduct.lean), and
[EffectiveLower](EffectiveLower.lean) retain effective degree $n-1$ even
when the exponential sum has more zeros.
[DiskMajorant](DiskMajorant.lean) assembles the pointwise logarithmic
majorant, and [GeometricBound](GeometricBound.lean) supplies the integration
step. [ComplexGeometric](ComplexGeometric.lean) obtains logarithmic
regularity and the bounded-spectrum geometric-mean estimate.

### 3. Weak logarithmic derivatives and arbitrary frequencies

[HalfPlane](HalfPlane.lean) and [HarmonicMass](HarmonicMass.lean) use
tangent-circle averages and Fatou's lemma to bound real-line logarithmic
mass. [CauchyHalfPlane](CauchyHalfPlane.lean) and
[CauchyWeak](CauchyWeak.lean) derive the weak distribution estimate for
actual finite Cauchy sums. In parallel,
[LogDerivative](LogDerivative.lean) controls the zero-free logarithmic
derivative using Harnack, Borel–Carathéodory, and Cauchy's estimate.
[BlaschkeDerivative](BlaschkeDerivative.lean) and
[WeakLogDerivative](WeakLogDerivative.lean) combine these inputs into the
weak logarithmic derivative bound obtained from actual disk growth.

[WeakLog](WeakLog.lean), [GeometricMean](GeometricMean.lean), and
[GeometricBase](GeometricBase.lean) turn weak distribution bounds into
geometric-mean control while treating zeros explicitly.
[Pruning](Pruning.lean) defines the genuine first-order pruning operators,
and [PruningInduction](PruningInduction.lean) proves the induction on the
number of terms using explicit bounded-spectrum and weak-pruning inputs.
[SpectralCentering](SpectralCentering.lean) and
[PruningModulation](PruningModulation.lean) connect these operators to
centered complex exponential sums without changing the real-line modulus.

[Unit](Unit.lean) supplies both analytic inputs, including the
bounded-spectrum result from the second proof line, and proves the
unconditional centered-unit-interval theorem. The induction retains the
original measurable set and permits repeated frequencies, zero coefficients,
and identically zero prunings. [AffineTransfer](AffineTransfer.lean) then
transfers this theorem to every bounded interval; [Main](Main.lean) exports
it as `oneDimensional_turan_comparison`.

### 4. From the one-dimensional theorem to convex bodies

[GeometryRay](GeometryRay.lean) identifies the ray sections of compact
convex bodies. [GeometryPolar](GeometryPolar.lean) proves polar
disintegration with the genuine radial density $r^{d-1}$.
[GeometryDensity](GeometryDensity.lean) selects a ray whose relative
one-dimensional measure controls the volume ratio.
[GeometryTransfer](GeometryTransfer.lean) restricts the multidimensional
exponential sum to that ray and applies a supplied
`OneDimensionalTuranComparison`, paying precisely the factor $2d$.

[EssentialTransfer](EssentialTransfer.lean) extends this reduction to
almost-everywhere bounds and essential $L^\infty$ norms.
[Main](Main.lean) supplies the proved scalar comparison from the first
three proof lines to both transfers. The resulting multidimensional
theorems have no scalar comparison or analytic estimate left as an
assumption.

## Verification

Run `lake build +MultiTuran.Turan.Main` to build the Turán interface, or
`lake build MultiTuran` for the full library. The
[Turán and single-clump audit](../Verification/Audit.lean) is available through
`lake build +MultiTuran.Verification.Audit`. It checks every imported project
declaration, including private proof bodies, for admissions and project
axioms, and checks that the listed public results depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Run
`python3 .github/ci/check.py` for the repository-wide verification.
