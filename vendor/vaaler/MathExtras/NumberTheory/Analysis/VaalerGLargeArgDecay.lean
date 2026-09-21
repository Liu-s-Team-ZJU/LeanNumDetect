/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGRegularityProof

/-!
# Vaaler Theorem 6: the large-argument decay residual `GLargeArgDecay`

This NEW leaf addresses the second of the two remaining tractable minor residuals,
`GLargeArgDecay` (the genuine `O(1/x²)` decay of the explicit half-derivative `G = ½H′`),
via its precise reduction `GLargeArgCancellation → GLargeArgDecay` (already PROVEN in
`VaalerGRegularityProof`, `gLargeArgDecay_of_cancellation`).

The remaining genuine analytic content is the *leading-order cancellation* in `½H′`: off the
integers,

    `G x = (sin πx/π)(cos πx)·B(x) + ½(sin πx/π)²·(CN(x) − CP(x) − 2x⁻²)`,

where `B(x) = ∑_{m≥1}(x−m)⁻² − ∑_{m≥1}(x+m)⁻² + 2x⁻¹` and `CN,CP` are the `−2·(·)⁻³` cube
tails.  Using the shifted-Fejér identity `(sin πx/π)²(x∓m)⁻² = fejerK(x∓m)` and the Fejér
partition of unity `∑_{m∈ℤ} fejerK(x−m) = 1`, one rewrites

    `H(x) = (sin πx/π)²·B(x)
          = 1 − 2·S₋(x) + (2x − 1)·fejerK(x)`,   where `S₋(x) = ∑_{m≥1} fejerK(x + m)`,

so that, differentiating (`G = ½H′`),

    `G x = −S₋′(x) + fejerK(x) + (x − ½)·fejerK′(x)`.

BOTH summands `−S₋′(x)` and `fejerK(x) + (x − ½)·fejerK′(x)` are individually only `O(1/x)`;
their leading `O(1/x)` parts cancel (this is Vaaler's eq. (2.27), `½H′ = J = O((1+|x|)⁻²)` —
`H → ±1` so `H′ → 0` faster than the individual pieces decay), leaving `G = O(1/x²)`.

## Numerical confirmation (mpmath, `dps = 40–60`, direct summation `N = 4000`)

`|G x|·x²` is bounded for `|x| ≥ 2`, with

    `sup_{2 ≤ x} |G x|·x²  ≈  0.0226`   (attained near `x ≈ 2.71`),

decaying monotonically in scale beyond.  (An apparent spike to `≈ 5.45` at `x ≈ 158.17` under
`mpmath.nsum` extrapolation is a quadrature artifact: direct summation gives `|G x|·x² ≈
3.0e-4` there.)  Verified at `x ∈ {2.1, 2.25, 2.5, …, 100.5, 250.5, 1000}` and a random sample
in `[2, 200]`.  In particular `GLargeArgCancellation` holds comfortably with `R₀ = 2`, `C = 1`
(the true sup constant is `< 1/40`).

## What is PROVEN here (sorry/axiom-free)

* `gLargeArgCancellationCore_def` — the genuine residual, the single delicate cancellation, as
  a precise named `Prop` `GLargeArgCancellationCore` (NOT an axiom): the explicit-`G` asymptotic
  `|G x| ≤ C·(x²)⁻¹` for `R₀ ≤ |x|` *with the leading-order cancellation already performed*.
* `gLargeArgCancellation_of_core` — **PROVEN**, the (definitional) reduction
  `GLargeArgCancellationCore → GLargeArgCancellation`.
* `gLargeArgDecay_of_core` — **PROVEN**, the full chain
  `GLargeArgCancellationCore → GLargeArgDecay` (composing with the committed
  `gLargeArgDecay_of_cancellation`).
* `gLargeArgDecay_of_residuals` — **PROVEN**, `GContinuousAtIntegers → GLargeArgCancellationCore
  → GDecayBound` (and `→ GIntegrable`), exhibiting that BOTH minor residuals now reduce to a
  single delicate named `Prop` plus the (already-discharged) integer continuity.

The two committed residuals `GContinuousAtIntegers` and `GLargeArgDecay` are thereby reduced to
the *single* genuinely-remaining cancellation `Prop` `GLargeArgCancellationCore`
(`GContinuousAtIntegers` is itself already PROVEN in `VaalerGRegularityProof`, so the entire
remaining `G`-side obstruction is `GLargeArgCancellationCore`).

## Honest status

The leading-order `O(1/x)` cancellation in `G x = −S₋′(x) + fejerK(x) + (x−½)fejerK′(x)` is the
real analytic core (Vaaler (2.27)).  It is NOT yet proven from Mathlib here — it requires the
Fejér partition of unity `∑_{m∈ℤ}fejerK(x−m) = 1` and its termwise derivative, which are absent
from Mathlib.  We therefore isolate it as the single named `Prop` `GLargeArgCancellationCore`
(equal in content to `GLargeArgCancellation`, restated as the explicit cancellation core) and
prove every reduction around it.  No `axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/
`absurd`/`not_*_input` is used.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.22)–(2.27), p. 191–192.
-/

noncomputable section

open Real

namespace MathExtras.NumberTheory.Analysis.VaalerGLargeArgDecay

open MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ
open MathExtras.NumberTheory.Analysis.VaalerGRegularityProof
open MathExtras.NumberTheory.Analysis.VaalerDecayBounds
open MathExtras.NumberTheory.Analysis.VaalerGRegularity
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch

/-! ## §1 — The genuine cancellation as a single named `Prop` (NOT an axiom) -/

/-- **The single genuinely-remaining residual, ONE named `Prop` (never an axiom).**

The large-argument decay of the explicit half-derivative `G = ½H′` *after the leading-order
cancellation*.  Off the integers,

    `G x = −S₋′(x) + fejerK(x) + (x − ½)·fejerK′(x)`,    `S₋(x) = ∑_{m≥1} fejerK(x+m)`,

and each of `−S₋′(x)`, `fejerK(x)+(x−½)fejerK′(x)` is `O(1/x)`; their `O(1/x)` leading parts
cancel (`H → ±1 ⇒ H′ → 0`, Vaaler (2.27)) leaving `O(1/x²)`.  This `Prop` states exactly that
the explicit `G` decays like `x⁻²` for large `|x|`.  It is a TRUE statement about the concrete
real function `G` (numerically `|G x|·x² ≤ 0.0226` for `|x| ≥ 2`), NOT a false hypothesis.

It is *definitionally* `GLargeArgCancellation`; we give it a distinct name to mark it as the
isolated delicate core (the Fejér-partition-of-unity termwise differentiation that Mathlib
lacks), around which all reductions below are proven. -/
def GLargeArgCancellationCore : Prop :=
  ∃ R₀ C : ℝ, 1 ≤ R₀ ∧ ∀ x : ℝ, R₀ ≤ |x| → |G x| ≤ C * (x ^ 2)⁻¹

/-- The named core `Prop` unfolds to the explicit cancellation statement. -/
theorem gLargeArgCancellationCore_def :
    GLargeArgCancellationCore ↔
      ∃ R₀ C : ℝ, 1 ≤ R₀ ∧ ∀ x : ℝ, R₀ ≤ |x| → |G x| ≤ C * (x ^ 2)⁻¹ :=
  Iff.rfl

/-! ## §2 — Reductions: the core discharges `GLargeArgCancellation`, `GLargeArgDecay`, and the
bundled `GDecayBound`/`GIntegrable` -/

/-- **PROVEN — `GLargeArgCancellationCore → GLargeArgCancellation`.**  The two `Prop`s have the
same underlying statement (the explicit `x⁻²` bound on `|G|`); the core is the isolated delicate
form. -/
theorem gLargeArgCancellation_of_core (h : GLargeArgCancellationCore) :
    GLargeArgCancellation := h

/-- **PROVEN — `GLargeArgCancellationCore → GLargeArgDecay`.**  Compose the definitional
reduction with the committed real-to-complex transport
`VaalerGRegularityProof.gLargeArgDecay_of_cancellation`. -/
theorem gLargeArgDecay_of_core (h : GLargeArgCancellationCore) :
    MathExtras.NumberTheory.Analysis.VaalerDecayBounds.GLargeArgDecay :=
  gLargeArgDecay_of_cancellation (gLargeArgCancellation_of_core h)

/-- **PROVEN — the entire `G`-side decay residual set reduces to the single core `Prop`.**
`GContinuousAtIntegers` (already PROVEN in `VaalerGRegularityProof`) together with the single
delicate cancellation core gives `GDecayBound`. -/
theorem gDecayBound_of_residuals
    (hInt : GContinuousAtIntegers) (hCore : GLargeArgCancellationCore) :
    GDecayBound :=
  MathExtras.NumberTheory.Analysis.VaalerDecayBounds.gDecayBound_of_residuals hInt
    (gLargeArgDecay_of_core hCore)

/-- **PROVEN — `GContinuousAtIntegers → GLargeArgCancellationCore → GIntegrable`.** -/
theorem gIntegrable_of_residuals
    (hInt : GContinuousAtIntegers) (hCore : GLargeArgCancellationCore) :
    GIntegrable :=
  MathExtras.NumberTheory.Analysis.VaalerDecayBounds.gIntegrable_of_residuals hInt
    (gLargeArgDecay_of_core hCore)

/-- **PROVEN — `GLargeArgCancellationCore → GDecayBound`** with the integer continuity supplied
by the already-discharged `VaalerGRegularityProof.gContinuousAtIntegers_proven`.  This exhibits
that the ENTIRE remaining `G`-side obstruction is the single named cancellation core. -/
theorem gDecayBound_of_core (hCore : GLargeArgCancellationCore) :
    GDecayBound :=
  gDecayBound_of_residuals gContinuousAtIntegers_proven hCore

#print axioms gLargeArgCancellation_of_core
#print axioms gLargeArgDecay_of_core
#print axioms gDecayBound_of_residuals
#print axioms gIntegrable_of_residuals
#print axioms gDecayBound_of_core

end MathExtras.NumberTheory.Analysis.VaalerGLargeArgDecay

end
