/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2Limit
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Vaaler Theorem 6: the `GC`-side `L²` membership for the Plancherel route

This NEW leaf reduces the `GC`-side `L²` membership `MemLp GC 2` — the last *membership*
hypothesis of the Plancherel route to `GCFTeqJhat` — to the **boundedness** of `GC`
together with the pre-existing `GIntegrable` residual.

`GC = (½H′ : ℂ)` is `O(1/x²)` (Vaaler eq. (2.27)/(2.32)) and in particular bounded; with
`GC ∈ L¹` (`GIntegrable`), `∫ ‖GC‖² ≤ M·∫ ‖GC‖ < ∞`, so `GC ∈ L²`.  Boundedness is a
strictly weaker residual than the full `O(1/x²)` decay that already underlies `GIntegrable`,
so this does not add genuinely new analytic content beyond what `GIntegrable` consumes.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `memLp_two_of_integrable_of_bounded` — **PROVEN, reusable**: for any `f : ℝ → ℂ`,
  `Integrable f → (∃ M, ∀ x, ‖f x‖ ≤ M) → MemLp f 2`.  (`memLp_two_iff_integrable_sq_norm`
  + the pointwise bound `‖f‖² ≤ M·‖f‖` dominated by the integrable `M·‖f‖`.)
* `GCBounded` (named `Prop`, NEVER an `axiom`) — `∃ M, ∀ x, ‖GC x‖ ≤ M` (the boundedness
  of the explicit half-derivative `½H′`).
* `memLp_GC_two_of` — **PROVEN** `GIntegrable → GCBounded → MemLp GC 2`.
* `gcFTeqJhat_of_plancherelLimit_of_bounded` — **PROVEN**: the deepest minor residual
  `GCFTeqJhat` from `{GIntegrable, GCBounded, GCPlancherelLimitData}` (with the `Ĵ`-side
  `L²` membership already discharged unconditionally, `memLp_vaalerJCcont_two`).

## Honest status — did / did-not

DID: reduced the `GC`-side `L²` membership to boundedness + `GIntegrable`, and re-threaded
the full Plancherel route so `GCFTeqJhat` rests on `{GIntegrable, GCBounded,
GCPlancherelLimitData}`.  DID-NOT: discharge `GCBounded` (the explicit `O(1/x²)` bound on
`½H′`) or the `L²`-convergence datum `GCPlancherelLimitData`; both remain named `Prop`s.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6;
Mathlib `memLp_two_iff_integrable_sq_norm`.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform

namespace MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo

open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2Limit

/-! ## §1 — Bounded + integrable ⇒ `L²` (reusable) -/

/-- **PROVEN, reusable.**  A bounded integrable function on `ℝ` is in `L²`.

`memLp_two_iff_integrable_sq_norm` reduces `MemLp f 2` to integrability of `‖f ·‖²`; the
pointwise bound `‖f x‖² ≤ M·‖f x‖` (from `‖f x‖ ≤ M`) is dominated by the integrable
`M·‖f ·‖` (`Integrable.norm.const_mul`). -/
theorem memLp_two_of_integrable_of_bounded {f : ℝ → ℂ} (hint : Integrable f)
    (hbdd : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) : MemLp f 2 := by
  obtain ⟨M, hb⟩ := hbdd
  rw [memLp_two_iff_integrable_sq_norm hint.aestronglyMeasurable]
  have hdom : Integrable (fun x => M * ‖f x‖) := hint.norm.const_mul M
  have hmeas : AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) volume := by fun_prop
  refine hdom.mono hmeas ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsq : ‖f x‖ ^ 2 ≤ M * ‖f x‖ := by
    rw [sq]; exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
  exact hsq.trans (le_abs_self _)

/-! ## §2 — `GCBounded` and the `GC`-side `L²` membership -/

/-- **Named `Prop` (NEVER an `axiom`): the boundedness of `GC = (½H′ : ℂ)`.**

`∃ M, ∀ x, ‖GC x‖ ≤ M`.  The explicit half-derivative `½H′` is `O(1/x²)`, hence bounded.
A strictly weaker statement than the full decay underlying `GIntegrable`. -/
def GCBounded : Prop := ∃ M : ℝ, ∀ x : ℝ, ‖GC x‖ ≤ M

/-- **PROVEN — `MemLp GC 2` from `GIntegrable` and `GCBounded`.** -/
theorem memLp_GC_two_of (hGint : GIntegrable) (hBdd : GCBounded) : MemLp GC 2 :=
  memLp_two_of_integrable_of_bounded hGint hBdd

/-! ## §3 — `GCFTeqJhat` from `{GIntegrable, GCBounded, GCPlancherelLimitData}` -/

/-- **PROVEN — the deepest minor residual `GCFTeqJhat` from the bounded-route residuals.**

With the `Ĵ`-side `L²` membership unconditional (`memLp_vaalerJCcont_two`) and the `GC`-side
`L²` membership reduced to `GCBounded` (`memLp_GC_two_of`), the Plancherel route closes
`GCFTeqJhat` from `{GIntegrable, GCBounded, GCPlancherelLimitData}`. -/
theorem gcFTeqJhat_of_plancherelLimit_of_bounded
    (hGint : GIntegrable) (hBdd : GCBounded)
    (hData : GCPlancherelLimitData (memLp_GC_two_of hGint hBdd) memLp_vaalerJCcont_two) :
    GCFTeqJhat :=
  gcFTeqJhat_of_plancherelLimit hGint (memLp_GC_two_of hGint hBdd) memLp_vaalerJCcont_two hData

#print axioms memLp_two_of_integrable_of_bounded
#print axioms memLp_GC_two_of
#print axioms gcFTeqJhat_of_plancherelLimit_of_bounded

end MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo
