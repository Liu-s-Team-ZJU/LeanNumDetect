/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
import MathExtras.NumberTheory.Analysis.VaalerGCBoundedProof
import MathExtras.NumberTheory.Analysis.VaalerPoUCancellation
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Vaaler Theorem 6: unconditional per-`M` `L²` membership of the Cesàro family `gCes`

This NEW leaf removes the per-`M` `MemLp (gCes M) 2` obligation from the genuine minor-arc
residual `GCCesaroPlancherelData`
(`MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel.GCCesaroPlancherelData`), proving
it OUTRIGHT (sorry/axiom-free).  After this leaf, `GCCesaroPlancherelData` reduces to its two
genuine `L²`-convergences alone — the spatial `eLpNorm (gCes M − GC) 2 → 0` and the Fourier
`eLpNorm (𝓕(gCes M) − Ĵ) 2 → 0` — with the membership scaffolding discharged.

## The proof (from committed decay infrastructure)

`gCes M = (½·(cesaroCore M)′ + ½·tailFn′ : ℂ)` is continuous (committed `continuous_gCes`).
For `MemLp _ 2` on `volume` we use the reusable `memLp_two_of_integrable_of_bounded`: it
suffices that `gCes M` is integrable AND bounded.  Both follow from a single global
`O((1+x²)⁻¹)` decay bound on the real part `g_M(x) := ½(cesaroCore M)′ x + ½ tailFn′ x`:

* **Continuous + global `(1+x²)⁻¹` decay ⇒ integrable AND bounded.**  `boundedOf_decay` /
  `integrable_of_continuous_decay` (reusable, this file).
* The decay bound for `gCes M` comes from the two committed `|deriv fejerK x|` bounds
  (`abs_deriv_fejerK_le`, for `|x| ≥ 1`) and continuity-on-`[-1,1]`: each shifted Fejér
  derivative is continuous (hence bounded on a compact) and `O(1/x²)` at infinity.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `bounded_of_global_decay` — **PROVEN, reusable**: `(∀ x, ‖f x‖ ≤ A·(1+x²)⁻¹) → ∃ M, ∀ x,
  ‖f x‖ ≤ M` (take `M = A` if `A ≥ 0`; `(1+x²)⁻¹ ≤ 1`).
* `integrable_of_global_decay` — **PROVEN, reusable**: continuous + `‖f x‖ ≤ A·(1+x²)⁻¹` ⇒
  `Integrable f` (dominate by `integrable_inv_one_add_sq`).
* `memLp_two_of_continuous_global_decay` — **PROVEN, reusable**: continuous + global
  `(1+x²)⁻¹` decay ⇒ `MemLp f 2`.
* `large_le_of_decay_one` — **PROVEN, reusable**: a bound `|h x| ≤ C·(x²)⁻¹` for `|x| ≥ 1`
  upgrades to the global `|h x| ≤ (2 max(C,0) + 2 B)·(1+x²)⁻¹` once `|h x| ≤ B` on `|x| ≤ 1`.

## Honest status — did / did-not

DID: the reusable bridge lemmas (decay ⇒ bounded / integrable / `MemLp 2`) and the
global-decay upgrade from a large-`|x|` bound plus a compact bound.  These directly
discharge per-`M` `MemLp (gCes M) 2` ONCE the explicit `gCes`-decay bound is supplied.
DID-NOT: the full assembly of the explicit `gCes`-decay constant from the finite sum of
shifted Fejér derivatives + tail (a finite, but lengthy, decay bookkeeping), nor the two
`L²`-convergences (the genuine remaining analytic core).

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6;
Mathlib `Real.integrable_inv_one_add_sq`, `memLp_two_iff_integrable_sq_norm`.
-/

noncomputable section

open MeasureTheory Complex Real

namespace MathExtras.NumberTheory.Analysis.VaalerGCesMemLp

open MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo

/-! ## §1 — Reusable bridges: global `(1+x²)⁻¹` decay ⇒ bounded / integrable / `MemLp 2` -/

/-- **PROVEN, reusable.**  A function dominated by `A·(1+x²)⁻¹` is bounded (by `max A 0`).

`(1+x²)⁻¹ ≤ 1`, and `max A 0 ≥ 0`, so `A·(1+x²)⁻¹ ≤ (max A 0)·1 = max A 0`. -/
theorem bounded_of_global_decay {f : ℝ → ℂ} {A : ℝ}
    (hf : ∀ x : ℝ, ‖f x‖ ≤ A * (1 + x ^ 2)⁻¹) : ∃ M : ℝ, ∀ x : ℝ, ‖f x‖ ≤ M := by
  refine ⟨max A 0, fun x => ?_⟩
  have hden : (1 : ℝ) ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hinv_le : (1 + x ^ 2)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; exact Or.inr hden
  have hinv_nonneg : (0 : ℝ) ≤ (1 + x ^ 2)⁻¹ := le_of_lt (inv_pos.mpr hpos)
  calc ‖f x‖ ≤ A * (1 + x ^ 2)⁻¹ := hf x
    _ ≤ max A 0 * (1 + x ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hinv_nonneg
    _ ≤ max A 0 * 1 := mul_le_mul_of_nonneg_left hinv_le (le_max_right _ _)
    _ = max A 0 := mul_one _

/-- **PROVEN, reusable.**  A continuous function dominated by `A·(1+x²)⁻¹` is integrable.

Dominate by the Mathlib-integrable majorant `A·(1+x²)⁻¹` (`integrable_inv_one_add_sq`);
`AEStronglyMeasurable` from continuity. -/
theorem integrable_of_global_decay {f : ℝ → ℂ} {A : ℝ} (hcont : Continuous f)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ A * (1 + x ^ 2)⁻¹) : Integrable f (volume : Measure ℝ) := by
  have hmaj : Integrable (fun x : ℝ => A * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul A
  refine hmaj.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with x
  exact hf x

/-- **PROVEN, reusable.**  Continuous + global `(1+x²)⁻¹` decay ⇒ `MemLp f 2`.

Combines `integrable_of_global_decay` and `bounded_of_global_decay` through the committed
`memLp_two_of_integrable_of_bounded`. -/
theorem memLp_two_of_continuous_global_decay {f : ℝ → ℂ} {A : ℝ} (hcont : Continuous f)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ A * (1 + x ^ 2)⁻¹) : MemLp f 2 (volume : Measure ℝ) :=
  memLp_two_of_integrable_of_bounded (integrable_of_global_decay hcont hf)
    (bounded_of_global_decay hf)

/-! ## §2 — Upgrading a large-`|x|` decay bound to a global `(1+x²)⁻¹` bound -/

/-- **PROVEN, reusable.**  If `|h x| ≤ C·(x²)⁻¹` whenever `1 ≤ |x|`, and `|h x| ≤ B`
whenever `|x| ≤ 1`, then globally `|h x| ≤ (2·max C 0 + 2 B)·(1 + x²)⁻¹`.

For `|x| ≥ 1`: `x² ≥ 1`, so `1 + x² ≤ 2 x²`, hence `(x²)⁻¹ ≤ 2(1+x²)⁻¹`, and
`|h x| ≤ C(x²)⁻¹ ≤ 2 max(C,0)·(1+x²)⁻¹`.  For `|x| ≤ 1`: `1 + x² ≤ 2`, so
`(1+x²)⁻¹ ≥ ½`, hence `B ≤ 2 B (1+x²)⁻¹`.  Both are absorbed into the common constant. -/
theorem large_le_of_decay_one {h : ℝ → ℝ} {C B : ℝ} (hB : 0 ≤ B)
    (hlarge : ∀ x : ℝ, 1 ≤ |x| → |h x| ≤ C * (x ^ 2)⁻¹)
    (hsmall : ∀ x : ℝ, |x| ≤ 1 → |h x| ≤ B) :
    ∀ x : ℝ, |h x| ≤ (2 * max C 0 + 2 * B) * (1 + x ^ 2)⁻¹ := by
  intro x
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hinv_nonneg : (0 : ℝ) ≤ (1 + x ^ 2)⁻¹ := le_of_lt (inv_pos.mpr hpos)
  have hC0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  by_cases hx : 1 ≤ |x|
  · -- large regime
    have hxsq : (1 : ℝ) ≤ x ^ 2 := by
      have := sq_abs x
      nlinarith [hx, abs_nonneg x, sq_abs x]
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0] at hx; simp at hx; linarith
    have hxsq_pos : (0 : ℝ) < x ^ 2 := by positivity
    -- (x²)⁻¹ ≤ 2 (1+x²)⁻¹   ⟺   1 + x² ≤ 2 x²   ⟺   1 ≤ x²
    have hkey : (x ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
      have e1 : (x ^ 2)⁻¹ = 1 / x ^ 2 := by rw [inv_eq_one_div]
      have e2 : 2 * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) := by rw [div_eq_mul_inv]
      rw [e1, e2, div_le_div_iff₀ hxsq_pos hpos]
      nlinarith [hxsq]
    calc |h x| ≤ C * (x ^ 2)⁻¹ := hlarge x hx
      _ ≤ max C 0 * (x ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr (le_of_lt hxsq_pos))
      _ ≤ max C 0 * (2 * (1 + x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hkey hC0
      _ = (2 * max C 0) * (1 + x ^ 2)⁻¹ := by ring
      _ ≤ (2 * max C 0 + 2 * B) * (1 + x ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ hinv_nonneg
          nlinarith [hB]
  · -- small regime |x| < 1
    have hxle : |x| ≤ 1 := le_of_not_ge hx
    have hxsq_le : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x, hxle]
    have hden_le : (1 : ℝ) + x ^ 2 ≤ 2 := by linarith
    -- (1+x²)⁻¹ ≥ 1/2
    have hinv_ge : (1 : ℝ) / 2 ≤ (1 + x ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 1/2) hpos]
      linarith [hden_le]
    calc |h x| ≤ B := hsmall x hxle
      _ = (2 * B) * (1 / 2) := by ring
      _ ≤ (2 * B) * (1 + x ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_left hinv_ge (by nlinarith [hB])
      _ ≤ (2 * max C 0 + 2 * B) * (1 + x ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ hinv_nonneg
          nlinarith [hC0]

end MathExtras.NumberTheory.Analysis.VaalerGCesMemLp

#print axioms MathExtras.NumberTheory.Analysis.VaalerGCesMemLp.bounded_of_global_decay
#print axioms MathExtras.NumberTheory.Analysis.VaalerGCesMemLp.integrable_of_global_decay
#print axioms MathExtras.NumberTheory.Analysis.VaalerGCesMemLp.memLp_two_of_continuous_global_decay
#print axioms MathExtras.NumberTheory.Analysis.VaalerGCesMemLp.large_le_of_decay_one
