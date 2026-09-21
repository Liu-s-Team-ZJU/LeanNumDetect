/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo
import MathExtras.NumberTheory.Analysis.VaalerCosecCubeIdentity

/-!
# Vaaler Theorem 6: discharging `GCBounded` (one of the three minor-wall inputs)

This NEW leaf proves the named `Prop`
`MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo.GCBounded`
(`∃ M, ∀ x, ‖GC x‖ ≤ M`), the boundedness of the complexified explicit half-derivative
`GC = (½ H′ : ℂ)`, which is one of the three remaining inputs to the minor-arc wall
(`{GIntegrable, GCBounded, GCCesaroPlancherelData}`).

## The proof (elementary, from committed pieces)

The committed capstone `VaalerCosecCubeIdentity.gDecayBound_proven` supplies the full
`O((1+x²)⁻¹)` decay bound `∃ C, ∀ x, ‖GC x‖ ≤ C·(1+x²)⁻¹` (Vaaler eq. (2.32)).  Boundedness
is strictly weaker: for the SAME constant `C`,

* `C ≥ 0` because `0 ≤ ‖GC 0‖ ≤ C·(1+0²)⁻¹ = C`;
* `(1 + x²)⁻¹ ≤ 1` for every real `x` (since `1 ≤ 1 + x²`), so
  `‖GC x‖ ≤ C·(1+x²)⁻¹ ≤ C·1 = C`.

Hence `GCBounded` holds with `M := C`.  No new analytic content beyond the already-proven
decay — exactly as the `VaalerGCMemLpTwo` header anticipates.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `gCBounded_proven` — **PROVEN** `GCBounded` (the named minor-wall input), `#print axioms`
  reducing only to `gDecayBound_proven`'s axiom profile.
* `memLp_GC_two_of_integrable` — **PROVEN** convenience: `GIntegrable → MemLp GC 2`
  (boundedness now being unconditional).

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eq. (2.32) (`½H′ = J`, `J(x) = O((1+|x|)⁻²)`).
-/

noncomputable section

open MeasureTheory Complex Real

namespace MathExtras.NumberTheory.Analysis.VaalerGCBoundedProof

open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo

/-- **PROVEN — `GCBounded`** (`∃ M, ∀ x, ‖GC x‖ ≤ M`).

Take `M := C` from the committed decay bound `gDecayBound_proven`
(`∃ C, ∀ x, ‖GC x‖ ≤ C·(1+x²)⁻¹`).  Then `C ≥ 0` (from the bound at `x = 0`), and since
`(1+x²)⁻¹ ≤ 1`, the decay bound dominates the constant bound:
`‖GC x‖ ≤ C·(1+x²)⁻¹ ≤ C·1 = C`. -/
theorem gCBounded_proven : GCBounded := by
  obtain ⟨C, hC⟩ := MathExtras.NumberTheory.Analysis.VaalerCosecCubeIdentity.gDecayBound_proven
  refine ⟨C, fun x => ?_⟩
  -- `(1 + x²)⁻¹ ≤ 1` and `C ≥ 0`, so `C·(1+x²)⁻¹ ≤ C`.
  have hden : (1 : ℝ) ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hinv_le_one : (1 + x ^ 2)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; exact Or.inr hden
  have hinv_nonneg : (0 : ℝ) ≤ (1 + x ^ 2)⁻¹ := le_of_lt (inv_pos.mpr hpos)
  -- `C ≥ 0` from the bound at `x = 0`.
  have hC0 : (0 : ℝ) ≤ C := by
    have h := hC 0
    have : C * (1 + (0 : ℝ) ^ 2)⁻¹ = C := by norm_num
    rw [this] at h
    exact le_trans (norm_nonneg _) h
  calc ‖GC x‖ ≤ C * (1 + x ^ 2)⁻¹ := hC x
    _ ≤ C * 1 := by exact mul_le_mul_of_nonneg_left hinv_le_one hC0
    _ = C := by ring

/-- **PROVEN — `MemLp GC 2` from `GIntegrable`** (boundedness now unconditional via
`gCBounded_proven`). -/
theorem memLp_GC_two_of_integrable (hGint : GIntegrable) : MemLp GC 2 (volume : Measure ℝ) :=
  memLp_GC_two_of hGint gCBounded_proven

#print axioms gCBounded_proven
#print axioms memLp_GC_two_of_integrable

end MathExtras.NumberTheory.Analysis.VaalerGCBoundedProof
