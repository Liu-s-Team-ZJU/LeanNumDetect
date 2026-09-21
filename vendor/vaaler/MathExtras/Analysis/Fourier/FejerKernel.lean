/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerPoUCancellation
import MathExtras.NumberTheory.Analysis.VaalerGRegularityProof
import MathExtras.NumberTheory.Analysis.VaalerGCesMemLp

/-!
# A consolidated Fejér-kernel toolkit (translation invariance + L² membership)

Mathlib has no Fejér theory; the repo's facts are scattered across ~10 Vaaler files. This module
consolidates the reusable core, with the two load-bearing facts for the Cesàro/Fejér L² arguments:

* **`eLpNorm_comp_sub_right` / `memLp_comp_sub_right`** — TRANSLATION INVARIANCE: every shifted copy
  `f(· − s)` has the *same* L² norm.  This is exactly why the *sharp* shifted-Fejér-derivative sum
  cannot converge in L² (DEAD_ENDS #22: each term has a fixed L² mass, no per-term decay) while only
  the *Cesàro* average cancels.  The Fejér mechanism lives here.
* **`memLp_deriv_fejerK_two`** — the base kernel derivative `deriv fejerK ∈ L²` (its `O(1/x²)` decay,
  `abs_deriv_fejerK_le`, gives `≤ A(1+x²)⁻¹`, hence square-integrable).  With translation invariance,
  every `deriv fejerK(· − s)` is `MemLp 2` with the *same* norm.

`fejerK x = if x = 0 then 1 else (sin πx/π)²·x⁻²` (`VaalerBeurlingNonneg`).
No `axiom`, no `sorry`.
-/

noncomputable section

open MeasureTheory MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open scoped ENNReal

namespace MathExtras.Analysis.Fourier.FejerKernel

/-- **Translation is measure-preserving** for Lebesgue on `ℝ`: `x ↦ x − s`. -/
theorem measurePreserving_sub_right (s : ℝ) :
    MeasurePreserving (fun x : ℝ => x - s) (volume : Measure ℝ) (volume : Measure ℝ) := by
  have h := measurePreserving_add_right (volume : Measure ℝ) (-s)
  simpa [sub_eq_add_neg] using h

/-- **L² (and Lᵖ) norm is translation-invariant.**  `‖f(· − s)‖_p = ‖f‖_p`. -/
theorem eLpNorm_comp_sub_right {f : ℝ → ℂ} (hf : AEStronglyMeasurable f (volume : Measure ℝ))
    (s : ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x => f (x - s)) p (volume : Measure ℝ) = eLpNorm f p (volume : Measure ℝ) := by
  have h : (fun x => f (x - s)) = f ∘ (fun x => x - s) := rfl
  rw [h, eLpNorm_comp_measurePreserving hf (measurePreserving_sub_right s)]

/-- **A translate of an Lᵖ function is Lᵖ** (with equal norm). -/
theorem memLp_comp_sub_right {f : ℝ → ℂ} {p : ℝ≥0∞} (hf : MemLp f p (volume : Measure ℝ)) (s : ℝ) :
    MemLp (fun x => f (x - s)) p (volume : Measure ℝ) :=
  hf.comp_measurePreserving (measurePreserving_sub_right s)

/-! ## §2  The base Fejér kernel derivative is `L²` -/

/-- `deriv fejerK` is continuous (the `s = 0` instance of the proven shifted continuity). -/
theorem continuous_deriv_fejerK :
    Continuous (deriv fejerK) := by
  have h := MathExtras.NumberTheory.Analysis.VaalerGRegularityProof.continuous_deriv_fejerK_shift 0
  simpa [sub_zero] using h

/-- **`deriv fejerK ∈ L²`** (as a `ℂ`-valued function).  From its `O(1/x²)` decay
(`abs_deriv_fejerK_le` for `|x| ≥ 1`, continuity-bounded on `[-1,1]`) ⟹ a global `A·(1+x²)⁻¹`
envelope ⟹ square-integrable. -/
theorem memLp_deriv_fejerK_two :
    MemLp (fun x => ((deriv fejerK x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  -- Continuity of the ℂ-cast.
  have hcont : Continuous (fun x => ((deriv fejerK x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_deriv_fejerK
  -- Compact bound on `[-1,1]`: `B := sup_{|x|≤1} |deriv fejerK x|`.
  obtain ⟨B, hB0, hBbnd⟩ :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |x| ≤ 1 → |deriv fejerK x| ≤ B := by
    obtain ⟨x₀, hx₀mem, hx₀max⟩ :=
      (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_isMaxOn
        ⟨0, by norm_num⟩ (continuous_abs.comp continuous_deriv_fejerK).continuousOn
    refine ⟨|deriv fejerK x₀|, abs_nonneg _, fun x hx => ?_⟩
    exact hx₀max (by rw [Set.mem_Icc]; exact abs_le.mp hx)
  -- Global `A·(1+x²)⁻¹` envelope via `large_le_of_decay_one`.
  have hglob : ∀ x : ℝ, ‖((deriv fejerK x : ℝ) : ℂ)‖ ≤
      (2 * max (2 / Real.pi + 2 / Real.pi ^ 2) 0 + 2 * B) * (1 + x ^ 2)⁻¹ := by
    intro x
    rw [Complex.norm_real]
    exact MathExtras.NumberTheory.Analysis.VaalerGCesMemLp.large_le_of_decay_one hB0
      (fun y hy => MathExtras.NumberTheory.Analysis.VaalerPoUCancellation.abs_deriv_fejerK_le hy)
      hBbnd x
  exact MathExtras.NumberTheory.Analysis.VaalerGCesMemLp.memLp_two_of_continuous_global_decay
    hcont hglob

/-- **Every shifted Fejér-kernel derivative is `L²`** (with the SAME norm as the base kernel). -/
theorem memLp_deriv_fejerK_shift_two (s : ℝ) :
    MemLp (fun x => ((deriv fejerK (x - s) : ℝ) : ℂ)) 2 (volume : Measure ℝ) :=
  memLp_comp_sub_right memLp_deriv_fejerK_two s

/-- **The shifted kernel derivative has the base kernel's `L²` norm** (translation invariance). -/
theorem eLpNorm_deriv_fejerK_shift_eq (s : ℝ) :
    eLpNorm (fun x => ((deriv fejerK (x - s) : ℝ) : ℂ)) 2 (volume : Measure ℝ)
      = eLpNorm (fun x => ((deriv fejerK x : ℝ) : ℂ)) 2 (volume : Measure ℝ) :=
  eLpNorm_comp_sub_right memLp_deriv_fejerK_two.aestronglyMeasurable s 2

end MathExtras.Analysis.Fourier.FejerKernel
