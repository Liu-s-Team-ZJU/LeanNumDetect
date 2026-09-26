import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Elementary, fully proved simplifications of the exact Chernoff factors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect.FiniteMatrixSampling

private theorem lower_log_bound {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    δ ^ 2 / 2 ≤ δ + (1 - δ) * Real.log (1 - δ) := by
  let f : ℝ → ℝ := fun x => x + (1 - x) * Real.log (1 - x) - x ^ 2 / 2
  have hd (x : ℝ) (hx : x ∈ Set.Icc 0 δ) :
      HasDerivAt f (-Real.log (1 - x) - x) x := by
    have hn : 1 - x ≠ 0 := by linarith [hx.2]
    have hid := hasDerivAt_id x
    have hsub := (hasDerivAt_const x 1).sub hid
    have hlog := (Real.hasDerivAt_log hn).comp x hsub
    convert! (hid.add (hsub.mul hlog)).sub ((hid.pow 2).div_const 2) using 1
    dsimp
    field_simp
    ring
  have hc : ContinuousOn f (Set.Icc 0 δ) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hmono : MonotoneOn f (Set.Icc 0 δ) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 δ) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (by
        intro x hx
        have hx' : x ∈ Set.Icc 0 δ := interior_subset hx
        have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 - x by linarith [hx'.2])
        linarith)
  have h := hmono (show 0 ∈ Set.Icc 0 δ from ⟨le_rfl, hδ0⟩)
    (show δ ∈ Set.Icc 0 δ from ⟨hδ0, le_rfl⟩) hδ0
  simp only [f, sub_zero, Real.log_one, mul_zero, zero_add, zero_pow (by omega : 2 ≠ 0),
    zero_div] at h
  linarith

private theorem upper_log_bound {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ ^ 2 / 3 ≤ (1 + δ) * Real.log (1 + δ) - δ := by
  have hlog := Real.le_log_one_add_of_nonneg hδ0
  have hden : 0 < δ + 2 := by positivity
  have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1 + δ by positivity)
  have he : (1 + δ) * (2 * δ / (δ + 2)) - δ = δ ^ 2 / (δ + 2) := by
    field_simp
    ring
  have hsq : δ ^ 2 / 3 ≤ δ ^ 2 / (δ + 2) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) hden
    linarith
  linarith

/-- Gaussian simplification of the exact lower Chernoff factor. -/
theorem lower_chernoff_factor_le {δ t : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (ht : 0 ≤ t) :
    (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ t ≤ Real.exp (-(t * δ ^ 2) / 2) := by
  have hp : 0 < 1 - δ := sub_pos.mpr hδ1
  rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hp _)),
    Real.log_div (Real.exp_ne_zero _) (ne_of_gt (Real.rpow_pos_of_pos hp _)),
    Real.log_exp, Real.log_rpow hp]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (lower_log_bound hδ0 hδ1) ht
  nlinarith

/-- Gaussian simplification of the exact upper Chernoff factor for `δ ≤ 1`. -/
theorem upper_chernoff_factor_le {δ t : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : 0 ≤ t) :
    (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ t ≤ Real.exp (-(t * δ ^ 2) / 3) := by
  have hp : 0 < 1 + δ := by positivity
  rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hp _)),
    Real.log_div (Real.exp_ne_zero _) (ne_of_gt (Real.rpow_pos_of_pos hp _)),
    Real.log_exp, Real.log_rpow hp]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (upper_log_bound hδ0 hδ1) ht
  nlinarith

end LeanNumDetect.FiniteMatrixSampling
