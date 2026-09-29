import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Exact logarithmic sampling arithmetic for the DFT-grid coherence bound. -/

set_option autoImplicit false

namespace LeanNumDetect.RandSamp

/-- The manuscript's sampling rate absorbs all nonzero DFT-offset tails.
Here `L` is the number of grid points, in any dimension. -/
theorem dft_failure_bound_of_sample_size {L r m ρ η : ℝ}
    (hL : 1 < L) (hr : 1 < r) (hρ : 0 < ρ) (hη : 0 < η)
    (hsample : 4 * (r - 1) ^ 2 / ρ ^ 2 *
      Real.log (4 * (L - 1) / η) ≤ m) :
    (L - 1) * (4 * Real.exp (-m * (ρ / (r - 1)) ^ 2 / 4)) ≤ η := by
  have hden : 0 < (r - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr)
  have hρsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hlog : Real.log (4 * (L - 1) / η) ≤
      m * ρ ^ 2 / (4 * (r - 1) ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * (r - 1) ^ 2)).2
    have hs : (4 * (r - 1) ^ 2 * Real.log (4 * (L - 1) / η)) / ρ ^ 2 ≤ m := by
      simpa only [div_mul_eq_mul_div] using hsample
    have hh := (div_le_iff₀ hρsq).1 hs
    nlinarith
  have hexp : Real.exp (-Real.log (4 * (L - 1) / η)) = η / (4 * (L - 1)) := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    exact inv_div _ _
  have htail : Real.exp (-m * (ρ / (r - 1)) ^ 2 / 4) ≤ η / (4 * (L - 1)) := by
    rw [← hexp]
    apply Real.exp_le_exp.mpr
    calc
      -m * (ρ / (r - 1)) ^ 2 / 4 = -(m * ρ ^ 2 / (4 * (r - 1) ^ 2)) := by
        field_simp
      _ ≤ -Real.log (4 * (L - 1) / η) := neg_le_neg hlog
  calc
    (L - 1) * (4 * Real.exp (-m * (ρ / (r - 1)) ^ 2 / 4)) ≤
        (L - 1) * (4 * (η / (4 * (L - 1)))) := by gcongr
    _ = η := by field_simp [ne_of_gt (sub_pos.mpr hL)]

end LeanNumDetect.RandSamp
