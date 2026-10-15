import MultiTuran.MultiClump.BoundFormula
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Exact cancellation in the explicit multi-clump norming constant -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

def clumpSelectorBound (nStar : ℕ) : ℝ :=
  1+(1+(1/Real.sqrt (2-Real.exp (1/2 : ℝ)))^nStar)^nStar

def clumpRestorationFactor (d nStar : ℕ) (C_T : ℝ) : ℝ :=
  2^d*(Real.pi*nStar/2)^(2*d)*(2^d*C_T*(d : ℝ))^(2*(nStar-1))

theorem clumpSelectorBound_pos (nStar : ℕ) : 0 < clumpSelectorBound nStar := by
  unfold clumpSelectorBound
  positivity

theorem clumpRestorationFactor_nonneg (d nStar : ℕ) (C_T : ℝ) (hC_T : 0 ≤ C_T) :
    0 ≤ clumpRestorationFactor d nStar C_T := by
  unfold clumpRestorationFactor
  positivity

theorem inverse_sqrt_frame_pow (nStar : ℕ) :
    (1/Real.sqrt (2-Real.exp (1/2 : ℝ)))^nStar =
      (2-Real.exp (1/2 : ℝ))^(-(nStar : ℝ)/2) := by
  have hlog : (1/2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hexp := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
  have ha : 0 < 2-Real.exp (1/2 : ℝ) := by linarith
  have hsqrt : (Real.sqrt (2-Real.exp (1/2 : ℝ)))^nStar =
      (2-Real.exp (1/2 : ℝ))^((nStar : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ha.le]
    congr 1
    ring
  rw [one_div, inv_pow, hsqrt, ← Real.rpow_neg ha.le]
  congr 1
  ring

theorem multiClumpNormingConstant_mul_energy_loss {d n nStar : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hs : 0 < nStar) {C_T : ℝ} (hC_T : 0 < C_T) :
    multiClumpNormingConstant d n nStar C_T *
      (2*(n : ℝ)^2*clumpRestorationFactor d nStar C_T*(clumpSelectorBound nStar)^2) = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hs0 : (nStar : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hbase : 2^d*C_T*(d : ℝ) ≠ 0 := by positivity
  have hsel : clumpSelectorBound nStar ≠ 0 := ne_of_gt (clumpSelectorBound_pos nStar)
  have hfirst : (2/(Real.pi^2*(nStar : ℝ)^2))^d *
      (2^d*(Real.pi*nStar/2)^(2*d)) = 1 := by
    have he : (2/(Real.pi^2*(nStar : ℝ)^2)) *
        (2*(Real.pi*nStar/2)^2) = 1 := by field_simp
    calc
      _ = ((2/(Real.pi^2*(nStar : ℝ)^2))*(2*(Real.pi*nStar/2)^2))^d := by
        rw [mul_pow, mul_pow, pow_mul]
      _ = 1 := by rw [he, one_pow]
  have hsecond : (1/(2^d*C_T*(d : ℝ)))^(2*(nStar-1)) *
      (2^d*C_T*(d : ℝ))^(2*(nStar-1)) = 1 := by
    rw [← mul_pow, one_div, inv_mul_cancel₀ hbase, one_pow]
  have heq : 1+(1+(2-Real.exp (1/2 : ℝ))^(-(nStar : ℝ)/2))^nStar =
      clumpSelectorBound nStar := by
    unfold clumpSelectorBound
    rw [inverse_sqrt_frame_pow]
  unfold multiClumpNormingConstant clumpRestorationFactor
  rw [heq, zpow_neg, zpow_ofNat]
  calc
    _ = ((1/(2*(n : ℝ)^2))*(2*(n : ℝ)^2)) *
        ((2/(Real.pi^2*(nStar : ℝ)^2))^d*(2^d*(Real.pi*nStar/2)^(2*d))) *
        ((1/(2^d*C_T*(d : ℝ)))^(2*(nStar-1))*(2^d*C_T*(d : ℝ))^(2*(nStar-1))) *
        (((clumpSelectorBound nStar)^2)⁻¹*(clumpSelectorBound nStar)^2) := by ring
    _ = 1 := by
      rw [hfirst,hsecond]
      have hn2 : 2*(n : ℝ)^2 ≠ 0 := by positivity
      rw [one_div, inv_mul_cancel₀ hn2, inv_mul_cancel₀ (pow_ne_zero 2 hsel)]
      norm_num

end
end LeanNumDetect.MultiTuran.MultiClump
