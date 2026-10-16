import MultiTuran.Nikolskii.NikolskiiFilter
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The limiting filter constant

Bernoulli's inequality and `cos x ≥ 1 - x² / 2` suffice for the upper
asymptotic bound. No logarithmic expansion or l'Hôpital argument is needed.
-/

set_option autoImplicit false
open Filter
open scoped Topology

namespace LeanNumDetect.MultiTuran.NikolskiiLimit
open NikolskiiFilter
noncomputable section

def filterPower (n m : ℕ) : ℝ :=
  Real.cos (filterAngle m) ^ (2 * n * (m + 1))

def limitingConstant (n : ℕ) : ℝ := Real.pi ^ 2 * (n : ℝ) ^ 2 / 4

def filterMajorant (n m : ℕ) : ℝ := limitingConstant n / filterPower n m

theorem filterPower_pos (n m : ℕ) (hm : 0 < m) : 0 < filterPower n m :=
  pow_pos (filterAngle_cos_pos hm) _

private theorem one_sub_pow_le (a : ℝ) (ha : 0 ≤ a) (K : ℕ) :
    1 - a ^ K ≤ (K : ℝ) * (1 - a) := by
  have h := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ a by linarith) K
  linarith

private theorem power_angle_identity (n m : ℕ) :
    ((2 * n * (m + 1) : ℕ) : ℝ) * filterAngle m ^ 2 / 2 =
      (n : ℝ) * Real.pi ^ 2 / (4 * ((m : ℝ) + 1)) := by
  unfold filterAngle
  push_cast
  field_simp
  ring

/-- A Bernoulli lower bound that tends to one. -/
theorem filterPower_lower (n m : ℕ) (hm : 0 < m) :
    1 - (n : ℝ) * Real.pi ^ 2 / (4 * ((m : ℝ) + 1)) ≤ filterPower n m := by
  have ha := (filterAngle_cos_pos hm).le
  have hB := one_sub_pow_le (Real.cos (filterAngle m)) ha (2 * n * (m + 1))
  have hcos : 1 - Real.cos (filterAngle m) ≤ filterAngle m ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := filterAngle m)]
  have hmul := mul_le_mul_of_nonneg_left hcos
    (Nat.cast_nonneg (2 * n * (m + 1)) : (0 : ℝ) ≤ ((2 * n * (m + 1) : ℕ) : ℝ))
  rw [← mul_div_assoc, power_angle_identity] at hmul
  unfold filterPower
  linarith

theorem filterPower_le_one (n m : ℕ) (hm : 0 < m) : filterPower n m ≤ 1 :=
  pow_le_one₀ (filterAngle_cos_pos hm).le (Real.cos_le_one _)

/-- The denominator in the finite filter estimate tends to one. -/
theorem tendsto_filterPower (n : ℕ) :
    Tendsto (filterPower n) atTop (𝓝 1) := by
  have hsmall : Tendsto (fun m : ℕ =>
      (n : ℝ) * Real.pi ^ 2 / (4 * ((m : ℝ) + 1))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      ((n : ℝ) * Real.pi ^ 2 / 4)
    simp only [mul_zero] at h
    convert h using 1
    funext m
    field_simp
  have hlower : Tendsto (fun m : ℕ =>
      1 - (n : ℝ) * Real.pi ^ 2 / (4 * ((m : ℝ) + 1))) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hsmall)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact filterPower_lower n m hm
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact filterPower_le_one n m hm

/-- A simple majorant has exactly the desired limit `π² n² / 4`. -/
theorem tendsto_filterMajorant (n : ℕ) :
    Tendsto (filterMajorant n) atTop (𝓝 (limitingConstant n)) := by
  change Tendsto (fun m => limitingConstant n / filterPower n m) atTop (𝓝 (limitingConstant n))
  have hc : Tendsto (fun _ : ℕ => limitingConstant n) atTop (𝓝 (limitingConstant n)) :=
    tendsto_const_nhds
  have h := hc.div (tendsto_filterPower n) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  exact h.congr' (Eventually.of_forall (fun _ => rfl))

/-- The sampled coefficient loss is bounded by a sequence with the sharp limit. -/
theorem sampled_filter_loss_le_majorant (n m : ℕ) (hm : 0 < m) :
    ((n : ℝ) * m) * (1 / filterPower n m - 1) ≤ filterMajorant n m := by
  have ha := (filterAngle_cos_pos hm).le
  have hB := one_sub_pow_le (Real.cos (filterAngle m)) ha (2 * n * (m + 1))
  have hcos : 1 - Real.cos (filterAngle m) ≤ filterAngle m ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := filterAngle m)]
  have hmul := mul_le_mul_of_nonneg_left hcos
    (Nat.cast_nonneg (2 * n * (m + 1)) : (0 : ℝ) ≤ ((2 * n * (m + 1) : ℕ) : ℝ))
  rw [← mul_div_assoc, power_angle_identity] at hmul
  have hbern : 1 - filterPower n m ≤
      (n : ℝ) * Real.pi ^ 2 / (4 * ((m : ℝ) + 1)) := hB.trans hmul
  have hscaled := mul_le_mul_of_nonneg_left hbern
    (by positivity : (0 : ℝ) ≤ (n : ℝ) * m)
  have hid : ((n : ℝ) * m) *
      ((n : ℝ) * Real.pi ^ 2 / (4 * ((m : ℝ) + 1))) =
      limitingConstant n * ((m : ℝ) / ((m : ℝ) + 1)) := by
    unfold limitingConstant
    field_simp
  rw [hid] at hscaled
  have hratio : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)).2
    linarith
  have hnum : ((n : ℝ) * m) * (1 - filterPower n m) ≤ limitingConstant n :=
    hscaled.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hratio (by unfold limitingConstant; positivity))
  have hden := filterPower_pos n m hm
  calc
    _ = (((n : ℝ) * m) * (1 - filterPower n m)) / filterPower n m := by
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hnum hden.le

/-- Rewriting the power of the polynomial-filter bound into its denominator. -/
theorem filter_bound_power (n m : ℕ) :
    (1 / Real.cos (filterAngle m) ^ (m + 1)) ^ (2 * n) = 1 / filterPower n m := by
  rw [div_pow, one_pow, ← pow_mul]
  congr 2
  ring

end
end LeanNumDetect.MultiTuran.NikolskiiLimit
