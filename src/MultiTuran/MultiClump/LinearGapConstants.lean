import MultiTuran.MultiClump.NormingConstants

/-! # Frame and coefficient budgets for the linear clump gap

Using the separated-frame parameter `7/5` leaves enough of the original
selector coefficient budget to control the continuous translations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

theorem linearGapFrameParameter_admissible :
    1 / (2 * Real.log 2) < (7 / 5 : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).mpr
  nlinarith [Real.log_two_gt_d9]

theorem linearGapFrameConstant_lower :
    (9 / 16 : ℝ) ≤ 2 - Real.exp (5 / 14 : ℝ) := by
  have h := Real.exp_bound' (x := (5 / 14 : ℝ)) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem linearGapFrameConstant_pos : 0 < 2 - Real.exp (5 / 14 : ℝ) := by
  linarith [linearGapFrameConstant_lower]

theorem linearGapFrameInverseSqrt_upper :
    1 / Real.sqrt (2 - Real.exp (5 / 14 : ℝ)) ≤ (4 / 3 : ℝ) := by
  have hs := Real.sq_sqrt linearGapFrameConstant_pos.le
  have hs0 := Real.sqrt_nonneg (2 - Real.exp (5 / 14 : ℝ))
  have hslo : (3 / 4 : ℝ) ≤ Real.sqrt (2 - Real.exp (5 / 14 : ℝ)) := by
    nlinarith [linearGapFrameConstant_lower]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr linearGapFrameConstant_pos)).mpr
  nlinarith

theorem originalFrameInverseSqrt_lower :
    (5 / 3 : ℝ) ≤ 1 / Real.sqrt (2 - Real.exp (1 / 2 : ℝ)) := by
  have hexp := Real.sum_le_exp_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at hexp
  have hlog : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hexp2 := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp2
  have hpos : 0 < 2 - Real.exp (1 / 2 : ℝ) := by linarith
  have hs := Real.sq_sqrt hpos.le
  have hs0 := Real.sqrt_nonneg (2 - Real.exp (1 / 2 : ℝ))
  have hsup : Real.sqrt (2 - Real.exp (1 / 2 : ℝ)) ≤ (3 / 5 : ℝ) := by
    nlinarith
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hpos)).mpr
  nlinarith

theorem linearGapFrameMass_upper (m : ℕ) :
    (1 / Real.sqrt (2 - Real.exp (5 / 14 : ℝ))) ^ m ≤ (4 / 3 : ℝ) ^ m :=
  pow_le_pow_left₀ (by positivity) linearGapFrameInverseSqrt_upper m

theorem originalFrameMass_lower (m : ℕ) :
    (5 / 3 : ℝ) ^ m ≤ (1 / Real.sqrt (2 - Real.exp (1 / 2 : ℝ))) ^ m :=
  pow_le_pow_left₀ (by norm_num) originalFrameInverseSqrt_lower m

theorem linearGap_rational_power_lower {m : ℕ} (hm : 7 ≤ m) :
    2 * (m : ℝ) / 3 ≤ (5 / 4 : ℝ) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      have hmR : (7 : ℝ) ≤ m := by exact_mod_cast hm
      calc
        2 * ((m + 1 : ℕ) : ℝ) / 3 ≤ (5 / 4 : ℝ) * (2 * (m : ℝ) / 3) := by
          push_cast
          nlinarith
        _ ≤ (5 / 4 : ℝ) * (5 / 4 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (5 / 4 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring

theorem linearGap_rational_selector_ratio {m : ℕ} (hm : 7 ≤ m) :
    (5 / 4 : ℝ) ^ (m - 1) * (1 + (4 / 3 : ℝ) ^ m) ≤
      1 + (5 / 3 : ℝ) ^ m := by
  have hm1 : m - 1 + 1 = m := by omega
  have hsmall : (3 / 4 : ℝ) ^ m ≤ 1 / 4 := by
    have h := pow_le_pow_of_le_one (a := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
      (show 5 ≤ m by omega)
    exact h.trans (by norm_num)
  have hprev : (5 / 4 : ℝ) ^ (m - 1) = (4 / 5 : ℝ) * (5 / 4 : ℝ) ^ m := by
    have hpow : (5 / 4 : ℝ) ^ m = (5 / 4 : ℝ) ^ (m - 1) * (5 / 4 : ℝ) := by
      rw [← pow_succ, hm1]
    rw [hpow]
    ring
  have hfactor : (5 / 4 : ℝ) ^ m = (5 / 3 : ℝ) ^ m * (3 / 4 : ℝ) ^ m := by
    rw [← mul_pow]
    congr 1
    norm_num
  have hfirst : (5 / 4 : ℝ) ^ (m - 1) ≤ (1 / 5 : ℝ) * (5 / 3 : ℝ) ^ m := by
    calc
      _ = (4 / 5 : ℝ) * (5 / 3 : ℝ) ^ m * (3 / 4 : ℝ) ^ m := by
        rw [hprev, hfactor]
        ring
      _ ≤ (4 / 5 : ℝ) * (5 / 3 : ℝ) ^ m * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by ring
  have hsecond : (5 / 4 : ℝ) ^ (m - 1) * (4 / 3 : ℝ) ^ m =
      (4 / 5 : ℝ) * (5 / 3 : ℝ) ^ m := by
    rw [hprev]
    calc
      _ = (4 / 5 : ℝ) * ((5 / 4 : ℝ) * (4 / 3 : ℝ)) ^ m := by
        rw [mul_pow]
        ring
      _ = _ := by norm_num
  nlinarith only [hfirst, hsecond]

/-- A stronger rational budget than the eventual coefficient estimate. -/
theorem linearGap_rational_mass_budget {m : ℕ} (hm : 2 ≤ m) :
    (2 * (m : ℝ) / 3) ^ (m - 1) * (1 + (4 / 3 : ℝ) ^ m) ^ m ≤
      (1 + (5 / 3 : ℝ) ^ m) ^ m := by
  by_cases hm7 : 7 ≤ m
  · have hpow := pow_le_pow_left₀ (show 0 ≤ 2 * (m : ℝ) / 3 by positivity)
      (linearGap_rational_power_lower hm7) (m - 1)
    calc
      _ ≤ ((5 / 4 : ℝ) ^ m) ^ (m - 1) * (1 + (4 / 3 : ℝ) ^ m) ^ m :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = ((5 / 4 : ℝ) ^ (m - 1) * (1 + (4 / 3 : ℝ) ^ m)) ^ m := by
        rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm m (m - 1)]
      _ ≤ _ := pow_le_pow_left₀ (by positivity)
        (linearGap_rational_selector_ratio hm7) m
  · have hm6 : m ≤ 6 := by omega
    interval_cases m <;> norm_num

/-- The improved frame pays for the translations while retaining exactly
the selector constant used in the original norming coefficient `η₀`. -/
theorem linearGap_mass_budget {m : ℕ} (hm : 2 ≤ m) :
    (2 * (m : ℝ) / 3) ^ (m - 1) *
      ((1 + (1 / Real.sqrt (2 - Real.exp (5 / 14 : ℝ))) ^ m) ^ m - 1) ≤
        clumpSelectorBound m := by
  have hfactor : 0 ≤ (2 * (m : ℝ) / 3) ^ (m - 1) := by positivity
  have hnew := pow_le_pow_left₀
    (show 0 ≤ 1 + (1 / Real.sqrt (2 - Real.exp (5 / 14 : ℝ))) ^ m by positivity)
    (add_le_add (le_refl (1 : ℝ)) (linearGapFrameMass_upper m)) m
  have hold := pow_le_pow_left₀ (show 0 ≤ 1 + (5 / 3 : ℝ) ^ m by positivity)
    (add_le_add (le_refl (1 : ℝ)) (originalFrameMass_lower m)) m
  calc
    _ ≤ (2 * (m : ℝ) / 3) ^ (m - 1) *
        (1 + (1 / Real.sqrt (2 - Real.exp (5 / 14 : ℝ))) ^ m) ^ m := by
      nlinarith only [hfactor]
    _ ≤ (2 * (m : ℝ) / 3) ^ (m - 1) * (1 + (4 / 3 : ℝ) ^ m) ^ m :=
      mul_le_mul_of_nonneg_left hnew hfactor
    _ ≤ (1 + (5 / 3 : ℝ) ^ m) ^ m := linearGap_rational_mass_budget hm
    _ ≤ (1 + (1 / Real.sqrt (2 - Real.exp (1 / 2 : ℝ))) ^ m) ^ m := hold
    _ ≤ clumpSelectorBound m := by unfold clumpSelectorBound; linarith

end
end LeanNumDetect.MultiTuran.MultiClump
