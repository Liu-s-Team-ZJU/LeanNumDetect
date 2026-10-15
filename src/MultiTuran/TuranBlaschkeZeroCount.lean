import MultiTuran.TuranBlaschkeQuotient
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Counting actual zeros from a genuine growth bound

On the disk of radius four, every zero in the disk of radius two contributes
at most `6/7` at every point in the unit disk. The partial Blaschke quotient
and the maximum principle therefore give an elementary quantitative count.
-/

set_option autoImplicit false
open scoped BigOperators
open Set Metric

namespace LeanNumDetect.MultiTuran
noncomputable section

theorem norm_blaschkeFactor_four_le {root w : ℂ}
    (hroot : ‖root‖ ≤ 2) (hw : ‖w‖ ≤ 1) :
    ‖blaschkeFactor 4 root w‖ ≤ (6/7 : ℝ) := by
  convert norm_blaschkeFactor_le (R := 4) (s := 2) (ρ := 1)
    (by norm_num) hroot hw (by norm_num) using 1 <;> norm_num

/-- Genuine zero count including arbitrary selected multiplicities. No
zero-count or factorization estimate is assumed. -/
theorem selected_zero_count_le_of_growth {N : ℕ} {roots : Fin N → ℂ}
    (hroots : ∀ i, ‖roots i‖ ≤ 2) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 4))
    (horder : ∀ z ∈ closedBall (0 : ℂ) 4,
      (zeroMultiplicity roots z : WithTop ℤ) ≤ meromorphicOrderAt f z)
    {M S : ℝ} (hM : 0 < M)
    (hbound : ∀ z ∈ sphere (0 : ℂ) 4, ‖f z‖ ≤ M) {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hgrowth : M ≤ Real.exp S*‖f w‖) : (N : ℝ) ≤ 7*S := by
  have hroots4 : ∀ i, ‖roots i‖ < (4 : ℝ) := fun i => (hroots i).trans_lt (by norm_num)
  obtain ⟨h,_han,hfactor,_hcircle,_hdom,hupper⟩ :=
    exists_blaschke_factor_of_zero_multiplicities (by norm_num : (0 : ℝ) < 4)
      hroots4 hf horder hbound
  have hw4 : w ∈ closedBall (0 : ℂ) 4 := by
    simp only [mem_closedBall,dist_zero_right]
    linarith
  have hprod : ‖blaschkeProduct 4 roots w‖ ≤ (6/7 : ℝ)^N := by
    unfold blaschkeProduct
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin N, (6/7 : ℝ) := Finset.prod_le_prod
        (fun _ _ => norm_nonneg _) (fun i _ => norm_blaschkeFactor_four_le (hroots i) hw)
      _ = _ := by simp [div_pow]
  have hfw : ‖f w‖ ≤ (6/7 : ℝ)^N*M := by
    rw [hfactor w hw4,norm_mul]
    exact mul_le_mul hprod (hupper w hw4) (norm_nonneg _) (by positivity)
  have hscaled : M ≤ (Real.exp S*(6/7 : ℝ)^N)*M := by
    calc
      _ ≤ Real.exp S*‖f w‖ := hgrowth
      _ ≤ Real.exp S*((6/7 : ℝ)^N*M) :=
        mul_le_mul_of_nonneg_left hfw (Real.exp_nonneg _)
      _ = _ := by ring
  have hone : 1 ≤ Real.exp S*(6/7 : ℝ)^N := by
    nlinarith only [hscaled,hM]
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hone
  rw [Real.log_one, Real.log_mul (Real.exp_ne_zero _) (by positivity),
    Real.log_exp, Real.log_pow] at hlog
  have hq : Real.log (6/7 : ℝ) ≤ -(1/7 : ℝ) := by
    calc
      _ ≤ 6/7-1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6/7)
      _ = _ := by norm_num
  have hnq := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  linarith

end
end LeanNumDetect.MultiTuran
