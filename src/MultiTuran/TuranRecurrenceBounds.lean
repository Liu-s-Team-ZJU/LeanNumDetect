import MultiTuran.TuranRecurrence

/-! # Degree-sharp bounds for the Turán recurrence coefficient -/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.TuranRecurrence
noncomputable section

/-- A generating-function bound for the partial binomial majorant. -/
theorem majorant_weighted_le (r M : ℕ) (hrM : r ≤ M)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x^r * majorant (r+1) M ≤ (1+2*x)^M := by
  calc
    _ = ∑ j ∈ Finset.range (r+1), x^r * ((2 : ℝ)^j * (M.choose j : ℝ)) := by
      rw [majorant, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range (r+1), (2*x)^j * (M.choose j : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjr : j ≤ r := by simpa using Finset.mem_range.mp hj
      calc
        _ = ((2 : ℝ)^j * (M.choose j : ℝ)) * x^r := by ring
        _ ≤ ((2 : ℝ)^j * (M.choose j : ℝ)) * x^j :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 hjr) (by positivity)
        _ = _ := by rw [mul_pow]; ring
    _ ≤ ∑ j ∈ Finset.range (M+1), (2*x)^j * (M.choose j : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro j _ _
      positivity
    _ = (1+2*x)^M := by
      simpa only [one_pow, mul_one, add_comm (2*x) 1] using (add_pow (2*x) 1 M).symm

/-- The precise degree `r` has an absolute base constant, with no loss
depending on the number of terms. -/
theorem majorant_le (r M : ℕ) (hr : 0 < r) (hrM : r ≤ M) :
    majorant (r+1) M ≤ (2 * Real.exp 1 * M / r)^r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hM : (0 : ℝ) < M := by exact_mod_cast hr.trans_le hrM
  have hrMR : (r : ℝ) ≤ M := by exact_mod_cast hrM
  let x : ℝ := (r : ℝ)/(2*M)
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_one (by positivity : (0 : ℝ) < 2*M)).mpr
    linarith
  have hweight := majorant_weighted_le r M hrM hx.le hx1
  have hexp : (1+2*x)^M ≤ Real.exp (r : ℝ) := by
    calc
      _ ≤ (Real.exp (2*x))^M :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2*x)]) M
      _ = Real.exp ((M : ℝ)*(2*x)) := (Real.exp_nat_mul (2*x) M).symm
      _ = _ := by congr 1; dsimp [x]; field_simp
  have hfactor : x^r * (2 * Real.exp 1 * M / r)^r = Real.exp (r : ℝ) := by
    rw [← mul_pow]
    have hxbase : x * (2 * Real.exp 1 * M / r) = Real.exp 1 := by
      dsimp [x]
      field_simp
    rw [hxbase, ← Real.exp_nat_mul]
    simp
  apply (mul_le_mul_iff_right₀ (pow_pos hx r)).mp
  rw [hfactor]
  exact hweight.trans hexp

/-- The discrete Turán estimate, uniform over all roots in the closed unit
disk, with the exact exponent `n - 1`. -/
theorem unit_powerSum_norm_le_degree {n : ℕ} (hn : 2 ≤ n)
    (z c : Fin n → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hinitial : ∀ k < n, ‖powerSum z c k‖ ≤ B) {M : ℕ} (hM : n-1 ≤ M) :
    ‖powerSum z c M‖ ≤ B * (2 * Real.exp 1 * M / (n-1 : ℕ))^(n-1) := by
  have h := unit_powerSum_norm_le z c hz hB hinitial M
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hB
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
    majorant_le (n-1) M (by omega) hM

end
end LeanNumDetect.MultiTuran.TuranRecurrence
