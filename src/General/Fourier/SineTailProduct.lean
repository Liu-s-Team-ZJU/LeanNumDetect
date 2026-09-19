import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
set_option autoImplicit false
open scoped BigOperators
namespace LeanNumDetect

noncomputable def sineTailProduct (s m : ℕ) (v : ℝ) : ℝ :=
  ∏ j ∈ Finset.range m, (1-v^2/(s+j+1 : ℝ)^2)

theorem sineTailProduct_at_endpoint (s m : ℕ) :
    sineTailProduct s m s =
      ((m.factorial : ℝ) * ((2*s+m).factorial : ℝ) * (s.factorial : ℝ)^2) /
        (((2*s).factorial : ℝ) * ((s+m).factorial : ℝ)^2) := by
  induction m with
  | zero =>
    simp only [sineTailProduct, Finset.prod_range_zero, Nat.add_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
    field_simp
  | succ m ih =>
    unfold sineTailProduct at ih ⊢
    rw [Finset.prod_range_succ, ih]
    simp only [Nat.add_succ, Nat.factorial_succ, Nat.cast_succ, Nat.cast_mul, Nat.cast_add]
    have h₁ : ((2*s).factorial : ℝ) ≠ 0 := by positivity
    have h₂ : ((s+m).factorial : ℝ) ≠ 0 := by positivity
    have h₃ : (s+m+1 : ℝ) ≠ 0 := by positivity
    field_simp
    ring

theorem factorial_midpoint_le (m s : ℕ) :
    (m+s).factorial^2 ≤ m.factorial * (m+2*s).factorial := by
  have hc : (m+s).choose s ≤ (m+2*s).choose s := Nat.choose_le_choose s (by omega)
  have h₁ := Nat.choose_mul_factorial_mul_factorial (show s ≤ m+s by omega)
  have h₂ := Nat.choose_mul_factorial_mul_factorial (show s ≤ m+2*s by omega)
  have he₁ : m+s-s = m := by omega
  have he₂ : m+2*s-s = m+s := by omega
  rw [he₁] at h₁
  rw [he₂] at h₂
  have hm := Nat.mul_le_mul_right (s.factorial*m.factorial*(m+s).factorial) hc
  calc
    _ = (m+s).choose s * (s.factorial*m.factorial*(m+s).factorial) := by rw [← h₁]; ring
    _ ≤ (m+2*s).choose s * (s.factorial*m.factorial*(m+s).factorial) := hm
    _ = _ := by rw [← h₂]; ring

theorem sineTailProduct_endpoint_lower (s m : ℕ) :
    (s.factorial : ℝ)^2 / ((2*s).factorial : ℝ) ≤ sineTailProduct s m s := by
  rw [sineTailProduct_at_endpoint]
  have hc : ((s+m).factorial : ℝ)^2 ≤ (m.factorial : ℝ)*((2*s+m).factorial : ℝ) := by
    exact_mod_cast (by simpa [Nat.add_comm] using factorial_midpoint_le m s)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ (s.factorial : ℝ)^2*((2*s).factorial : ℝ) by positivity)]

theorem sineTailProduct_lower (s m : ℕ) {v : ℝ} (hv : |v| ≤ s) :
    (s.factorial : ℝ)^2 / ((2*s).factorial : ℝ) ≤ sineTailProduct s m v := by
  apply (sineTailProduct_endpoint_lower s m).trans
  unfold sineTailProduct
  apply Finset.prod_le_prod
  · intro j _
    have hs : (0 : ℝ) ≤ s := by positivity
    have hd : (0 : ℝ) < s+j+1 := by positivity
    have hsq : (s : ℝ)^2 ≤ (s+j+1 : ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
    exact sub_nonneg.mpr ((div_le_one (sq_pos_of_pos hd)).2 hsq)
  · intro j _
    have hv2 : v^2 ≤ (s : ℝ)^2 := by nlinarith [sq_abs v, sq_le_sq₀ (abs_nonneg v) (Nat.cast_nonneg (α := ℝ) s) |>.2 hv]
    exact sub_le_sub_left (div_le_div_of_nonneg_right hv2 (sq_nonneg _)) _
theorem reciprocal_central_factorial_lower (s : ℕ) :
    1/(4 : ℝ)^s ≤ (s.factorial : ℝ)^2 / ((2*s).factorial : ℝ) := by
  have he := Nat.choose_mul_factorial_mul_factorial (show s ≤ 2*s by omega)
  rw [show 2*s-s = s by omega] at he
  have heR : ((2*s).choose s : ℝ)*(s.factorial : ℝ)^2 = ((2*s).factorial : ℝ) := by
    exact_mod_cast (by simpa [pow_two, mul_assoc] using he)
  have hc := Nat.choose_le_two_pow (2*s) s
  have hp : (2 : ℕ)^(2*s) = 4^s := by rw [pow_mul]; rfl
  rw [hp] at hc
  have hcR : ((2*s).choose s : ℝ) ≤ (4 : ℝ)^s := by exact_mod_cast hc
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_right hcR (sq_nonneg (s.factorial : ℝ))]
end LeanNumDetect
