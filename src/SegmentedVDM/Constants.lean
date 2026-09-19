import SegmentedVDM.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
namespace SegmentedVDM

noncomputable def clumpBase : ℝ := 2-Real.sqrt (Real.exp 1)

theorem clumpBase_pos : 0 < clumpBase := by
  have hh := Real.sq_sqrt (Real.exp_pos 1).le
  have hn := Real.sqrt_nonneg (Real.exp 1)
  have he := Real.exp_one_lt_three
  dsimp [clumpBase]
  nlinarith

theorem clumpBase_le_half : clumpBase ≤ 1/2 := by
  have hh := Real.sq_sqrt (Real.exp_pos 1).le
  have hn := Real.sqrt_nonneg (Real.exp 1)
  have he := Real.exp_one_gt_d9
  dsimp [clumpBase]
  nlinarith

theorem sqrt_pow_eq_rpow (a : ℝ) (ha : 0 ≤ a) (s : ℕ) :
    (Real.sqrt a)^s = a^((s : ℝ)/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ha]
  congr 1
  ring

/-- Cancel the interpolation coefficient bound and rewrite the averaging
factor in the normalization used in the article. -/
theorem bound_normalization {n s M b : ℕ} (hn : 0 < n) (hs : 0 < s)
    (hM : 0 < M) {a D Δ : ℝ} (ha : 0 < a) (hD : 0 < D) (hΔ : 0 < Δ) :
    Real.sqrt ((M : ℝ)/s*(b+1)) /
      (Real.sqrt n * ((1/Real.sqrt a)^s *
        (Real.sqrt 2/(((M : ℝ)/s)*D*Δ/Real.pi))^(s-1))) =
    a^((s : ℝ)/2) * Real.sqrt ((M : ℝ)*(b+1)/(n*s)) *
      ((M : ℝ)*D*Δ/(Real.sqrt 2*Real.pi*s))^(s-1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have haR := Real.sqrt_pos.2 ha
  have hroot : Real.sqrt ((M : ℝ)/s*(b+1)) / Real.sqrt n =
      Real.sqrt ((M : ℝ)*(b+1)/(n*s)) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    ring
  rw [← sqrt_pow_eq_rpow a ha.le]
  have hf : ((M : ℝ)*D*Δ/(Real.sqrt 2*Real.pi*s)) =
      (Real.sqrt 2/(((M : ℝ)/s)*D*Δ/Real.pi))⁻¹ := by field_simp
  rw [hf, inv_pow, one_div_pow]
  rw [← hroot]
  field_simp

end SegmentedVDM
