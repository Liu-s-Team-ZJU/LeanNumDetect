import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.ToIntervalMod

/-! Exact elementary estimates and periodicity for real Fourier phases. -/

set_option autoImplicit false

namespace LeanNumDetect

/-- The unit-circle phase is Lipschitz with constant one in its real argument. -/
theorem norm_exp_I_mul_sub_le (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ ≤
      |x - y| := by
  have he : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ)) *
        (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)

/-- Integer-frequency phases are unchanged by choosing representatives in
the standard angular interval `[0,2π)`. -/
theorem exp_I_int_mul_toIcoMod (a : ℤ) (t : ℝ) :
    Complex.exp (Complex.I * (((a : ℝ) * toIcoMod Real.two_pi_pos 0 t : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (((a : ℝ) * t : ℝ) : ℂ)) := by
  let q : ℤ := toIcoDiv Real.two_pi_pos 0 t
  have hw : toIcoMod Real.two_pi_pos 0 t = t - (q : ℝ) * (2 * Real.pi) := by
    simp only [toIcoMod, q, zsmul_eq_mul]
  rw [hw]
  have he : Complex.I * (((a : ℝ) * (t - (q : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) =
      Complex.I * (((a : ℝ) * t : ℝ) : ℂ) - ((a * q : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

end LeanNumDetect
