import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # From true scalar derivatives to squared-modulus oscillation

These mean-value consequences apply to actual complex functions, including
the coordinate sections used by the multidimensional Riemann estimate.
-/

set_option autoImplicit false
open Set

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- Squared modulus has Lipschitz coefficient `2B` on the complex disk of
radius `B`, with no differentiability assumption. -/
theorem norm_sq_sub_norm_sq_le {z w : ℂ} {B : ℝ}
    (hz : ‖z‖ ≤ B) (hw : ‖w‖ ≤ B) :
    |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ (2 * B) * ‖z-w‖ := by
  have hsum : 0 ≤ ‖z‖ + ‖w‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hfactor : ‖z‖ ^ 2 - ‖w‖ ^ 2 = (‖z‖+‖w‖) * (‖z‖-‖w‖) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg hsum]
  exact mul_le_mul (by linarith) (abs_norm_sub_norm_le z w)
    (abs_nonneg _) (by linarith [norm_nonneg z])

/-- A bound on the genuine derivative and a pointwise modulus bound give
the actual squared-modulus mean-value estimate on a real interval. -/
theorem norm_sq_variation_of_derivative_bound {f : ℝ → ℂ} {a b B D x y : ℝ}
    (hB : 0 ≤ B) (hf : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hval : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ B)
    (hderiv : ∀ t ∈ Set.Icc a b, ‖deriv f t‖ ≤ D)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |‖f y‖ ^ 2 - ‖f x‖ ^ 2| ≤ (2 * B * D) * |y-x| := by
  have h := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le hf hderiv hx hy
  rw [Real.norm_eq_abs] at h
  calc
    _ ≤ (2 * B) * ‖f y-f x‖ := norm_sq_sub_norm_sq_le (hval y hy) (hval x hx)
    _ ≤ (2 * B) * (D * |y-x|) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

end
end LeanNumDetect.MultiTuran
