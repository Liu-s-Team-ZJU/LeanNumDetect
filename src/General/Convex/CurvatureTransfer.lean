import Mathlib

/-! Curvature transfer under a mixed third-derivative bound and a perturbation bound. -/

set_option autoImplicit false
open Set
namespace LeanNumDetect
noncomputable section

/-- A derivative bound controls how much directional curvature changes along a radial segment. -/
theorem curvature_lower_of_radial_deriv_bound
    (H : ℝ → ℝ) (C : ℝ)
    (hdiff : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ H t)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1, |deriv H t| ≤ C) :
    H 0 - C ≤ H 1 := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Icc (0 : ℝ) 1) (x := 0) (y := 1) hdiff
    (by intro t ht; simpa only [Real.norm_eq_abs] using hderiv t ht)
    (convex_Icc 0 1) (by simp) (by simp)
  have habs : |H 1 - H 0| ≤ C := by simpa using h
  linarith [(abs_le.mp habs).1]

/-- A derivative bound on a radial interval of length `ρ` yields a `Cρ` curvature loss. -/
theorem curvature_lower_of_radial_deriv_bound_at_radius
    (H : ℝ → ℝ) (C ρ : ℝ) (hρ : 0 ≤ ρ)
    (hdiff : ∀ t ∈ Icc (0 : ℝ) ρ, DifferentiableAt ℝ H t)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) ρ, |deriv H t| ≤ C) :
    H 0 - C * ρ ≤ H ρ := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Icc (0 : ℝ) ρ) (x := 0) (y := ρ) hdiff
    (by intro t ht; simpa only [Real.norm_eq_abs] using hderiv t ht)
    (convex_Icc 0 ρ) (left_mem_Icc.mpr hρ) (right_mem_Icc.mpr hρ)
  have habs : |H ρ - H 0| ≤ C * ρ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hρ] using h
  linarith [(abs_le.mp habs).1]

/-- Source curvature survives radial variation and projector perturbation. -/
theorem perturbed_curvature_pos_of_bounds
    (c Ω ρ ε Hsource Hexact Hnoisy : ℝ)
    (hsource : 2 * c ^ 2 ≤ Hsource)
    (hvariation : Hsource - 8 * Ω ^ 3 * ρ ≤ Hexact)
    (hperturbation : Hexact - 4 * Ω ^ 2 * ε ≤ Hnoisy)
    (hradius : 8 * Ω ^ 3 * ρ ≤ c ^ 2)
    (hnoise : 4 * Ω ^ 2 * ε < c ^ 2 / 2) :
    c ^ 2 / 2 < Hnoisy := by
  linarith

end
end LeanNumDetect
