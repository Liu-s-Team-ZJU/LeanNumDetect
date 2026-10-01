import Mathlib.Analysis.Convex.Deriv

set_option autoImplicit false

open Set

namespace LeanNumDetect

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strict convexity along every nonconstant segment yields strict convexity on the domain. -/
theorem strictConvexOn_of_segment_strictConvex
    (s : Set E) (f : E → ℝ) (hs : Convex ℝ s)
    (hline : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      StrictConvexOn ℝ (Icc (0 : ℝ) 1)
        (fun t : ℝ => f ((1 - t) • x + t • y))) :
    StrictConvexOn ℝ s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have h₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h := (hline x hx y hy hxy).2 h₀ h₁ (by norm_num) ha hb hab
  have hcoeff : 1 - b = a := by linarith
  simpa only [mul_zero, mul_one, zero_add, sub_zero, sub_self,
    zero_smul, one_smul, add_zero, hcoeff, smul_eq_mul] using h

/-- Positivity of the second derivative along every nonconstant segment yields
strict convexity on a convex domain. -/
theorem strictConvexOn_of_segment_deriv2_pos
    (s : Set E) (f : E → ℝ) (hs : Convex ℝ s)
    (hf : ContinuousOn f s)
    (hsecond : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ∀ t ∈ Icc (0 : ℝ) 1,
        0 < (deriv^[2] (fun t : ℝ => f ((1 - t) • x + t • y))) t) :
    StrictConvexOn ℝ s f := by
  apply strictConvexOn_of_segment_strictConvex s f hs
  intro x hx y hy hxy
  let line : ℝ → E := fun t => (1 - t) • x + t • y
  have hlinecont : Continuous line := by
    dsimp [line]
    fun_prop
  have hlineMaps : MapsTo line (Icc (0 : ℝ) 1) s := by
    intro t ht
    exact hs hx hy (by linarith [ht.2]) ht.1 (by ring)
  have hlineQ : ContinuousOn (fun t : ℝ => f (line t)) (Icc (0 : ℝ) 1) := by
    exact hf.comp hlinecont.continuousOn hlineMaps
  exact strictConvexOn_of_deriv2_pos' (convex_Icc 0 1) hlineQ
    (hsecond x hx y hy hxy)

end

end LeanNumDetect
