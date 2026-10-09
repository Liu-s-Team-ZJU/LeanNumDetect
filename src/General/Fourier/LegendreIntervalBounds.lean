import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! The interval bound for solutions of the shifted Legendre equation.
The Sonin energy is monotone on each half of the unit interval. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Polynomial

namespace LeanNumDetect.PolynomialEvaluationBounds
noncomputable section

theorem polynomial_unit_abs_le_one_of_legendreEquation
    (P : ℝ[X]) {eigenvalue : ℝ} (heigenvalue : 0 < eigenvalue)
    (hODE : ∀ x ∈ Icc (0 : ℝ) 1,
      x * (1 - x) * P.derivative.derivative.eval x +
        (1 - 2 * x) * P.derivative.eval x + eigenvalue * P.eval x = 0)
    (hzero : (P.eval 0)^2 ≤ 1) (hone : (P.eval 1)^2 ≤ 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : |P.eval x| ≤ 1 := by
  let E : ℝ → ℝ := fun t =>
    (P.eval t)^2 + t * (1 - t) / eigenvalue * (P.derivative.eval t)^2
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt E ((2 * t - 1) / eigenvalue * (P.derivative.eval t)^2) t := by
    have hw : HasDerivAt (fun u : ℝ => u * (1 - u) / eigenvalue) ((1 - 2 * t) / eigenvalue) t := by
      convert! ((hasDerivAt_id t).mul ((hasDerivAt_const t 1).sub (hasDerivAt_id t))).div_const eigenvalue using 1
      simp only [Pi.sub_apply, id_eq]
      ring
    have hraw := ((P.hasDerivAt t).pow 2).add
      (hw.mul ((P.derivative.hasDerivAt t).pow 2))
    convert! hraw using 1
    try dsimp [E]
    field_simp [ne_of_gt heigenvalue]
    have hh := congrArg (fun z : ℝ => 2 * P.derivative.eval t * z) (hODE t ht)
    nlinarith [hh]
  have hleft : AntitoneOn E (Icc (0 : ℝ) (1 / 2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · exact (show Continuous E by dsimp [E]; fun_prop).continuousOn
    · intro t ht
      exact (hd t ⟨(interior_subset ht).1, by linarith [(interior_subset ht).2]⟩).hasDerivWithinAt
    · intro t ht
      apply mul_nonpos_of_nonpos_of_nonneg
      · apply div_nonpos_of_nonpos_of_nonneg
        · linarith [(interior_subset ht).2]
        · exact heigenvalue.le
      · exact sq_nonneg _
  have hright : MonotoneOn E (Icc (1 / 2 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    · exact (show Continuous E by dsimp [E]; fun_prop).continuousOn
    · intro t ht
      exact (hd t ⟨by linarith [(interior_subset ht).1], (interior_subset ht).2⟩).hasDerivWithinAt
    · intro t ht
      apply mul_nonneg
      · apply div_nonneg
        · linarith [(interior_subset ht).1]
        · exact heigenvalue.le
      · exact sq_nonneg _
  have hE : E x ≤ 1 := by
    by_cases hhalf : x ≤ 1 / 2
    · have h := hleft ⟨by norm_num, by norm_num⟩ ⟨hx.1, hhalf⟩ hx.1
      exact h.trans (by simpa [E] using hzero)
    · have h := hright ⟨le_of_not_ge hhalf, hx.2⟩ ⟨by norm_num, by norm_num⟩ hx.2
      exact h.trans (by simpa [E] using hone)
  have hnonneg : 0 ≤ x * (1 - x) / eigenvalue * (P.derivative.eval x)^2 := by
    exact mul_nonneg (div_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) heigenvalue.le) (sq_nonneg _)
  have hsq : (P.eval x)^2 ≤ 1 := by dsimp [E] at hE; linarith
  exact (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).1 (by simpa using hsq)

/-- The square form used for normalized shifted Legendre polynomials. -/
theorem realPolynomial_unit_sq_le_one_of_legendre_ode
    {P : ℝ[X]} {eigenvalue : ℝ} (hpositive : 0 < eigenvalue)
    (hode : ∀ x ∈ Icc (0 : ℝ) 1,
      x * (1 - x) * P.derivative.derivative.eval x +
        (1 - 2 * x) * P.derivative.eval x + eigenvalue * P.eval x = 0)
    (hzero : (P.eval 0)^2 = 1) (hone : (P.eval 1)^2 = 1)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : (P.eval x)^2 ≤ 1 := by
  have h := polynomial_unit_abs_le_one_of_legendreEquation P hpositive hode hzero.le hone.le hx
  have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).2 h
  simpa only [sq_abs, one_pow] using hs

end
end LeanNumDetect.PolynomialEvaluationBounds
