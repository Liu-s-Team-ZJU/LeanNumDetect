import General.Convex.PeakBallStrictConvex
import General.Convex.CurvatureTransfer

set_option autoImplicit false
open Set
namespace LeanNumDetect
noncomputable section

/-- A mixed third-derivative bound along a radial segment controls directional curvature at its endpoint. -/
theorem lineCurvature_lower_of_radial_deriv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : E → ℝ) (node z w : E) (Ω ρ : ℝ)
    (hdiff : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ
        (fun s : ℝ => lineCurvature Q (node + s • (z - node)) w) t)
    (hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      |deriv (fun s : ℝ => lineCurvature Q (node + s • (z - node)) w) t| ≤
        8 * Ω ^ 3 * ρ * ‖w‖ ^ 2) :
    lineCurvature Q node w - 8 * Ω ^ 3 * ρ * ‖w‖ ^ 2 ≤
      lineCurvature Q z w := by
  have h := curvature_lower_of_radial_deriv_bound
    (fun s : ℝ => lineCurvature Q (node + s • (z - node)) w)
    (8 * Ω ^ 3 * ρ * ‖w‖ ^ 2) hdiff hderiv
  simpa using h

end
end LeanNumDetect
