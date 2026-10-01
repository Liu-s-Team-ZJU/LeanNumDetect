import NumDetect.MUSICPeakGrowth
import General.Convex.PeakBallStrictConvex

/-! A finite Fourier MUSIC source-ball convexity theorem from growth and curvature bounds. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WithLp Filter
open scoped Topology
namespace LeanNumDetect
namespace NumDetect
noncomputable section

/-- Squared finite-Fourier MUSIC residual in Euclidean coordinates. -/
def finiteFourierSquaredMUSIC
    {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (frequency : ι → Point d) (A : Matrix ι κ ℂ) (n : ℕ)
    (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  rankNoiseSpaceCorrelation frequency A n (ofLp z) ^ 2

/-- Global residual growth and quantitative Hessian bounds make noisy MUSIC strictly convex on a source ball. -/
theorem finiteFourierMUSIC_strictConvexOn_sourceBall_of_bounds
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (frequency : ι → Point d) (A₀ Aσ : Matrix ι κ ℂ)
    (node : Fin n → EuclideanSpace ℝ (Fin d))
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (hn : 0 < n) (Δ c ρ Ω ε : ℝ) (hΔ : 0 < Δ) (hc : 0 ≤ c)
    (hsep : ∀ i k : Fin n, i ≠ k → Δ ≤ dist (node i) (node k))
    (j : Fin n) (hK : K ∈ 𝓝 (node j))
    (hzero : rankNoiseSpaceCorrelation frequency A₀ n (ofLp (node j)) = 0)
    (hgrowth : ∀ y ∈ K,
      c * min (Δ / 4) (finiteSourceDistance hn node y) ≤
        rankNoiseSpaceCorrelation frequency A₀ n (ofLp y))
    (hradiusVariation : ∀ z ∈ Metric.closedBall (node j) ρ, ∀ w : EuclideanSpace ℝ (Fin d),
      lineCurvature (finiteFourierSquaredMUSIC frequency A₀ n) (node j) w -
        8 * Ω ^ 3 * ρ * ‖w‖ ^ 2 ≤
      lineCurvature (finiteFourierSquaredMUSIC frequency A₀ n) z w)
    (hprojectorVariation : ∀ z ∈ Metric.closedBall (node j) ρ, ∀ w : EuclideanSpace ℝ (Fin d),
      lineCurvature (finiteFourierSquaredMUSIC frequency A₀ n) z w -
        4 * Ω ^ 2 * ε * ‖w‖ ^ 2 ≤
      lineCurvature (finiteFourierSquaredMUSIC frequency Aσ n) z w)
    (hradius : 8 * Ω ^ 3 * ρ ≤ c ^ 2)
    (hnoise : 4 * Ω ^ 2 * ε < c ^ 2 / 2) :
    StrictConvexOn ℝ (Metric.closedBall (node j) ρ)
      (finiteFourierSquaredMUSIC frequency Aσ n) := by
  have hQ0 : ContDiff ℝ 2 (finiteFourierSquaredMUSIC frequency A₀ n) :=
    rankNoiseSpaceCorrelation_sq_contDiff_two_euclidean frequency A₀ n
  have hQσ : ContinuousOn (finiteFourierSquaredMUSIC frequency Aσ n)
      (Metric.closedBall (node j) ρ) :=
    (rankNoiseSpaceCorrelation_sq_contDiff_two_euclidean frequency Aσ n).continuous.continuousOn
  have hunit (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
      2 * c ^ 2 ≤ lineCurvature
        (finiteFourierSquaredMUSIC frequency A₀ n) (node j) u := by
    exact finiteFourierMUSIC_source_curvature_on_unit_line
      frequency A₀ node K hn Δ c hΔ hc hsep j hK u hu hzero hgrowth
  have hsource (w : EuclideanSpace ℝ (Fin d)) :
      2 * c ^ 2 * ‖w‖ ^ 2 ≤ lineCurvature
        (finiteFourierSquaredMUSIC frequency A₀ n) (node j) w :=
    lineCurvature_lower_of_unitDirections _ _ c hQ0 hunit w
  exact strictConvexOn_closedBall_of_curvature_bounds
    (finiteFourierSquaredMUSIC frequency A₀ n)
    (finiteFourierSquaredMUSIC frequency Aσ n)
    (node j) ρ c Ω ε hQσ hsource hradiusVariation
    hprojectorVariation hradius hnoise

end
end NumDetect
end LeanNumDetect
