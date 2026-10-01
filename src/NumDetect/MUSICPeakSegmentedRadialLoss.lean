import NumDetect.MUSICPeakFourierCurvature
import NumDetect.MUSICPeakStrictConvex
import NumDetect.MUSICPeakSegmentedFrequency
import General.Convex.RadialCurvatureLoss

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WithLp
namespace LeanNumDetect
namespace NumDetect
noncomputable section

/-- The segmented frequency cutoff bounds radial variation of exact MUSIC curvature. -/
theorem segmentedFourierMUSIC_radialCurvature_lower
    {d m r D n : ℕ} {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (A : Matrix (SegmentedIndex d m r) κ ℂ)
    (node z w : EuclideanSpace ℝ (Fin d)) (ρ : ℝ)
    (hz : z ∈ Metric.closedBall node ρ) :
    lineCurvature
        (finiteFourierSquaredMUSIC (segmentedFrequency d m r D) A n)
        node w -
      8 * (Real.sqrt d * (segmentedCutoff m r D : ℝ)) ^ 3 * ρ * ‖w‖ ^ 2 ≤
    lineCurvature
      (finiteFourierSquaredMUSIC (segmentedFrequency d m r D) A n)
      z w := by
  classical
  let ΩA : ℝ := Real.sqrt d * (segmentedCutoff m r D : ℝ)
  have hΩA : 0 ≤ ΩA := by dsimp [ΩA]; positivity
  have hρ : 0 ≤ ρ := (dist_nonneg).trans (Metric.mem_closedBall.mp hz)
  have hdist : ‖z - node‖ ≤ ρ := by
    simpa only [dist_eq_norm] using (Metric.mem_closedBall.mp hz)
  have hu (α : SegmentedIndex d m r) :
      |dot (segmentedFrequency d m r D α) (ofLp w)| ≤ ΩA * ‖w‖ := by
    simpa only [ΩA, toLp_ofLp] using
      (segmentedFrequency_phase_le α (ofLp w))
  have hv (α : SegmentedIndex d m r) :
      |dot (segmentedFrequency d m r D α) (ofLp (z - node))| ≤
        ΩA * ρ := by
    have h := segmentedFrequency_phase_le (D := D) α (ofLp (z - node))
    have h' : |dot (segmentedFrequency d m r D α) (ofLp (z - node))| ≤
        ΩA * ‖z - node‖ := by simpa only [ΩA, toLp_ofLp] using h
    exact h'.trans (mul_le_mul_of_nonneg_left hdist hΩA)
  let S := trailingLeftSingularSubspace A n
  let Q := finiteFourierSquaredMUSIC (segmentedFrequency d m r D) A n
  let H (τ : ℝ) := lineCurvature Q (node + τ • (z - node)) w
  have hH : H = fun τ : ℝ => iteratedDeriv 2 (fun t : ℝ =>
      ‖S.starProjection (toLp 2 (normalizedSteering
        (segmentedFrequency d m r D)
        ((ofLp node + τ • ofLp (z - node)) + t • ofLp w)))‖ ^ 2) 0 := by
    funext τ
    simp only [H, lineCurvature, Q, finiteFourierSquaredMUSIC,
      rankNoiseSpaceCorrelation, S, ofLp_add, ofLp_smul]
  have hbound := fourierProjected_sq_line_curvature_radial_deriv_abs_le
    (segmentedFrequency d m r D) S
    (ofLp node) (ofLp w) (ofLp (z - node))
    (ΩA * ‖w‖) (ΩA * ρ)
    (mul_nonneg hΩA (norm_nonneg _)) (mul_nonneg hΩA hρ) hu hv
  have hdiff : ∀ τ ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ H τ := by
    intro τ _
    rw [hH]
    exact (hbound τ).1
  have hderiv : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      |deriv H τ| ≤ 8 * ΩA ^ 3 * ρ * ‖w‖ ^ 2 := by
    intro τ _
    rw [hH]
    calc
      _ ≤ 8 * (ΩA * ‖w‖) ^ 2 * (ΩA * ρ) := (hbound τ).2
      _ = 8 * ΩA ^ 3 * ρ * ‖w‖ ^ 2 := by ring
  simpa only [Q, ΩA] using
    lineCurvature_lower_of_radial_deriv_bound Q node z w ΩA ρ hdiff hderiv

end
end NumDetect
end LeanNumDetect
