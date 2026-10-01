import General.Convex.LinewiseSecondDerivative
import General.Convex.CurvatureTransfer

/-! Positive directional curvature yields strict convexity on source balls. -/

set_option autoImplicit false
open Set
namespace LeanNumDetect
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Second directional derivative of a function at a base point. -/
def lineCurvature (Q : E → ℝ) (z w : E) : ℝ :=
  iteratedDeriv 2 (fun t : ℝ => Q (z + t • w)) 0

/-- A unit-direction curvature lower bound scales quadratically to every direction. -/
theorem lineCurvature_lower_of_unitDirections
    (Q : E → ℝ) (center : E) (c : ℝ)
    (hQ : ContDiff ℝ 2 Q)
    (hunit : ∀ u : E, ‖u‖ = 1 → 2 * c ^ 2 ≤ lineCurvature Q center u)
    (w : E) :
    2 * c ^ 2 * ‖w‖ ^ 2 ≤ lineCurvature Q center w := by
  by_cases hw : w = 0
  · subst w
    simp [lineCurvature, iteratedDeriv_const]
  let r := ‖w‖
  let u := r⁻¹ • w
  have hrpos : 0 < r := norm_pos_iff.mpr hw
  have hunorm : ‖u‖ = 1 := by
    simp [u, norm_smul, r, inv_mul_cancel₀ hrpos.ne']
  have hru : r • u = w := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
  let f : ℝ → ℝ := fun s => Q (center + s • u)
  have hf : ContDiff ℝ 2 f := hQ.comp (by fun_prop)
  have hfun : (fun t : ℝ => Q (center + t • w)) =
      (fun t : ℝ => f (r * t)) := by
    funext t
    dsimp [f]
    congr 1
    rw [← hru, smul_smul, mul_comm]
  have hscale : lineCurvature Q center w =
      r ^ 2 * lineCurvature Q center u := by
    unfold lineCurvature
    rw [hfun, iteratedDeriv_comp_const_mul hf r]
    simp [f]
  rw [hscale]
  have hbase := hunit u hunorm
  have hrsq : 0 ≤ r ^ 2 := sq_nonneg r
  have hmul := mul_le_mul_of_nonneg_left hbase hrsq
  simpa [r, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- A segment's second derivative equals the corresponding directional curvature. -/
theorem segment_second_eq_lineCurvature
    (Q : E → ℝ) (x y : E) (t : ℝ) :
    (deriv^[2] (fun s : ℝ => Q ((1 - s) • x + s • y))) t =
      lineCurvature Q ((1 - t) • x + t • y) (y - x) := by
  let w : E := y - x
  let g : ℝ → ℝ := fun s => Q (x + s • w)
  have hline : (fun s : ℝ => Q ((1 - s) • x + s • y)) = g := by
    funext s
    dsimp [g, w]
    congr 1
    module
  have hshift : (fun s : ℝ => Q (((1 - t) • x + t • y) + s • w)) =
      (fun s : ℝ => g (t + s)) := by
    funext s
    dsimp [g, w]
    congr 1
    module
  rw [← iteratedDeriv_eq_iterate, hline]
  unfold lineCurvature
  rw [hshift, iteratedDeriv_comp_const_add]
  simp

/-- Positive directional curvature on a ball makes the objective strictly convex there. -/
theorem strictConvexOn_closedBall_of_lineCurvature_pos
    (Q : E → ℝ) (center : E) (ρ : ℝ)
    (hQ : ContinuousOn Q (Metric.closedBall center ρ))
    (hcurv : ∀ z ∈ Metric.closedBall center ρ, ∀ w : E,
      w ≠ 0 → 0 < lineCurvature Q z w) :
    StrictConvexOn ℝ (Metric.closedBall center ρ) Q := by
  apply strictConvexOn_of_segment_deriv2_pos
    (Metric.closedBall center ρ) Q (convex_closedBall center ρ) hQ
  intro x hx y hy hxy t ht
  have hz : (1 - t) • x + t • y ∈ Metric.closedBall center ρ :=
    (convex_closedBall center ρ) hx hy (by linarith [ht.2]) ht.1 (by ring)
  rw [segment_second_eq_lineCurvature]
  exact hcurv _ hz _ (sub_ne_zero.mpr (Ne.symm hxy))

/-- Source curvature, radial variation, and projector perturbation imply strict convexity. -/
theorem strictConvexOn_closedBall_of_curvature_bounds
    (Q Qσ : E → ℝ) (center : E) (ρ c Ω ε : ℝ)
    (hQσ : ContinuousOn Qσ (Metric.closedBall center ρ))
    (hsource : ∀ w : E,
      2 * c ^ 2 * ‖w‖ ^ 2 ≤ lineCurvature Q center w)
    (hradiusVariation : ∀ z ∈ Metric.closedBall center ρ, ∀ w : E,
      lineCurvature Q center w - 8 * Ω ^ 3 * ρ * ‖w‖ ^ 2 ≤
        lineCurvature Q z w)
    (hprojectorVariation : ∀ z ∈ Metric.closedBall center ρ, ∀ w : E,
      lineCurvature Q z w - 4 * Ω ^ 2 * ε * ‖w‖ ^ 2 ≤
        lineCurvature Qσ z w)
    (hρ : 8 * Ω ^ 3 * ρ ≤ c ^ 2)
    (hε : 4 * Ω ^ 2 * ε < c ^ 2 / 2) :
    StrictConvexOn ℝ (Metric.closedBall center ρ) Qσ := by
  apply strictConvexOn_closedBall_of_lineCurvature_pos Qσ center ρ hQσ
  intro z hz w hw
  have hnorm : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  have hrad : 8 * Ω ^ 3 * ρ * ‖w‖ ^ 2 ≤ c ^ 2 * ‖w‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hρ hnorm.le
  have hnoise : 4 * Ω ^ 2 * ε * ‖w‖ ^ 2 < c ^ 2 / 2 * ‖w‖ ^ 2 :=
    mul_lt_mul_of_pos_right hε hnorm
  have hfinal := hprojectorVariation z hz w
  have hmid := hradiusVariation z hz w
  have hbase := hsource w
  have hcnonneg : 0 ≤ c ^ 2 / 2 * ‖w‖ ^ 2 := by positivity
  dsimp [lineCurvature] at *
  linarith

end
end LeanNumDetect
