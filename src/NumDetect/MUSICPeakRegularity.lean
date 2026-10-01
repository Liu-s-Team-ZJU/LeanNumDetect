import NumDetect.SegmentedMUSICGrowth

/-! Smoothness of finite Fourier steering maps and squared MUSIC correlations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WithLp
open scoped ContDiff
namespace LeanNumDetect
namespace NumDetect
noncomputable section

/-- A finite Fourier steering map is twice continuously differentiable. -/
theorem steeringVector_contDiff_two
    {d : ℕ} {ι : Type*} [Fintype ι] (frequency : ι → Point d) :
    ContDiff ℝ 2 (steeringVector frequency) := by
  rw [contDiff_pi]
  intro i
  simp only [steeringVector, dot]
  have hphase : ContDiff ℝ 2 (fun y : Point d =>
      ∑ k, frequency i k * y k) := by fun_prop
  have hcast : ContDiff ℝ 2 (fun y : Point d =>
      (↑(∑ k, frequency i k * y k) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp hphase
  exact ContDiff.cexp (n := 2)
    ((contDiff_const : ContDiff ℝ 2 (fun _ : Point d => Complex.I)).mul hcast)

/-- The squared norm of a projected steering map is twice continuously differentiable. -/
theorem squaredProjectedSteering_contDiff_two
    {d : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d)
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    ContDiff ℝ 2 (fun y : Point d =>
      ‖S.starProjection (toLp 2 (steeringVector frequency y))‖ ^ 2) := by
  have hsteer := steeringVector_contDiff_two frequency
  have hsteerLp : ContDiff ℝ 2
      (fun y : Point d => toLp 2 (steeringVector frequency y)) :=
    PiLp.contDiff_toLp.comp hsteer
  exact ((S.starProjection.restrictScalars ℝ).contDiff.comp hsteerLp).norm_sq ℂ

/-- The unit-normalized finite Fourier steering map is twice continuously differentiable. -/
theorem normalizedSteering_contDiff_two
    {d : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d) :
    ContDiff ℝ 2 (normalizedSteering frequency) := by
  have hsteer := steeringVector_contDiff_two frequency
  have hscaled : ContDiff ℝ 2 (fun y : Point d =>
      ((Real.sqrt (Fintype.card ι : ℝ) : ℂ)⁻¹) • steeringVector frequency y) := by
    fun_prop
  convert hscaled using 1
  funext y
  simp only [normalizedSteering, steeringVector_norm_eq_sqrt_card]

/-- The squared fixed-rank MUSIC residual is twice continuously differentiable. -/
theorem rankNoiseSpaceCorrelation_sq_contDiff_two
    {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (frequency : ι → Point d) (A : Matrix ι κ ℂ) (n : ℕ) :
    ContDiff ℝ 2 (fun y : Point d =>
      rankNoiseSpaceCorrelation frequency A n y ^ 2) := by
  let S := trailingLeftSingularSubspace A n
  have hnorm : ContDiff ℝ 2 (normalizedSteering frequency) :=
    normalizedSteering_contDiff_two frequency
  have hnormLp : ContDiff ℝ 2
      (fun y : Point d => toLp 2 (normalizedSteering frequency y)) :=
    PiLp.contDiff_toLp.comp hnorm
  change ContDiff ℝ 2 (fun y : Point d =>
    ‖S.starProjection (toLp 2 (normalizedSteering frequency y))‖ ^ 2)
  exact ((S.starProjection.restrictScalars ℝ).contDiff.comp hnormLp).norm_sq ℂ

/-- Euclidean-coordinate version of squared MUSIC residual smoothness. -/
theorem rankNoiseSpaceCorrelation_sq_contDiff_two_euclidean
    {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (frequency : ι → Point d) (A : Matrix ι κ ℂ) (n : ℕ) :
    ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin d) =>
      rankNoiseSpaceCorrelation frequency A n (ofLp y) ^ 2) := by
  exact (rankNoiseSpaceCorrelation_sq_contDiff_two frequency A n).comp
    PiLp.contDiff_ofLp

end
end NumDetect
end LeanNumDetect
