import General.Fourier.CubeClumpBounds

/-! The fixed cube-clump geometry and deterministic coefficient used by the
manuscript's random sampling theorem. The general frame-parameter argument
is retained in `General.Fourier.CubeClumpBounds`; the numerical source
condition is discharged here rather than exposed as a theorem hypothesis. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect.NumDetect
noncomputable section

private theorem fixedFrameParameter_admissible :
    1 / (2 * Real.log 2) < (1 : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_lt_one (by positivity : 0 < 2 * Real.log 2)).2
  nlinarith [Real.log_two_gt_d9]

theorem cubeFrameConstant_pos : 0 < 2 - Real.exp (1 / 2 : ℝ) := by
  simpa only [mul_one] using liFrameConstant_pos fixedFrameParameter_admissible

/-- The deterministic coefficient depends only on dimension, node count,
and maximal clump size. -/
def cubeClumpUniformCoefficient (d n nStar : ℕ) : ℝ :=
  (2 - Real.exp (1 / 2 : ℝ)) ^ ((nStar : ℝ) / 2) /
    (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1) *
      (Real.sqrt (3 * nStar)) ^ d * (4 * Real.pi * nStar) ^ (nStar - 1))

private theorem cubeClumpUniformCoefficient_eq_general (d n nStar : ℕ) :
    cubeClumpUniformCoefficient d n nStar = liCubeClumpUniformCoefficient d n nStar 1 := by
  simp only [cubeClumpUniformCoefficient, liCubeClumpUniformCoefficient, mul_one]

theorem cubeClumpUniformCoefficient_pos {d n nStar : ℕ}
    (hn : 0 < n) (hs : 0 < nStar) :
    0 < cubeClumpUniformCoefficient d n nStar := by
  have ha := cubeFrameConstant_pos
  unfold cubeClumpUniformCoefficient
  positivity

/-- The manuscript's angular geometry with independent bandwidth and
separation bounds and no auxiliary frame parameter. -/
def CubeClumpGeometry {d n : ℕ} (μ : AtomicMeasure d n)
    (A nStar L : ℕ) (τ η : ℝ) (hn : 2 ≤ n) : Prop :=
  Even L ∧ 8 * n ≤ L ∧ IsAngularClumpStructure μ.node A nStar τ η ∧
    8 * Real.pi * d * nStar / L ≤ τ ∧
    τ ≤ Real.pi / (2 * d) ∧
    periodicMinimumL1Separation μ.node hn ≤ 4 * Real.pi * nStar / L

private theorem cubeClumpGeometry_to_general
    {d n A nStar L : ℕ} {τ η : ℝ}
    (μ : AtomicMeasure d n) (hn : 2 ≤ n)
    (hgeom : CubeClumpGeometry μ A nStar L τ η hn) :
    LiCubeClumpGeometry μ A nStar L τ η 1 hn := by
  rcases hgeom with ⟨hEven, hL, hclumps, hseparation, hτ, hscale⟩
  exact ⟨hEven, hL, hclumps, fixedFrameParameter_admissible,
    by simpa only [mul_one] using hseparation, hτ, hscale⟩

/-- The deterministic full-cube lower estimate with the fixed manuscript
constant and no frame-parameter hypothesis. -/
theorem cubeClumpVandermonde_normalized_uniform_lower
    {d n A nStar L : ℕ} {τ η : ℝ}
    (μ : AtomicMeasure d n) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hgeom : CubeClumpGeometry μ A nStar L τ η hn) :
    cubeClumpUniformCoefficient d n nStar *
        ((L : ℝ) * periodicMinimumL1Separation μ.node hn) ^ (nStar - 1) ≤
      matrixSingularValue (RandSamp.cubeFullVandermonde L μ.node) (n - 1) := by
  rw [cubeClumpUniformCoefficient_eq_general]
  exact liCubeClumpVandermonde_normalized_uniform_lower μ hd hn
    (cubeClumpGeometry_to_general μ hn hgeom)

end
end LeanNumDetect.NumDetect
