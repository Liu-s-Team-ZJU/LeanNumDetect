import General.MatrixAnalysis.LogDetDirectionalDerivative
import General.Probability.SmoothFramePotential
import General.MatrixAnalysis.InverseMetric
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! First-order optimality for the smooth precision-matrix frame potential. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp Filter
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Topology

namespace LeanNumDetect.FiniteMatrixSampling

open FrameMatrixBounds
noncomputable section

/-- The directional derivative of the smooth frame potential. -/
theorem smoothFramePotential_hasDerivAt_affine {N n : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin n)) {R : ℝ} (hR : 0 < R)
    (A H : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    HasDerivAt (fun t : ℝ => smoothFramePotential f R (A + (t : ℂ) • H))
      (-(A⁻¹ * H).trace.re + (N : ℝ)⁻¹ *
        ∑ k, smoothWeight R (quadratic A (f k)) * quadratic H (f k)) 0 := by
  have hrow (k : Fin N) : HasDerivAt
      (fun t : ℝ => smoothEntropy R (quadratic (A + (t : ℂ) • H) (f k)))
      (smoothWeight R (quadratic A (f k)) * quadratic H (f k)) 0 := by
    have hq : HasDerivAt (fun t : ℝ => quadratic (A + (t : ℂ) • H) (f k))
        (quadratic H (f k)) 0 := by
      simp_rw [TraceExponential.quadratic_add, quadratic_smul_matrix]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (quadratic H (f k))).const_add
        (quadratic A (f k))
    have he := smoothEntropy_hasDerivAt hR (quadratic_nonneg hA.posSemidef (f k))
    have he' : HasDerivAt (smoothEntropy R)
        (smoothWeight R (quadratic A (f k))) (quadratic (A + ((0 : ℝ) : ℂ) • H) (f k)) := by
      simpa only [Complex.ofReal_zero, zero_smul, add_zero] using he
    simpa only [Function.comp_def] using
      (HasDerivAt.comp (h₂ := smoothEntropy R)
        (h := fun t : ℝ => quadratic (A + (t : ℂ) • H) (f k)) 0 he' hq)
  have hd := (hasDerivAt_log_realDet_affine A H hA).neg
  have hs := (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hrow k)).const_mul
    (N : ℝ)⁻¹
  convert hd.add hs using 1 <;> first | rfl | (ext t; simp [smoothFramePotential])

/-- A rank-one Hermitian perturbation stays positive definite near zero. -/
theorem eventually_posDef_rankOne_affine {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (x : EuclideanSpace ℂ (Fin n)) :
    ∀ᶠ t : ℝ in 𝓝 0,
      (A + (t : ℂ) • framePopulation (fun _ : Fin 1 => x) 0).PosDef := by
  let H := framePopulation (fun _ : Fin 1 => x) 0
  let q := quadratic A⁻¹ x
  have hq : 0 ≤ q := quadratic_nonneg hA.posSemidef.inv x
  have he : 0 < 1 / (q + 1) := by positivity
  have ht : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 / (q + 1) := by
    exact (continuous_abs.tendsto (0 : ℝ)).eventually (gt_mem_nhds (by simpa using he))
  filter_upwards [ht] with t ht
  have hH : (A + (t : ℂ) • H).IsHermitian :=
    hA.isHermitian.add ((framePopulation_posSemidef (fun _ : Fin 1 => x) 0).isHermitian.smul
      (by simp [IsSelfAdjoint]))
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hH
  intro v hv
  have hv' : (toLp 2 v : EuclideanSpace ℂ (Fin n)) ≠ 0 := by simpa using hv
  have hpos : 0 < quadratic A (toLp 2 v) := by
    simpa only [quadratic, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct_comm, ofLp_toLp, RCLike.re_eq_complex_re] using hA.re_dotProduct_pos hv
  have hrow := row_energy_le_inverse_metric A hA x (toLp 2 v)
  have hcoef : |t| * q < 1 := by
    have hh : |t| * (q + 1) < 1 := (lt_div_iff₀ (by positivity : 0 < q + 1)).mp ht
    nlinarith [abs_nonneg t]
  have henergy : 0 < quadratic (A + (t : ℂ) • H) (toLp 2 v) := by
    rw [TraceExponential.quadratic_add, quadratic_smul_matrix]
    have hnonneg : 0 ≤ ‖⟪x, toLp 2 v⟫_ℂ‖ ^ 2 := sq_nonneg _
    have hb := mul_le_mul_of_nonneg_left hrow (abs_nonneg t)
    have hl := mul_le_mul_of_nonneg_right (neg_abs_le t) hnonneg
    have hp := mul_pos (sub_pos.mpr hcoef) hpos
    rw [quadratic_framePopulation]
    dsimp [q] at hcoef
    nlinarith
  apply RCLike.pos_iff.mpr
  exact ⟨by simpa only [quadratic, Matrix.toLpLin_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, ofLp_toLp,
    RCLike.re_eq_complex_re] using henergy,
    hH.im_star_dotProduct_mulVec_self v⟩

/-- A minimizer on the full positive cone has the covariance fixed-point identity. -/
theorem smoothFramePotential_minimizer_stationary {N n : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin n)) {R : ℝ} (hR : 0 < R)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (hmin : ∀ D : Matrix (Fin n) (Fin n) ℂ, D.PosDef →
      smoothFramePotential f R A ≤ smoothFramePotential f R D) :
    A⁻¹ = mean (weightedPopulation (framePopulation f)
      (fun k => smoothWeight R (quadratic A (f k)))) := by
  let w := fun k => smoothWeight R (quadratic A (f k))
  let B := mean (weightedPopulation (framePopulation f) w)
  have hB : B.PosSemidef := mean_posSemidef _
    (weightedPopulation_posSemidef _ _ (framePopulation_posSemidef f)
      (fun k => (smoothWeight_pos_le_one hR (quadratic_nonneg hA.posSemidef (f k))).1.le))
  have hquad (x : EuclideanSpace ℂ (Fin n)) : quadratic A⁻¹ x = quadratic B x := by
    let H := framePopulation (fun _ : Fin 1 => x) 0
    have hlocal : IsLocalMin
        (fun t : ℝ => smoothFramePotential f R (A + (t : ℂ) • H)) 0 := by
      filter_upwards [eventually_posDef_rankOne_affine A hA x] with t ht
      simpa only [Complex.ofReal_zero, zero_smul, add_zero] using hmin _ ht
    have hz := hlocal.hasDerivAt_eq_zero (smoothFramePotential_hasDerivAt_affine f hR A H hA)
    have htrace : (A⁻¹ * H).trace.re = quadratic A⁻¹ x :=
      trace_mul_framePopulation (fun _ : Fin 1 => x) 0 A⁻¹
    have hsum : (N : ℝ)⁻¹ * ∑ k, w k * quadratic H (f k) = quadratic B x := by
      change _ = quadratic (mean (weightedPopulation (framePopulation f) w)) x
      rw [quadratic_mean_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [weightedPopulation, quadratic_smul_matrix]
      change w k * quadratic (framePopulation (fun _ : Fin 1 => x) 0) (f k) =
        w k * quadratic (framePopulation f k) x
      rw [quadratic_framePopulation, quadratic_framePopulation]
      rw [norm_inner_symm]
    change -(A⁻¹ * H).trace.re + (N : ℝ)⁻¹ * ∑ k, w k * quadratic H (f k) = 0 at hz
    rw [htrace, hsum] at hz
    linarith
  exact le_antisymm
    (matrix_le_of_quadratic_le hA.isHermitian.inv hB.isHermitian (fun x => (hquad x).le))
    (matrix_le_of_quadratic_le hB.isHermitian hA.isHermitian.inv (fun x => (hquad x).ge))

end
end LeanNumDetect.FiniteMatrixSampling
