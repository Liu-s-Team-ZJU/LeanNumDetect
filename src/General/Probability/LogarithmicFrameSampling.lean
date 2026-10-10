import General.MatrixAnalysis.SmoothFrameStationarity
import General.Probability.SmoothWeightExistence

/-! Logarithmic entropy and stationary smooth weights yield an unconditional
lower sampling estimate for finite isotropic frames. The direct path checks
rank-one rows after normalization. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.FiniteMatrixSampling

open FrameMatrixBounds
noncomputable section
attribute [local instance] Classical.propDecidable

def logarithmicFrameFloor (n : ℕ) (θ : ℝ) : ℝ :=
  Real.exp (-(5*(n : ℝ)+6*(n : ℝ)*Real.log (((12/5 : ℝ)*n)/θ^2)))

theorem logarithmicFrameFloor_pos (n : ℕ) (θ : ℝ) : 0 < logarithmicFrameFloor n θ :=
  Real.exp_pos _

/-- The normalized auxiliary row is rank one; its only nonzero eigenvalue
is bounded by the smooth-weight energy cap. -/
theorem smooth_normalized_row_bound {N n : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin n)) {R : ℝ} (hR : 0 < R)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * A⁻¹ * P = 1)
    (k : Fin N) (x : EuclideanSpace ℂ (Fin n)) :
    quadratic (Pᴴ * weightedPopulation (framePopulation f)
      (fun j => smoothWeight R (quadratic A (f j))) k * P) x ≤ R * ‖x‖ ^ 2 := by
  let v := Pᴴ.toEuclideanLin (f k)
  have hnorm : ‖v‖ ^ 2 = quadratic A (f k) := by
    have hh := inverse_eq_whitening_gram hA.inv hP hwhite
    letI := hA.isUnit.invertible
    rw [Matrix.inv_inv_of_invertible] at hh
    rw [hh, quadratic_whitening_gram]
  have hquad : quadratic (Pᴴ * weightedPopulation (framePopulation f)
      (fun j => smoothWeight R (quadratic A (f j))) k * P) x =
      smoothWeight R (quadratic A (f k)) * ‖⟪v, x⟫_ℂ‖ ^ 2 := by
    rw [quadratic_congruence, weightedPopulation, quadratic_smul_matrix,
      quadratic_framePopulation]
    congr 1
    dsimp [v]
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_left]
  rw [hquad]
  have hw := smoothWeight_pos_le_one hR (quadratic_nonneg hA.posSemidef (f k))
  have hcap := smoothWeight_mul_le hR (quadratic_nonneg hA.posSemidef (f k))
  have hh := norm_inner_le_norm (𝕜 := ℂ) v x
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖v‖ * ‖x‖)).mpr hh
  calc
    _ ≤ smoothWeight R (quadratic A (f k)) * (‖v‖ ^ 2 * ‖x‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hw.1.le
      simpa only [mul_pow] using hs
    _ = (smoothWeight R (quadratic A (f k)) * quadratic A (f k)) * ‖x‖ ^ 2 := by
      rw [hnorm]
      ring
    _ ≤ R * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hcap (sq_nonneg _)

/-- A logarithmic entropy estimate supplies unchanged uniform sampling through
stationary smooth weights and the directly normalized rank-one population. -/
theorem sampleMean_logarithmic_frame_lower_bound_probability {N n m : ℕ}
    (hN : 0 < N) (hn : 0 < n) (hm : 1 ≤ m) (hmN : m ≤ N)
    (f : Fin N → EuclideanSpace ℂ (Fin n)) (hfull : mean (framePopulation f) = 1)
    {θ ρ ε : ℝ} (hθ : 0 < θ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (hentropy : ∀ (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef),
      (6 / 5 : ℝ) * (∑ j,
        Real.log (1 + θ ^ 2 * hH.isHermitian.eigenvalues j / ((12 / 5 : ℝ) * n))) ≤
        (N : ℝ)⁻¹ *
          ∑ i, smoothEntropy ((12 / 5 : ℝ) * n) (quadratic H (f i)))
    (hsample : 3*(n : ℝ)/ρ^2*Real.log ((n : ℝ)/ε) ≤ (m : ℝ)) :
    1-ε ≤ probability (fun Ω : Sample N m => ∀ x : EuclideanSpace ℂ (Fin n),
      ((1-ρ)/2)*logarithmicFrameFloor n θ*‖x‖^2 ≤ quadratic (sampleMean (framePopulation f) Ω) x) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let R : ℝ := (12 / 5 : ℝ) * n
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨A, hA, hmin⟩ := exists_smoothFramePotential_minimizer_of_entropy
    hN hn f hfull hθ hentropy
  let w : Fin N → ℝ := fun k => smoothWeight R (quadratic A (f k))
  let X := weightedPopulation (framePopulation f) w
  have hw (k : Fin N) : 0 < w k ∧ w k ≤ 1 :=
    smoothWeight_pos_le_one hR (quadratic_nonneg hA.posSemidef (f k))
  have hstationary : A⁻¹ = mean X :=
    smoothFramePotential_minimizer_stationary f hR A hA hmin
  have hupper (x : EuclideanSpace ℂ (Fin n)) : quadratic A⁻¹ x ≤ ‖x‖ ^ 2 := by
    rw [hstationary]
    have hh := mean_weighted_le (framePopulation f) w (framePopulation_posSemidef f)
      (fun k => (hw k).2) x
    simpa only [hfull, quadratic_identity] using hh
  have hpotential : smoothFramePotential f R A ≤ (n : ℝ) :=
    (hmin 1 Matrix.PosDef.one).trans (smoothFramePotential_one_le f hR hfull)
  have hlower (x : EuclideanSpace ℂ (Fin n)) :
      logarithmicFrameFloor n θ * ‖x‖ ^ 2 ≤ quadratic A⁻¹ x := by
    exact smoothFramePotential_inverse_quadratic_lower_of_entropy hn f A hA hθ
      (by simpa using hentropy A hA) hpotential hupper x
  obtain ⟨P, hP, hwhite⟩ := exists_whitening_matrix A⁻¹ hA.inv
  letI := hP.invertible
  let Z := fun k => Pᴴ * X k * P
  have hmean : mean Z = 1 := by rw [mean_congruence, ← hstationary, hwhite]
  have hprob := sampleMean_half_lower_bound_probability hN hn hm hmN Z
    (R := (5/2 : ℝ)*n) (by positivity) (by norm_num : (0 : ℝ) < 1) hρ0 hρ1
    (fun k => (weightedPopulation_posSemidef (framePopulation f) w
      (framePopulation_posSemidef f) (fun j => (hw j).1.le) k).conjTranspose_mul_mul_same P)
    (fun k x => (smooth_normalized_row_bound f hR A hA P hP hwhite k x).trans
      (mul_le_mul_of_nonneg_right
        (show R ≤ (5/2 : ℝ)*n by dsimp [R]; nlinarith) (sq_nonneg _)))
    (a := 1) (fun x => by simp [hmean])
  have heq : -(5*(m : ℝ)*1*ρ^2)/(6*((5/2 : ℝ)*n)) =
      -((m : ℝ)*ρ^2)/(3*n) := by field_simp; ring
  rw [heq] at hprob
  have hq : 0 < ρ^2 := pow_pos hρ0 _
  have hs : 3*(n : ℝ)*Real.log ((n : ℝ)/ε) ≤ (m : ℝ)*ρ^2 := by
    apply (div_le_iff₀ hq).mp
    calc
      _ = 3*(n : ℝ)/ρ^2*Real.log ((n : ℝ)/ε) := by ring
      _ ≤ (m : ℝ) := hsample
  have hl : Real.log ((n : ℝ)/ε) ≤ ((m : ℝ)*ρ^2)/(3*n) := by
    apply (le_div_iff₀ (by positivity : 0 < 3*(n : ℝ))).mpr
    nlinarith
  have he : Real.exp (-Real.log ((n : ℝ)/ε)) = ε/(n : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (div_pos hn' hε)]
    exact inv_div _ _
  have htail : (n : ℝ)*Real.exp (-((m : ℝ)*ρ^2)/(3*n)) ≤ ε := by
    have hh : Real.exp (-((m : ℝ)*ρ^2)/(3*n)) ≤ ε/(n : ℝ) := by
      rw [← he]
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hl
    have hh' := mul_le_mul_of_nonneg_left hh hn'.le
    have he' : (n : ℝ)*(ε/(n : ℝ)) = ε := by field_simp
    rwa [he'] at hh'
  apply ((sub_le_sub_left htail 1).trans hprob).trans
  apply probability_mono
  intro Ω hΩ x
  let y := P⁻¹.toEuclideanLin x
  have hxy : P.toEuclideanLin y = x := by
    change (P.toEuclideanLin ∘ₗ P⁻¹.toEuclideanLin) x = x
    rw [← Matrix.toLpLin_mul_same, Matrix.mul_inv_of_invertible]
    simp
  have hmetric : ‖y‖ ^ 2 = quadratic A⁻¹ x := by
    have hh := congrArg (fun H => quadratic H y) hwhite
    rw [quadratic_congruence, hxy, quadratic_identity] at hh
    exact hh.symm
  have hh := hΩ y
  rw [sampleMean_congruence, quadratic_congruence, hxy, hmetric] at hh
  have hhalf : 1-(1+ρ)/2 = (1-ρ)/2 := by ring
  rw [hhalf] at hh
  have hlow := mul_le_mul_of_nonneg_left (hlower x)
    (show 0 ≤ (1-ρ)/2 by linarith)
  have hweighted : ((1-ρ)/2)*quadratic A⁻¹ x ≤ quadratic (sampleMean X Ω) x := by
    simpa only [mul_one] using hh
  calc
    _ = ((1-ρ)/2)*(logarithmicFrameFloor n θ*‖x‖^2) := by ring
    _ ≤ quadratic (sampleMean (framePopulation f) Ω) x :=
      hlow.trans (hweighted.trans (sampleMean_weighted_le (framePopulation f) w
        (framePopulation_posSemidef f) (fun k => (hw k).2) Ω x))

end
end LeanNumDetect.FiniteMatrixSampling
