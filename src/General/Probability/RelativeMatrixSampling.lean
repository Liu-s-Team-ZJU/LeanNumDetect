import General.Probability.MatrixChernoffBounds
import Mathlib.Analysis.Matrix.Order

/-! Relative concentration obtained by whitening a positive definite population
mean.  All congruence, normalization, and change-of-coordinate steps are proved. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section

theorem quadratic_congruence {d : ℕ}
    (A P : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    quadratic (Pᴴ * A * P) x = quadratic A (P.toEuclideanLin x) := by
  unfold quadratic
  rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.adjoint_inner_right]

@[simp] theorem quadratic_identity {d : ℕ} (x : EuclideanSpace ℂ (Fin d)) :
    quadratic (1 : Matrix (Fin d) (Fin d) ℂ) x = ‖x‖ ^ 2 := by
  simp [quadratic, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

theorem mean_congruence {N d : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) (P : Matrix (Fin d) (Fin d) ℂ) :
    mean (fun k => Pᴴ * X k * P) = Pᴴ * mean X * P := by
  simp only [mean, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]

theorem sampleMean_congruence {N d m : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) (P : Matrix (Fin d) (Fin d) ℂ)
    (Ω : Sample N m) :
    sampleMean (fun k => Pᴴ * X k * P) Ω = Pᴴ * sampleMean X Ω * P := by
  simp only [sampleMean, sampleSum, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul]

/-- Every positive definite complex matrix admits an invertible whitening
congruence. No lower eigenvalue or condition number enters the statement. -/
theorem exists_whitening_matrix {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ)
    (hG : G.PosDef) :
    ∃ P : Matrix (Fin d) (Fin d) ℂ, IsUnit P ∧ Pᴴ * G * P = 1 := by
  let Q := CFC.sqrt G
  have hQ : IsUnit Q := (CFC.isUnit_sqrt_iff G hG.posSemidef.nonneg).mpr hG.isUnit
  letI := hQ.invertible
  have hQstar : Qᴴ = Q := (CFC.sqrt_nonneg G).posSemidef.isHermitian.eq
  have hQQ : Q * Q = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  refine ⟨Q⁻¹, Matrix.isUnit_nonsing_inv_iff.mpr hQ, ?_⟩
  rw [Matrix.conjTranspose_nonsing_inv, hQstar, ← hQQ]
  simp only [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul,
    Matrix.mul_inv_of_invertible]

/-- The two-tail without-replacement concentration estimate, relative to the
actual positive definite population mean. The radius is a leverage bound in
the metric of the mean, and need not contain its least eigenvalue. -/
theorem sampleMean_relative_bounds_probability
    {N d m : ℕ} (hN : 0 < N) (hd : 0 < d) (hm : 1 ≤ m) (hmN : m ≤ N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) {R ρ : ℝ}
    (hR : 0 < R) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hX : ∀ k, (X k).PosSemidef) (hG : (mean X).PosDef)
    (hbound : ∀ k (x : EuclideanSpace ℂ (Fin d)),
      quadratic (X k) x ≤ R * quadratic (mean X) x) :
    1 - ((d : ℝ) * Real.exp (-((m : ℝ) * ρ ^ 2) / (2 * R)) +
      (d : ℝ) * Real.exp (-((m : ℝ) * ρ ^ 2) / (3 * R))) ≤
    probability (fun Ω : Sample N m => ∀ x : EuclideanSpace ℂ (Fin d),
      (1 - ρ) * quadratic (mean X) x ≤ quadratic (sampleMean X Ω) x ∧
      quadratic (sampleMean X Ω) x ≤ (1 + ρ) * quadratic (mean X) x) := by
  obtain ⟨P, hP, hwhite⟩ := exists_whitening_matrix (mean X) hG
  letI := hP.invertible
  let W := fun k => Pᴴ * X k * P
  have hmean : mean W = 1 := by rw [mean_congruence, hwhite]
  have hmetric (x : EuclideanSpace ℂ (Fin d)) :
      quadratic (mean X) (P.toEuclideanLin x) = ‖x‖ ^ 2 := by
    rw [← quadratic_congruence, hwhite, quadratic_identity]
  have hprob := sampleMean_bounds_probability hN hd hm hmN W hR
    (by norm_num : (0 : ℝ) < 1) hρ0 hρ1
    (fun k => (hX k).conjTranspose_mul_mul_same P)
    (fun k x => by
      rw [quadratic_congruence]
      simpa only [hmetric] using hbound k (P.toEuclideanLin x))
    (a := 1) (b := 1) (fun x => by simp [hmean])
  simp only [mul_one] at hprob
  apply hprob.trans
  apply probability_mono
  intro Ω hΩ x
  let y := P⁻¹.toEuclideanLin x
  have hxy : P.toEuclideanLin y = x := by
    change (P.toEuclideanLin ∘ₗ P⁻¹.toEuclideanLin) x = x
    rw [← Matrix.toLpLin_mul_same, Matrix.mul_inv_of_invertible]
    simp
  have hy := hΩ y
  rw [sampleMean_congruence, quadratic_congruence, ← hmetric y, hxy] at hy
  simpa only [mul_one] using hy

end

end LeanNumDetect.FiniteMatrixSampling
