import RandSamp.RandomModel
import General.Probability.FiniteMatrixSampling

/-! Fully proved conversion between the Fourier population, its average Gram
matrix, and the squared action of the sampled Vandermonde matrix. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

theorem quadratic_fourierRowGram {s : ℕ} (Y : Fin s → ℝ) (k : ℕ)
    (z : EuclideanSpace ℂ (Fin s)) :
    FiniteMatrixSampling.quadratic (fourierRowGram Y k) z = fourierRowEnergy Y k (ofLp z) := by
  convert fourierRowGram_quadratic Y k (ofLp z) using 1
  rw [FiniteMatrixSampling.quadratic, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

/-- The population from which the Gram summands are sampled. -/
def fourierPopulation {N s : ℕ} (Y : Fin s → ℝ) :
    Fin N → Matrix (Fin s) (Fin s) ℂ := fun k => fourierRowGram Y k.val

theorem fourierPopulation_bound {N s : ℕ} (Y : Fin s → ℝ) (k : Fin N)
    (z : EuclideanSpace ℂ (Fin s)) :
    0 ≤ FiniteMatrixSampling.quadratic (fourierPopulation Y k) z ∧
      FiniteMatrixSampling.quadratic (fourierPopulation Y k) z ≤ (s : ℝ) * ‖z‖ ^ 2 := by
  rw [fourierPopulation, quadratic_fourierRowGram, EuclideanSpace.norm_sq_eq]
  exact ⟨fourierRowEnergy_nonneg Y k.val (ofLp z), fourierRowEnergy_le Y k.val (ofLp z)⟩

theorem quadratic_fourier_mean {N s : ℕ} (Y : Fin s → ℝ)
    (z : EuclideanSpace ℂ (Fin s)) :
    FiniteMatrixSampling.quadratic (mean (fourierPopulation (N := N) Y)) z =
      (N : ℝ)⁻¹ * ∑ k : Fin N, fourierRowEnergy Y k.val (ofLp z) := by
  rw [FiniteMatrixSampling.quadratic, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change (star (ofLp z) ⬝ᵥ (((N : ℂ)⁻¹ • ∑ k, fourierPopulation Y k) *ᵥ ofLp z)).re = _
  simp only [Matrix.smul_mulVec, Matrix.sum_mulVec, dotProduct_smul, dotProduct_sum,
    smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.re_ofReal_mul, Complex.re_sum, fourierPopulation, fourierRowGram_quadratic]

theorem quadratic_fourier_sampleMean {N s m : ℕ} (Y : Fin s → ℝ)
    (Ω : Sample N m) (z : EuclideanSpace ℂ (Fin s)) :
    FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z =
      ‖(sampledVandermonde m Y Ω.val).toEuclideanLin z‖ ^ 2 := by
  rw [sampledVandermonde_energy]
  rw [FiniteMatrixSampling.quadratic, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change (star (ofLp z) ⬝ᵥ (((m : ℂ)⁻¹ • ∑ k ∈ Ω.val, fourierPopulation Y k) *ᵥ ofLp z)).re = _
  simp only [Matrix.smul_mulVec, Matrix.sum_mulVec, dotProduct_smul, dotProduct_sum,
    smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.re_ofReal_mul, Complex.re_sum, fourierPopulation, fourierRowGram_quadratic]

end

end LeanNumDetect.RandSamp
