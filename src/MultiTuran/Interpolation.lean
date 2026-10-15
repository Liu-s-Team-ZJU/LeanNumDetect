import General.MatrixAnalysis.SingularValueBounds
import General.MatrixAnalysis.SpectralInterval

/-! # Cardinal interpolation and the least singular value

The finite-dimensional argument of `lem:interp-sv` in the MultiTuran manuscript.
Rows of `F` are the Fourier coefficient vectors of the cardinal functions.
The interpolation equation is `F * A = 1`, without complex conjugation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- Uniform lower energy bounds imply a lower bound on the last column
singular value. The conclusion concerns the actual matrix singular value. -/
theorem minimumSingularValue_ge_of_energy_lower
    {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℂ) (hn : 0 < n) {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ c : Fin n → ℂ,
      b ^ 2 * (∑ j, ‖c j‖ ^ 2) ≤ ∑ k, ‖∑ j, A k j * c j‖ ^ 2) :
    b ≤ matrixSingularValue A (n - 1) := by
  obtain ⟨z, hz, he⟩ := exists_unit_vector_norm_sq_eq_singularValue_sq A
    (i := n - 1) (by simpa using Nat.sub_lt hn Nat.zero_lt_one)
  have h := hA (ofLp z)
  have henergy : (∑ k, ‖∑ j, A k j * ofLp z j‖ ^ 2) =
      ‖A.toEuclideanLin z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [← EuclideanSpace.norm_sq_eq, hz, one_pow, mul_one, henergy, he] at h
  exact (sq_le_sq₀ hb (A.toEuclideanLin.singularValues_nonneg _)).mp h

/-- The coefficient norm in `lem:interp-sv` is the square root of the sum
of the squared Euclidean norms of all cardinal coefficient vectors. -/
def interpolationCoefficientNorm
    {ι : Type*} [Fintype ι] {n : ℕ} (F : Matrix (Fin n) ι ℂ) : ℝ :=
  Real.sqrt (∑ j, ∑ k, ‖F j k‖ ^ 2)

/-- Exact reciprocal estimate of manuscript `lem:interp-sv`. -/
theorem reciprocal_minimumSingularValue_le_of_interpolation
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℂ) (F : Matrix (Fin n) ι ℂ)
    (hn : 0 < n) (hFA : F * A = 1) :
    1 / matrixSingularValue A (n - 1) ≤ interpolationCoefficientNorm F := by
  obtain ⟨z, hz, he⟩ := exists_unit_vector_norm_sq_eq_singularValue_sq A
    (i := n - 1) (by simpa using Nat.sub_lt hn Nat.zero_lt_one)
  have hnorm : ‖A.toEuclideanLin z‖ = matrixSingularValue A (n - 1) :=
    (sq_eq_sq₀ (norm_nonneg _) (A.toEuclideanLin.singularValues_nonneg _)).mp he
  have hleft : F.toEuclideanLin (A.toEuclideanLin z) = z := by
    change (F.toEuclideanLin.comp A.toEuclideanLin) z = z
    rw [← Matrix.toLpLin_mul_same, hFA]
    simp
  have hbound := F.toEuclideanLin.toContinuousLinearMap.le_opNorm (A.toEuclideanLin z)
  have hF := matrix_l2OpNorm_le_sqrt_entryNormSq F
  have hbound' : 1 ≤ interpolationCoefficientNorm F * matrixSingularValue A (n - 1) := by
    change ‖F.toEuclideanLin (A.toEuclideanLin z)‖ ≤
      ‖F.toEuclideanLin.toContinuousLinearMap‖ * ‖A.toEuclideanLin z‖ at hbound
    rw [hleft, hz, hnorm] at hbound
    have hnormF : ‖F.toEuclideanLin.toContinuousLinearMap‖ = ‖F‖ := by
      rw [Matrix.l2_opNorm_def]
      rfl
    rw [hnormF] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right hF
      (A.toEuclideanLin.singularValues_nonneg _))
  have hσ : 0 < matrixSingularValue A (n - 1) := by
    have hσ0 := A.toEuclideanLin.singularValues_nonneg (n - 1)
    have hF0 : 0 ≤ interpolationCoefficientNorm F := Real.sqrt_nonneg _
    by_contra h
    have hzero : matrixSingularValue A (n - 1) = 0 := le_antisymm (le_of_not_gt h) hσ0
    rw [hzero, mul_zero] at hbound'
    norm_num at hbound'
  exact (div_le_iff₀ hσ).mpr hbound'

end
end LeanNumDetect.MultiTuran
