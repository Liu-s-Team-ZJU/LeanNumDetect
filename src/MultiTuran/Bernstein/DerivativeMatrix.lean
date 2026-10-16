import General.MatrixAnalysis.SingularValueBounds
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The finite-dimensional matrix identity behind differentiation bounds.
The Hermitian part of a differentiation matrix is controlled by its boundary
forms. No assertion about a function-space realization is assumed here. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace LeanNumDetect.MultiTuran
noncomputable section

private theorem norm_add_conj_sq (a b : ℂ) :
    ‖a + star b‖^2 = ‖a‖^2 + ‖b‖^2 + 2*(a*b).re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add]
  simp only [Complex.normSq_eq_norm_sq, ← Complex.star_def, star_star, norm_star]

/-- The exact Frobenius identity, valid without normality of `D`. -/
theorem matrixEntryNormSq_add_adjoint {ι : Type*} [Fintype ι]
    (D : Matrix ι ι ℂ) :
    matrixEntryNormSq (D + Dᴴ) =
      2*matrixEntryNormSq D + 2*(Matrix.trace (D*D)).re := by
  unfold matrixEntryNormSq
  simp only [Matrix.add_apply, Matrix.conjTranspose_apply, norm_add_conj_sq,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  have hswap : (∑ i : ι, ∑ j : ι, ‖D j i‖^2) = ∑ i : ι, ∑ j : ι, ‖D i j‖^2 :=
    Finset.sum_comm
  rw [hswap]
  have htrace : (Matrix.trace (D*D)).re = ∑ i : ι, ∑ j : ι, (D i j*D j i).re := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [htrace]
  ring

/-- Solving the Frobenius identity for the original matrix. -/
theorem matrixEntryNormSq_eq_neg_trace_add_half {ι : Type*} [Fintype ι]
    (D : Matrix ι ι ℂ) :
    matrixEntryNormSq D = -(Matrix.trace (D*D)).re + matrixEntryNormSq (D+Dᴴ)/2 := by
  have h := matrixEntryNormSq_add_adjoint D
  linarith

private theorem norm_sub_sq_le_twice (a b : ℂ) :
    ‖a-b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h := (sq_le_sq₀ (norm_nonneg (a-b))
    (add_nonneg (norm_nonneg a) (norm_nonneg b))).mpr (norm_sub_le a b)
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

/-- The squared Frobenius norm obeys the elementary two-term triangle bound. -/
theorem matrixEntryNormSq_sub_le_twice {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A B : Matrix ι κ ℂ) :
    matrixEntryNormSq (A-B) ≤ 2*(matrixEntryNormSq A+matrixEntryNormSq B) := by
  unfold matrixEntryNormSq
  calc
    _ ≤ ∑ i : ι, ∑ j : κ, 2*(‖A i j‖^2+‖B i j‖^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact norm_sub_sq_le_twice _ _
    _ = _ := by simp only [← Finset.mul_sum, Finset.sum_add_distrib]

/-- A rank-one boundary form has squared Frobenius norm equal to the fourth
power of the evaluation-vector norm. -/
theorem matrixEntryNormSq_vecMulVec_star {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    matrixEntryNormSq (Matrix.vecMulVec u (star u)) = (∑ i, ‖u i‖^2)^2 := by
  unfold matrixEntryNormSq
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, norm_mul, norm_star, mul_pow]
  rw [← Finset.sum_mul_sum]
  ring

/-- A complete eigenvector family computes `trace(D²)` without requiring an
orthogonal eigenbasis. This applies to a basis chosen from spanning exponentials. -/
theorem trace_square_of_imaginary_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D P Q : Matrix ι ι ℂ) (frequency : ι → ℝ)
    (hPQ : P*Q = 1) (hQP : Q*P = 1)
    (hDP : D*P = P*Matrix.diagonal (fun j => Complex.I*(frequency j : ℂ))) :
    (Matrix.trace (D*D)).re = -(∑ j, frequency j^2) := by
  let T := Matrix.diagonal (fun j => Complex.I*(frequency j : ℂ))
  have hDT : D*P = P*T := hDP
  have hsq : (D*D)*P = P*(T*T) := by
    calc
      _ = D*(D*P) := Matrix.mul_assoc _ _ _
      _ = D*(P*T) := by rw [hDT]
      _ = (D*P)*T := (Matrix.mul_assoc _ _ _).symm
      _ = (P*T)*T := by rw [hDT]
      _ = _ := Matrix.mul_assoc _ _ _
  have hrepr : D*D = P*(T*T)*Q := by
    calc
      D*D = (D*D)*(P*Q) := by rw [hPQ,Matrix.mul_one]
      _ = ((D*D)*P)*Q := (Matrix.mul_assoc _ _ _).symm
      _ = _ := by rw [hsq]
  have ht : Matrix.trace (D*D) = Matrix.trace (T*T) := by
    rw [hrepr, Matrix.trace_mul_cycle, hQP, Matrix.one_mul]
  rw [ht]
  simp [T, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    Complex.mul_re, Complex.mul_im, pow_two]

/-- Boundary forms and the trace of `D²` control the full differentiation
matrix, even when it is highly nonnormal. -/
theorem derivative_matrix_entryEnergy_le {ι : Type*} [Fintype ι]
    (D : Matrix ι ι ℂ) (u v : ι → ℂ) (frequency : ι → ℝ) {K : ℝ}
    (hboundary : D+Dᴴ = Matrix.vecMulVec u (star u)-Matrix.vecMulVec v (star v))
    (hu : (∑ i, ‖u i‖^2) ≤ K^2) (hv : (∑ i, ‖v i‖^2) ≤ K^2)
    (htrace : (Matrix.trace (D*D)).re = -(∑ i, frequency i^2)) :
    matrixEntryNormSq D ≤ (∑ i, frequency i^2)+2*K^4 := by
  have hu0 : 0 ≤ ∑ i, ‖u i‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hv0 : 0 ≤ ∑ i, ‖v i‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hu2 := (sq_le_sq₀ hu0 (sq_nonneg K)).mpr hu
  have hv2 := (sq_le_sq₀ hv0 (sq_nonneg K)).mpr hv
  have hB := matrixEntryNormSq_sub_le_twice
    (Matrix.vecMulVec u (star u)) (Matrix.vecMulVec v (star v))
  rw [matrixEntryNormSq_vecMulVec_star, matrixEntryNormSq_vecMulVec_star] at hB
  have hD := matrixEntryNormSq_eq_neg_trace_add_half D
  rw [htrace,hboundary] at hD
  nlinarith

/-- The corresponding Euclidean operator-norm estimate. -/
theorem derivative_matrix_operatorNorm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℂ) (u v : ι → ℂ) (frequency : ι → ℝ) {K : ℝ}
    (hboundary : D+Dᴴ = Matrix.vecMulVec u (star u)-Matrix.vecMulVec v (star v))
    (hu : (∑ i, ‖u i‖^2) ≤ K^2) (hv : (∑ i, ‖v i‖^2) ≤ K^2)
    (htrace : (Matrix.trace (D*D)).re = -(∑ i, frequency i^2)) :
    ‖D‖ ≤ Real.sqrt ((∑ i, frequency i^2)+2*K^4) :=
  (matrix_l2OpNorm_le_sqrt_entryNormSq D).trans
    (Real.sqrt_le_sqrt (derivative_matrix_entryEnergy_le D u v frequency hboundary hu hv htrace))

end
end LeanNumDetect.MultiTuran
