import General.MatrixAnalysis.MatrixReduction
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-! Orthonormal changes of basis and singular values after deleting rows.
These reductions do not depend on any external formula. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped ComplexOrder

namespace LeanNumDetect

/-- Matrix singular values for the Euclidean norms, indexed from zero. -/
noncomputable def matrixSingularValue {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℂ) (i : ℕ) : ℝ :=
  A.toEuclideanLin.singularValues i

/-- A squared singular value below the column dimension has a nonzero Gram eigenvector. -/
theorem singularValue_gram_eigenvector {m : Type*} [Fintype m] {n i : ℕ}
    (A : Matrix m (Fin n) ℂ) (hi : i < n) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧
      (Aᴴ * A) *ᵥ v = ((matrixSingularValue A i ^ 2 : ℝ) : ℂ) • v := by
  classical
  have hi' : i < Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) := by simpa using hi
  obtain ⟨v, hv⟩ :=
    (A.toEuclideanLin.hasEigenvalue_adjoint_comp_self_sq_singularValues hi').exists_hasEigenvector
  refine ⟨ofLp v, by simpa using hv.2, ?_⟩
  have h := congrArg ofLp hv.apply_eq_smul
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h
  change Aᴴ *ᵥ (A *ᵥ ofLp v) =
    ((matrixSingularValue A i : ℝ) : ℂ) ^ 2 • ofLp v at h
  simpa only [Matrix.mulVec_mulVec, Complex.ofReal_pow] using h

/-- Inclusion of column spaces gives an actual matrix of coefficients. -/
theorem factor_of_range_le {m n : Type*} [Fintype n] [DecidableEq n]
    (U V : Matrix m n ℂ)
    (h : LinearMap.range U.mulVecLin ≤ LinearMap.range V.mulVecLin) :
    ∃ P : Matrix n n ℂ, U = V * P := by
  classical
  have hc (j : n) : ∃ p : n → ℂ, V *ᵥ p = Uᵀ j := by
    apply h
    exact ⟨Pi.single j 1, by simp [Matrix.col]⟩
  choose p hp using hc
  refine ⟨fun i j => p j i, ?_⟩
  ext i j
  exact (congrFun (hp j) i).symm

/-- Orthonormalizing a full rank matrix transports removed-row Gram eigenpairs
 to the corresponding Gram quotient. This is the algebraic form of
 `U = V G^{-1/2} Q`, without choosing a matrix square root. -/
theorem removed_gram_eigenpair {m k : Type*} [Fintype m] [Fintype k] {n : ℕ}
    (U V : Matrix m (Fin n) ℂ) (f : k → m)
    (hU : Uᴴ * U = 1)
    (hspan : LinearMap.range U.mulVecLin ≤ LinearMap.range V.mulVecLin)
    (hG : (Vᴴ * V).PosDef)
    {z : ℂ} {v : Fin n → ℂ} (hv : v ≠ 0)
    (heig : ((U.submatrix f id)ᴴ * U.submatrix f id) *ᵥ v = z • v) :
    ∃ w : Fin n → ℂ, w ≠ 0 ∧
      ((Vᴴ * V)⁻¹ * ((V.submatrix f id)ᴴ * V.submatrix f id)) *ᵥ w = z • w := by
  obtain ⟨P, hP⟩ := factor_of_range_le U V hspan
  let G := Vᴴ * V
  have hnorm : (Pᴴ * G) * P = 1 := by
    simpa only [hP, Matrix.conjTranspose_mul, Matrix.mul_assoc, G] using hU
  have hnorm' : P * (Pᴴ * G) = 1 := mul_eq_one_comm.mp hnorm
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hPP : P * Pᴴ = G⁻¹ := by
    calc
      P * Pᴴ = (P * (Pᴴ * G)) * G⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, G.mul_nonsing_inv hdet, Matrix.mul_one]
      _ = G⁻¹ := by rw [hnorm', Matrix.one_mul]
  have hw : P *ᵥ v ≠ 0 := by
    intro heq
    apply hv
    have h := congrArg (fun w => (Pᴴ * G) *ᵥ w) heq
    simpa only [Matrix.mulVec_mulVec, hnorm, Matrix.one_mulVec, Matrix.mulVec_zero] using h
  have hblock : U.submatrix f id = V.submatrix f id * P := by
    rw [hP]
    ext i j
    rfl
  refine ⟨P *ᵥ v, hw, ?_⟩
  have h := congrArg (fun w => P *ᵥ w) heig
  simpa only [hblock, Matrix.conjTranspose_mul, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPP, G] using h

/-- Deleting rows from an orthonormal basis converts an endpoint Gram-quotient
 upper bound into a lower bound on every retained singular value. -/
theorem rowDeletion_singularValue_gt {m k q : Type*}
    [Fintype m] [Fintype k] [Fintype q] {n i : ℕ}
    (U V : Matrix m (Fin n) ℂ) (R : Matrix q (Fin n) ℂ) (f : k → m)
    (hU : Uᴴ * U = 1)
    (hspan : LinearMap.range U.mulVecLin ≤ LinearMap.range V.mulVecLin)
    (hG : (Vᴴ * V).PosDef)
    (hsplit : Rᴴ * R + (U.submatrix f id)ᴴ * U.submatrix f id = 1)
    {C : ℝ}
    (hbound : ∀ (z : ℂ) (v : Fin n → ℂ), v ≠ 0 →
      ((Vᴴ * V)⁻¹ * ((V.submatrix f id)ᴴ * V.submatrix f id)) *ᵥ v = z • v →
      z.re < 1 - C)
    (hi : i < n) : C < matrixSingularValue R i ^ 2 := by
  obtain ⟨v, hv, heig⟩ := singularValue_gram_eigenvector R hi
  have hremoved : ((U.submatrix f id)ᴴ * U.submatrix f id) *ᵥ v =
      (1 - ((matrixSingularValue R i ^ 2 : ℝ) : ℂ)) • v := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M *ᵥ v) hsplit
    rw [Matrix.add_mulVec, Matrix.one_mulVec, heig] at h
    rw [sub_smul, one_smul]
    exact eq_sub_of_add_eq' h
  obtain ⟨w, hw, he⟩ := removed_gram_eigenpair U V f hU hspan hG hv hremoved
  have hb := hbound _ w hw he
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hb
  linarith

/-- The non-strict version of `rowDeletion_singularValue_gt`. -/
theorem rowDeletion_singularValue_ge {m k q : Type*}
    [Fintype m] [Fintype k] [Fintype q] {n i : ℕ}
    (U V : Matrix m (Fin n) ℂ) (R : Matrix q (Fin n) ℂ) (f : k → m)
    (hU : Uᴴ * U = 1)
    (hspan : LinearMap.range U.mulVecLin ≤ LinearMap.range V.mulVecLin)
    (hG : (Vᴴ * V).PosDef)
    (hsplit : Rᴴ * R + (U.submatrix f id)ᴴ * U.submatrix f id = 1)
    {C : ℝ}
    (hbound : ∀ (z : ℂ) (v : Fin n → ℂ), v ≠ 0 →
      ((Vᴴ * V)⁻¹ * ((V.submatrix f id)ᴴ * V.submatrix f id)) *ᵥ v = z • v →
      z.re ≤ 1 - C)
    (hi : i < n) : C ≤ matrixSingularValue R i ^ 2 := by
  obtain ⟨v, hv, heig⟩ := singularValue_gram_eigenvector R hi
  have hremoved : ((U.submatrix f id)ᴴ * U.submatrix f id) *ᵥ v =
      (1 - ((matrixSingularValue R i ^ 2 : ℝ) : ℂ)) • v := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M *ᵥ v) hsplit
    rw [Matrix.add_mulVec, Matrix.one_mulVec, heig] at h
    rw [sub_smul, one_smul]
    exact eq_sub_of_add_eq' h
  obtain ⟨w, hw, he⟩ := removed_gram_eigenpair U V f hU hspan hG hv hremoved
  have hb := hbound _ w hw he
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hb
  linarith

/-- One block of a matrix whose rows are indexed by block and within-block position. -/
def rowBlock {r : ℕ} {k n : Type*} (U : Matrix (Fin (r + 1) × k) n ℂ)
    (j : Fin (r + 1)) : Matrix k n ℂ := U.submatrix (fun t => (j, t)) id

/-- Delete the first block. -/
def dropFirstBlock {r : ℕ} {k n : Type*} (U : Matrix (Fin (r + 1) × k) n ℂ) :
    Matrix (Fin r × k) n ℂ := U.submatrix (fun t => (t.1.succ, t.2)) id

/-- Delete the last block. -/
def dropLastBlock {r : ℕ} {k n : Type*} (U : Matrix (Fin (r + 1) × k) n ℂ) :
    Matrix (Fin r × k) n ℂ := U.submatrix (fun t => (t.1.castSucc, t.2)) id

theorem gram_dropFirstBlock {r : ℕ} {k n : Type*} [Fintype k]
    (U : Matrix (Fin (r + 1) × k) n ℂ) :
    (dropFirstBlock U)ᴴ * dropFirstBlock U + (rowBlock U 0)ᴴ * rowBlock U 0 = Uᴴ * U := by
  ext i j
  simp only [dropFirstBlock, rowBlock, Matrix.add_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq, Fintype.sum_prod_type]
  rw [Fin.sum_univ_succ]
  exact add_comm _ _

theorem gram_dropLastBlock {r : ℕ} {k n : Type*} [Fintype k]
    (U : Matrix (Fin (r + 1) × k) n ℂ) :
    (dropLastBlock U)ᴴ * dropLastBlock U +
      (rowBlock U (Fin.last r))ᴴ * rowBlock U (Fin.last r) = Uᴴ * U := by
  ext i j
  simp only [dropLastBlock, rowBlock, Matrix.add_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq, Fintype.sum_prod_type]
  rw [Fin.sum_univ_castSucc]

end LeanNumDetect
