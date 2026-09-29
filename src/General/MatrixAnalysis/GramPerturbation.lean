import General.MatrixAnalysis.SpectralInterval

/-! Entrywise perturbations of Hermitian Gram matrices control every action
energy and hence the complete extremal singular-value interval. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect

noncomputable section

/-- A Hermitian matrix with zero diagonal and off-diagonal entries bounded by
`ε` has its quadratic form bounded by `(card n - 1) ε` times squared norm. -/
theorem hermitian_re_inner_abs_le_of_zero_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) {ε : ℝ}
    (hdiag : ∀ j, H j j = 0)
    (hoff : ∀ j k, j ≠ k → ‖H j k‖ ≤ ε)
    (z : EuclideanSpace ℂ n) :
    |RCLike.re ⟪z, H.toEuclideanLin z⟫_ℂ| ≤
      ((Fintype.card n : ℝ) - 1) * ε * ‖z‖ ^ 2 := by
  classical
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have heig (j : Fin (Module.finrank ℂ (EuclideanSpace ℂ n))) :
      |hT.eigenvalues rfl j| ≤ ((Fintype.card n : ℝ) - 1) * ε := by
    let v := hT.eigenvectorBasis rfl j
    have hv := hT.hasEigenvector_eigenvectorBasis rfl j
    have he : Module.End.HasEigenvalue (Matrix.toLin' H)
        ((hT.eigenvalues rfl j : ℝ) : ℂ) :=
      Module.End.hasEigenvalue_of_hasEigenvector (x := ofLp v)
        ⟨Module.End.mem_eigenspace_iff.mpr (congrArg ofLp hv.apply_eq_smul),
          by simpa [v] using hv.2⟩
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball he
    rw [mem_closedBall_iff_norm, hdiag, sub_zero, Complex.norm_real, Real.norm_eq_abs] at hk
    apply hk.trans
    calc
      ∑ j ∈ Finset.univ.erase k, ‖H k j‖ ≤ ∑ _j ∈ Finset.univ.erase k, ε := by
        apply Finset.sum_le_sum
        intro j hj
        exact hoff k j (Ne.symm (Finset.mem_erase.mp hj).1)
      _ = ((Fintype.card n : ℝ) - 1) * ε := by
        simp only [Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ]
        rw [Nat.cast_sub (by exact Fintype.card_pos_iff.mpr ⟨k⟩), Nat.cast_one]
  have hlo := rayleigh_lower_of_support H.toEuclideanLin hT z
    (c := -(((Fintype.card n : ℝ) - 1) * ε))
    (fun j _ => (abs_le.mp (heig j)).1)
  have hhi := rayleigh_upper_of_support H.toEuclideanLin hT z
    (c := ((Fintype.card n : ℝ) - 1) * ε)
    (fun j _ => (abs_le.mp (heig j)).2)
  exact abs_le.mpr ⟨by simpa only [neg_mul] using hlo, hhi⟩

/-- A matrix action energy equals the real quadratic form of its Gram matrix. -/
theorem matrix_norm_sq_eq_re_inner_gram
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (z : EuclideanSpace ℂ n) :
    ‖A.toEuclideanLin z‖ ^ 2 = RCLike.re ⟪z, (Aᴴ * A).toEuclideanLin z⟫_ℂ := by
  classical
  rw [Matrix.toLpLin_mul 2 2 2, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  exact (@RCLike.re_ofReal_pow ℂ _ ‖A.toEuclideanLin z‖ 2).symm

/-- Matching Gram diagonals and a uniform off-diagonal difference bound control
the difference between two action energies. The row types may differ. -/
theorem matrix_norm_sq_sub_norm_sq_le_of_gram_entry_bounds
    {m k n : Type*} [Fintype m] [Fintype k] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix k n ℂ) {ε : ℝ}
    (hdiag : ∀ j, (Aᴴ * A) j j = (Bᴴ * B) j j)
    (hoff : ∀ j l, j ≠ l → ‖(Aᴴ * A) j l - (Bᴴ * B) j l‖ ≤ ε)
    (z : EuclideanSpace ℂ n) :
    |‖A.toEuclideanLin z‖ ^ 2 - ‖B.toEuclideanLin z‖ ^ 2| ≤
      ((Fintype.card n : ℝ) - 1) * ε * ‖z‖ ^ 2 := by
  have h := hermitian_re_inner_abs_le_of_zero_diagonal (Aᴴ * A - Bᴴ * B)
    ((Matrix.isHermitian_conjTranspose_mul_self A).sub
      (Matrix.isHermitian_conjTranspose_mul_self B))
    (by intro j; simp only [Matrix.sub_apply, hdiag, sub_self]) hoff z
  simpa only [map_sub, LinearMap.sub_apply, inner_sub_right,
    ← matrix_norm_sq_eq_re_inner_gram] using h

/-- Uniform full-matrix energy bounds survive an entrywise Gram perturbation. -/
theorem matrix_norm_sq_bounds_of_gram_perturbation
    {m k n : Type*} [Fintype m] [Fintype k] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix k n ℂ) {ε a b : ℝ}
    (hdiag : ∀ j, (Aᴴ * A) j j = (Bᴴ * B) j j)
    (hoff : ∀ j l, j ≠ l → ‖(Aᴴ * A) j l - (Bᴴ * B) j l‖ ≤ ε)
    (hfull : ∀ z : EuclideanSpace ℂ n,
      a * ‖z‖ ^ 2 ≤ ‖B.toEuclideanLin z‖ ^ 2 ∧
        ‖B.toEuclideanLin z‖ ^ 2 ≤ b * ‖z‖ ^ 2)
    (z : EuclideanSpace ℂ n) :
    (a - ((Fintype.card n : ℝ) - 1) * ε) * ‖z‖ ^ 2 ≤ ‖A.toEuclideanLin z‖ ^ 2 ∧
      ‖A.toEuclideanLin z‖ ^ 2 ≤ (b + ((Fintype.card n : ℝ) - 1) * ε) * ‖z‖ ^ 2 := by
  have h := abs_le.mp (matrix_norm_sq_sub_norm_sq_le_of_gram_entry_bounds A B hdiag hoff z)
  have hf := hfull z
  constructor <;> nlinarith only [h.1, h.2, hf.1, hf.2]

/-- The extremal singular-value interval obtained by perturbing a full Gram
matrix. Only nonnegativity of the proposed lower endpoint is required. -/
theorem matrixSingularValue_bounds_of_gram_perturbation
    {m k n : Type*} [Fintype m] [Fintype k] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (B : Matrix k n ℂ) (hn : 0 < Fintype.card n) {ε a b : ℝ}
    (hdiag : ∀ j, (Aᴴ * A) j j = (Bᴴ * B) j j)
    (hoff : ∀ j l, j ≠ l → ‖(Aᴴ * A) j l - (Bᴴ * B) j l‖ ≤ ε)
    (hfull : ∀ z : EuclideanSpace ℂ n,
      a * ‖z‖ ^ 2 ≤ ‖B.toEuclideanLin z‖ ^ 2 ∧
        ‖B.toEuclideanLin z‖ ^ 2 ≤ b * ‖z‖ ^ 2)
    (hlow : 0 ≤ a - ((Fintype.card n : ℝ) - 1) * ε) :
    Real.sqrt (a - ((Fintype.card n : ℝ) - 1) * ε) ≤
        matrixSingularValue A (Fintype.card n - 1) ∧
      matrixSingularValue A (Fintype.card n - 1) ≤ matrixSingularValue A 0 ∧
      matrixSingularValue A 0 ≤ Real.sqrt (b + ((Fintype.card n : ℝ) - 1) * ε) := by
  have hbound := matrix_norm_sq_bounds_of_gram_perturbation A B hdiag hoff hfull
  have hhi := matrixSingularValue_sq_bounds_of_norm_sq_bounds A hbound (i := 0) hn
  exact (matrixSingularValue_interval_iff_norm_sq_bounds A hn hlow
    ((sq_nonneg _).trans hhi.2)).mpr hbound

end

end LeanNumDetect
