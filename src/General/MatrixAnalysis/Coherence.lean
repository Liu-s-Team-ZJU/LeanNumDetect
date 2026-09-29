import General.MatrixAnalysis.SingularValueBounds
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-! Deterministic singular-value and energy bounds from unit column norms and
an entrywise bound on the off-diagonal Gram matrix. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect

noncomputable section

/-- Gershgorin bounds the squared singular values of a matrix with unit columns. -/
theorem matrixSingularValue_sq_sub_one_le_of_coherence
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {u : ℝ}
    (hdiag : ∀ j, (Aᴴ * A) j j = 1)
    (hoff : ∀ j k, j ≠ k → ‖(Aᴴ * A) j k‖ ≤ u)
    {i : ℕ} (hi : i < Fintype.card n) :
    |matrixSingularValue A i ^ 2 - 1| ≤ ((Fintype.card n : ℝ) - 1) * u := by
  classical
  have hi' : i < Module.finrank ℂ (EuclideanSpace ℂ n) := by simpa using hi
  obtain ⟨v, hv⟩ :=
    (A.toEuclideanLin.hasEigenvalue_adjoint_comp_self_sq_singularValues hi').exists_hasEigenvector
  have hvec : (Aᴴ * A) *ᵥ ofLp v =
      ((matrixSingularValue A i ^ 2 : ℝ) : ℂ) • ofLp v := by
    have h := congrArg ofLp hv.apply_eq_smul
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h
    change Aᴴ *ᵥ (A *ᵥ ofLp v) =
      ((matrixSingularValue A i : ℝ) : ℂ) ^ 2 • ofLp v at h
    simpa only [Matrix.mulVec_mulVec, Complex.ofReal_pow] using h
  have heig : Module.End.HasEigenvalue (Matrix.toLin' (Aᴴ * A))
      ((matrixSingularValue A i ^ 2 : ℝ) : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector (x := ofLp v)
      ⟨Module.End.mem_eigenspace_iff.mpr hvec, by simpa using hv.2⟩
  obtain ⟨j, hj⟩ := eigenvalue_mem_ball heig
  rw [mem_closedBall_iff_norm, hdiag] at hj
  have hnorm : ‖((matrixSingularValue A i ^ 2 : ℝ) : ℂ) - 1‖ =
      |matrixSingularValue A i ^ 2 - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at hj
  apply hj.trans
  calc
    ∑ k ∈ Finset.univ.erase j, ‖(Aᴴ * A) j k‖
        ≤ ∑ _k ∈ Finset.univ.erase j, u := by
          apply Finset.sum_le_sum
          intro k hk
          exact hoff j k (Ne.symm (Finset.mem_erase.mp hk).1)
    _ = ((Fintype.card n : ℝ) - 1) * u := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ j),
        Finset.card_univ]
      rw [Nat.cast_sub (by exact Fintype.card_pos_iff.mpr ⟨j⟩), Nat.cast_one]

/-- A coherence bound at sparsity `r` controls every squared singular value. -/
theorem matrixSingularValue_sq_bounds_of_coherence
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {r : ℕ} {ρ : ℝ}
    (hr : 2 ≤ r) (hnr : Fintype.card n ≤ r) (hρ : 0 ≤ ρ)
    (hdiag : ∀ j, (Aᴴ * A) j j = 1)
    (hoff : ∀ j k, j ≠ k → ‖(Aᴴ * A) j k‖ ≤ ρ / (r - 1 : ℝ))
    {i : ℕ} (hi : i < Fintype.card n) :
    1 - ρ ≤ matrixSingularValue A i ^ 2 ∧
      matrixSingularValue A i ^ 2 ≤ 1 + ρ := by
  have hr' : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hc : (Fintype.card n : ℝ) ≤ r := by exact_mod_cast hnr
  have hu : 0 ≤ ρ / (r - 1 : ℝ) := div_nonneg hρ (by linarith)
  have h := matrixSingularValue_sq_sub_one_le_of_coherence A hdiag hoff hi
  have hmul : ((Fintype.card n : ℝ) - 1) * (ρ / (r - 1 : ℝ)) ≤ ρ := by
    calc
      _ ≤ ((r : ℝ) - 1) * (ρ / (r - 1 : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) hu
      _ = ρ := by field_simp [ne_of_gt (show 0 < (r : ℝ) - 1 by linarith)]
  have habs := abs_le.mp (h.trans hmul)
  constructor <;> linarith [habs.1, habs.2]

/-- The extremal singular-value interval supplied by coherence, for any finite
nonempty column index type. -/
theorem matrixSingularValue_bounds_of_coherence
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {r : ℕ} {ρ : ℝ}
    (hn : 0 < Fintype.card n) (hr : 2 ≤ r) (hnr : Fintype.card n ≤ r)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hdiag : ∀ j, (Aᴴ * A) j j = 1)
    (hoff : ∀ j k, j ≠ k → ‖(Aᴴ * A) j k‖ ≤ ρ / (r - 1 : ℝ)) :
    √(1 - ρ) ≤ matrixSingularValue A (Fintype.card n - 1) ∧
      matrixSingularValue A (Fintype.card n - 1) ≤ matrixSingularValue A 0 ∧
      matrixSingularValue A 0 ≤ √(1 + ρ) := by
  have hlo := matrixSingularValue_sq_bounds_of_coherence A hr hnr hρ0 hdiag hoff
    (i := Fintype.card n - 1) (Nat.sub_lt hn Nat.zero_lt_one)
  have hhi := matrixSingularValue_sq_bounds_of_coherence A hr hnr hρ0 hdiag hoff
    (i := 0) hn
  refine ⟨?_, A.toEuclideanLin.singularValues_antitone (Nat.zero_le _), ?_⟩
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (A.toEuclideanLin.singularValues_nonneg _)).1
    simpa only [Real.sq_sqrt (by linarith : 0 ≤ 1 - ρ), matrixSingularValue] using hlo.1
  · apply (sq_le_sq₀ (A.toEuclideanLin.singularValues_nonneg _) (Real.sqrt_nonneg _)).1
    simpa only [Real.sq_sqrt (by linarith : 0 ≤ 1 + ρ), matrixSingularValue] using hhi.2

/-- Bounds on all squared singular values are bounds on every action energy. -/
theorem matrix_norm_sq_bounds_of_singularValue_sq_bounds
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {a b : ℝ}
    (hbound : ∀ i < Fintype.card n,
      a ≤ matrixSingularValue A i ^ 2 ∧ matrixSingularValue A i ^ 2 ≤ b)
    (z : EuclideanSpace ℂ n) :
    a * ‖z‖ ^ 2 ≤ ‖A.toEuclideanLin z‖ ^ 2 ∧
      ‖A.toEuclideanLin z‖ ^ 2 ≤ b * ‖z‖ ^ 2 := by
  let T := A.toEuclideanLin
  let H := T.adjoint ∘ₗ T
  let hH := T.isSymmetric_adjoint_comp_self
  have he : ‖T z‖ ^ 2 = RCLike.re ⟪z, H z⟫_ℂ := by
    rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    exact (@RCLike.re_ofReal_pow ℂ _ ‖T z‖ 2).symm
  have hb (j : Fin (Module.finrank ℂ (EuclideanSpace ℂ n))) :
      a ≤ hH.eigenvalues rfl j ∧ hH.eigenvalues rfl j ≤ b := by
    have h := hbound j.val (by simpa using j.isLt)
    have hs := T.sq_singularValues_of_lt rfl j.isLt
    simpa only [matrixSingularValue, T, hs] using h
  change a * ‖z‖ ^ 2 ≤ ‖T z‖ ^ 2 ∧ ‖T z‖ ^ 2 ≤ b * ‖z‖ ^ 2
  rw [he]
  exact ⟨rayleigh_lower_of_support H hH z (fun j _ => (hb j).1),
    rayleigh_upper_of_support H hH z (fun j _ => (hb j).2)⟩

/-- Coherence gives the usual restricted-isometry energy inequalities. -/
theorem matrix_norm_sq_bounds_of_coherence
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {r : ℕ} {ρ : ℝ}
    (hr : 2 ≤ r) (hnr : Fintype.card n ≤ r) (hρ : 0 ≤ ρ)
    (hdiag : ∀ j, (Aᴴ * A) j j = 1)
    (hoff : ∀ j k, j ≠ k → ‖(Aᴴ * A) j k‖ ≤ ρ / (r - 1 : ℝ))
    (z : EuclideanSpace ℂ n) :
    (1 - ρ) * ‖z‖ ^ 2 ≤ ‖A.toEuclideanLin z‖ ^ 2 ∧
      ‖A.toEuclideanLin z‖ ^ 2 ≤ (1 + ρ) * ‖z‖ ^ 2 :=
  matrix_norm_sq_bounds_of_singularValue_sq_bounds A
    (fun _ hi => matrixSingularValue_sq_bounds_of_coherence A hr hnr hρ hdiag hoff hi) z

end

end LeanNumDetect
