import General.MatrixAnalysis.SingularValueBounds

/-!
Conversion of quadratic energy estimates into extremal singular-value bounds.
These are the deterministic spectral steps used by the fixed separated-support
theorem (`thm:fixed-separated-singular-values`) in the RandSamp manuscript.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect
namespace RandSamp

noncomputable section

/-- A right singular direction can be chosen to have unit Euclidean norm. -/
theorem exists_unit_vector_norm_sq_eq_singularValue_sq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {i : ℕ} (hi : i < Fintype.card n) :
    ∃ z : EuclideanSpace ℂ n,
      ‖z‖ = 1 ∧ ‖A.toEuclideanLin z‖ ^ 2 = matrixSingularValue A i ^ 2 := by
  let T := A.toEuclideanLin
  let H := T.adjoint ∘ₗ T
  let hH := T.isSymmetric_adjoint_comp_self
  have hi' : i < Module.finrank ℂ (EuclideanSpace ℂ n) := by simpa using hi
  let j : Fin (Module.finrank ℂ (EuclideanSpace ℂ n)) := ⟨i, hi'⟩
  let z := hH.eigenvectorBasis rfl j
  have hz : ‖z‖ = 1 := (hH.eigenvectorBasis rfl).orthonormal.1 j
  refine ⟨z, hz, ?_⟩
  have he : H z = (hH.eigenvalues rfl j : ℂ) • z :=
    hH.apply_eigenvectorBasis rfl j
  have henergy : ‖T z‖ ^ 2 = RCLike.re ⟪z, H z⟫_ℂ := by
    rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    exact (@RCLike.re_ofReal_pow ℂ _ ‖T z‖ 2).symm
  change ‖T z‖ ^ 2 = T.singularValues i ^ 2
  rw [henergy, he, inner_smul_right, inner_self_eq_norm_sq_to_K, hz]
  simpa using (T.sq_singularValues_of_lt rfl hi').symm

/-- A uniform quadratic energy estimate bounds every squared singular value. -/
theorem matrixSingularValue_sq_bounds_of_norm_sq_bounds
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {a b : ℝ}
    (hbound : ∀ z : EuclideanSpace ℂ n,
      a * ‖z‖ ^ 2 ≤ ‖A.toEuclideanLin z‖ ^ 2 ∧
      ‖A.toEuclideanLin z‖ ^ 2 ≤ b * ‖z‖ ^ 2)
    {i : ℕ} (hi : i < Fintype.card n) :
    a ≤ matrixSingularValue A i ^ 2 ∧ matrixSingularValue A i ^ 2 ≤ b := by
  obtain ⟨z, hz, he⟩ := exists_unit_vector_norm_sq_eq_singularValue_sq A hi
  simpa only [hz, he, one_pow, mul_one] using hbound z

/-- The smallest and largest singular values lie between the square roots of
uniform quadratic energy bounds. -/
theorem matrixSingularValue_bounds_of_norm_sq_bounds
    {m : Type*} [Fintype m] {s : ℕ}
    (A : Matrix m (Fin s) ℂ) (hs : 0 < s) {a b : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ z : EuclideanSpace ℂ (Fin s),
      a * ‖z‖ ^ 2 ≤ ‖A.toEuclideanLin z‖ ^ 2 ∧
      ‖A.toEuclideanLin z‖ ^ 2 ≤ b * ‖z‖ ^ 2) :
    √a ≤ matrixSingularValue A (s - 1) ∧
      matrixSingularValue A (s - 1) ≤ matrixSingularValue A 0 ∧
      matrixSingularValue A 0 ≤ √b := by
  have hlo := matrixSingularValue_sq_bounds_of_norm_sq_bounds A hbound
    (i := s - 1) (by simpa using Nat.sub_lt hs Nat.zero_lt_one)
  have hhi := matrixSingularValue_sq_bounds_of_norm_sq_bounds A hbound
    (i := 0) (by simpa using hs)
  have hb : 0 ≤ b := (sq_nonneg (matrixSingularValue A 0)).trans hhi.2
  refine ⟨?_, A.toEuclideanLin.singularValues_antitone (Nat.zero_le _), ?_⟩
  · apply (sq_le_sq₀ (Real.sqrt_nonneg a) (A.toEuclideanLin.singularValues_nonneg _)).1
    simpa only [Real.sq_sqrt ha, matrixSingularValue] using hlo.1
  · apply (sq_le_sq₀ (A.toEuclideanLin.singularValues_nonneg _) (Real.sqrt_nonneg b)).1
    simpa only [Real.sq_sqrt hb, matrixSingularValue] using hhi.2

/-- The Euclidean squared norm of a matrix action is its row-by-row energy. -/
theorem matrix_action_norm_sq_eq_energy
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (z : EuclideanSpace ℂ n) :
    ‖A.toEuclideanLin z‖ ^ 2 = ∑ i, ‖∑ j, A i j * z j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rfl

/-- Entrywise energy estimates give the extremal singular-value bounds without
requiring callers to unfold Euclidean linear maps. -/
theorem matrixSingularValue_bounds_of_energy_bounds
    {m : Type*} [Fintype m] {s : ℕ}
    (A : Matrix m (Fin s) ℂ) (hs : 0 < s) {a b : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ z : Fin s → ℂ,
      a * (∑ j, ‖z j‖ ^ 2) ≤ ∑ i, ‖∑ j, A i j * z j‖ ^ 2 ∧
      (∑ i, ‖∑ j, A i j * z j‖ ^ 2) ≤ b * (∑ j, ‖z j‖ ^ 2)) :
    √a ≤ matrixSingularValue A (s - 1) ∧
      matrixSingularValue A (s - 1) ≤ matrixSingularValue A 0 ∧
      matrixSingularValue A 0 ≤ √b := by
  apply matrixSingularValue_bounds_of_norm_sq_bounds A hs ha
  intro z
  rw [matrix_action_norm_sq_eq_energy, EuclideanSpace.norm_sq_eq]
  exact hbound (ofLp z)

end

end RandSamp
end LeanNumDetect
