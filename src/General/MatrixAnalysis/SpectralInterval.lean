import General.MatrixAnalysis.Coherence

/-! Equivalence of singular-value intervals and uniform quadratic energy bounds.
Both directions apply to matrices with arbitrary finite row and column types. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect

noncomputable section

/-- Every singular value at a valid column index is attained on a unit vector. -/
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

/-- Uniform bounds on matrix action energy bound every squared singular value. -/
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

/-- For a nonempty column set, a singular-value interval is equivalent to
the corresponding uniform interval for squared Euclidean action norms. -/
theorem matrixSingularValue_interval_iff_norm_sq_bounds
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hn : 0 < Fintype.card n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a ≤ matrixSingularValue A (Fintype.card n - 1) ∧
      matrixSingularValue A (Fintype.card n - 1) ≤ matrixSingularValue A 0 ∧
      matrixSingularValue A 0 ≤ Real.sqrt b) ↔
    (∀ z : EuclideanSpace ℂ n,
      a * ‖z‖ ^ 2 ≤ ‖A.toEuclideanLin z‖ ^ 2 ∧
      ‖A.toEuclideanLin z‖ ^ 2 ≤ b * ‖z‖ ^ 2) := by
  constructor
  · intro h z
    apply matrix_norm_sq_bounds_of_singularValue_sq_bounds A (fun i hi => ?_) z
    have hlo : a ≤ matrixSingularValue A (Fintype.card n - 1) ^ 2 := by
      simpa only [Real.sq_sqrt ha, matrixSingularValue] using
        (sq_le_sq₀ (Real.sqrt_nonneg a)
          (A.toEuclideanLin.singularValues_nonneg _)).2 h.1
    have hhi : matrixSingularValue A 0 ^ 2 ≤ b := by
      simpa only [Real.sq_sqrt hb, matrixSingularValue] using
        (sq_le_sq₀ (A.toEuclideanLin.singularValues_nonneg _)
          (Real.sqrt_nonneg b)).2 h.2.2
    constructor
    · exact hlo.trans ((sq_le_sq₀ (A.toEuclideanLin.singularValues_nonneg _)
        (A.toEuclideanLin.singularValues_nonneg _)).2
          (A.toEuclideanLin.singularValues_antitone (by omega : i ≤ Fintype.card n - 1)))
    · exact ((sq_le_sq₀ (A.toEuclideanLin.singularValues_nonneg _)
        (A.toEuclideanLin.singularValues_nonneg _)).2
          (A.toEuclideanLin.singularValues_antitone (Nat.zero_le i))).trans hhi
  · intro h
    have hlo := matrixSingularValue_sq_bounds_of_norm_sq_bounds A h
      (i := Fintype.card n - 1) (by omega)
    have hhi := matrixSingularValue_sq_bounds_of_norm_sq_bounds A h (i := 0) hn
    refine ⟨?_, A.toEuclideanLin.singularValues_antitone (Nat.zero_le _), ?_⟩
    · apply (sq_le_sq₀ (Real.sqrt_nonneg a)
        (A.toEuclideanLin.singularValues_nonneg _)).1
      simpa only [Real.sq_sqrt ha, matrixSingularValue] using hlo.1
    · apply (sq_le_sq₀ (A.toEuclideanLin.singularValues_nonneg _)
        (Real.sqrt_nonneg b)).1
      simpa only [Real.sq_sqrt hb, matrixSingularValue] using hhi.2

/-- The same equivalence expressed entirely using finite coordinate sums. -/
theorem matrixSingularValue_interval_iff_energy_bounds
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hn : 0 < Fintype.card n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a ≤ matrixSingularValue A (Fintype.card n - 1) ∧
      matrixSingularValue A (Fintype.card n - 1) ≤ matrixSingularValue A 0 ∧
      matrixSingularValue A 0 ≤ Real.sqrt b) ↔
    (∀ z : n → ℂ,
      a * (∑ j, ‖z j‖ ^ 2) ≤ ∑ i, ‖∑ j, A i j * z j‖ ^ 2 ∧
      (∑ i, ‖∑ j, A i j * z j‖ ^ 2) ≤ b * (∑ j, ‖z j‖ ^ 2)) := by
  rw [matrixSingularValue_interval_iff_norm_sq_bounds A hn ha hb]
  have he (z : EuclideanSpace ℂ n) :
      ‖A.toEuclideanLin z‖ ^ 2 = ∑ i, ‖∑ j, A i j * z j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  constructor
  · intro h z
    simpa only [he, EuclideanSpace.norm_sq_eq] using h (toLp 2 z)
  · intro h z
    simpa only [he, EuclideanSpace.norm_sq_eq] using h (ofLp z)

end

end LeanNumDetect
