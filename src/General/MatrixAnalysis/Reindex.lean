import General.MatrixAnalysis.SingularValueBounds

/-! Preservation of singular values under isometric changes of coordinates,
including arbitrary bijective row and column relabellings. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect

noncomputable section

/-- Domain and codomain relabellings preserving action norms preserve all
singular values. The codomains need not have the same dimension. -/
theorem singularValues_eq_of_isometry_norm_eq
    {E E' F F' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [FiniteDimensional ℂ F']
    (A : E →ₗ[ℂ] F) (B : E' →ₗ[ℂ] F') (e : E ≃ₗᵢ[ℂ] E')
    (hnorm : ∀ x, ‖A x‖ = ‖B (e x)‖) : A.singularValues = B.singularValues := by
  have hdim := e.toLinearEquiv.finrank_eq
  suffices hle : ∀ (C : E →ₗ[ℂ] F) (D : E' →ₗ[ℂ] F')
      (f : E ≃ₗᵢ[ℂ] E'), (∀ x, ‖C x‖ = ‖D (f x)‖) →
      ∀ i, C.singularValues i ≤ D.singularValues i by
    ext i
    apply le_antisymm (hle A B e hnorm i)
    by_cases hi : i < Module.finrank ℂ E'
    · obtain ⟨S, hS, hB⟩ := singularValues_lower_subspace_exists B hi
      apply le_singularValues_of_subspace A (by simpa only [hdim] using hi)
        (S.map e.symm.toLinearEquiv.toLinearMap)
      · simpa only [e.symm.toLinearEquiv.finrank_map_eq] using hS
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
        simpa only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
          e.symm.norm_map, hnorm, e.apply_symm_apply] using hB y hy
    · rw [B.singularValues_of_finrank_le (Nat.le_of_not_gt hi),
        A.singularValues_of_finrank_le (by simpa only [hdim] using Nat.le_of_not_gt hi)]
  intro C D f h i
  by_cases hi : i < Module.finrank ℂ E
  · obtain ⟨S, hS, hC⟩ := singularValues_lower_subspace_exists C hi
    apply le_singularValues_of_subspace D (by simpa only [← hdim] using hi)
      (S.map f.toLinearEquiv.toLinearMap)
    · simpa only [f.toLinearEquiv.finrank_map_eq] using hS
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      simpa only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
        f.norm_map, h] using hC y hy
  · rw [C.singularValues_of_finrank_le (Nat.le_of_not_gt hi),
      D.singularValues_of_finrank_le (by simpa only [← hdim] using Nat.le_of_not_gt hi)]

/-- Bijective relabelling of both row and column indices preserves singular
values, including zero values after the column dimension. -/
theorem matrixSingularValue_submatrix_equiv
    {m m' n n' : Type*} [Fintype m] [Fintype m'] [Fintype n] [Fintype n']
    [DecidableEq n] [DecidableEq n']
    (A : Matrix m n ℂ) (er : m' ≃ m) (ec : n' ≃ n) (i : ℕ) :
    matrixSingularValue (A.submatrix er ec) i = matrixSingularValue A i := by
  apply congrArg (fun values : ℕ →₀ ℝ => values i)
  apply singularValues_eq_of_isometry_norm_eq _ _
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ ec)
  intro z
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ x : m', ‖∑ y : n', A (er x) (ec y) * z y‖ ^ 2) =
    ∑ x : m, ‖∑ y : n, A x y * z (ec.symm y)‖ ^ 2
  apply Fintype.sum_equiv er
  intro x
  congr 2
  exact Fintype.sum_equiv ec _ _ (fun y => by simp)

end

end LeanNumDetect
