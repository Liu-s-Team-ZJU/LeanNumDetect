import General.MatrixAnalysis.SingularValueBounds

/-! Multiplicative action bounds imply the same bounds for every singular
value, including maps with different finite-dimensional codomains. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

/-- A relative action estimate transfers to every ordered singular value. -/
theorem singularValues_relative_bounds (A : E →ₗ[ℂ] F) (B : E →ₗ[ℂ] G)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hlower : ∀ x, a * ‖A x‖ ≤ ‖B x‖)
    (hupper : ∀ x, ‖B x‖ ≤ b * ‖A x‖) (i : ℕ) :
    a * A.singularValues i ≤ B.singularValues i ∧
      B.singularValues i ≤ b * A.singularValues i := by
  by_cases hi : i < Module.finrank ℂ E
  · constructor
    · obtain ⟨S, hS, hA⟩ := singularValues_lower_subspace_exists A hi
      apply le_singularValues_of_subspace B hi S hS
      intro x hx
      calc
        a * A.singularValues i * ‖x‖ = a * (A.singularValues i * ‖x‖) := by ring
        _ ≤ a * ‖A x‖ := mul_le_mul_of_nonneg_left (hA x hx) ha
        _ ≤ _ := hlower x
    · obtain ⟨S, hS, hB⟩ := singularValues_lower_subspace_exists B hi
      obtain ⟨x, hx, hnorm, hA⟩ := singularValues_upper_vector_exists A hi S hS
      calc
        B.singularValues i = B.singularValues i * ‖x‖ := by rw [hnorm, mul_one]
        _ ≤ ‖B x‖ := hB x hx
        _ ≤ b * ‖A x‖ := hupper x
        _ ≤ _ := mul_le_mul_of_nonneg_left hA hb
  · rw [A.singularValues_of_finrank_le (Nat.le_of_not_gt hi),
      B.singularValues_of_finrank_le (Nat.le_of_not_gt hi)]
    simp

end LeanNumDetect
