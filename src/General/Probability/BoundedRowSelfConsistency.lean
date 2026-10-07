import General.Probability.CausalShellParameters

/-! Closing the scalar expectation inequality after weighted
symmetrization. The constants are universal and do not depend on the
cardinalities of the row distribution or coefficient class. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect.BoundedRieszConcentration

theorem sqrt_le_self_add_one {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ x + 1 := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨by linarith, by nlinarith [sq_nonneg x]⟩

theorem boundedRow_expectation_selfConsistency {e S δ : ℝ}
    (he : 0 ≤ e) (hS : 0 ≤ S) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : e ≤ 6 * δ + δ / 5 * Real.sqrt ((16 / 9 : ℝ) * (S + e) + δ)) :
    e ≤ 16 * δ * (1 + S) := by
  have hs := sqrt_le_self_add_one
    (show 0 ≤ (16 / 9 : ℝ) * (S + e) + δ by positivity)
  have h1 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ δ / 5)
  have heδ : δ * e ≤ e := mul_le_of_le_one_left he hδ1
  have hδδ : δ * δ ≤ δ := mul_le_of_le_one_left hδ.le hδ1
  have hδS : 0 ≤ δ * S := mul_nonneg hδ.le hS
  nlinarith

theorem shell_budget_le_distortion {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {p δ : ℝ} (hδ : 0 < δ) (hpδ : 4 * δ ≤ p)
    (hsample : 1000000000000 * p * δ⁻¹ ^ 2 *
      Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2 ≤ (m : ℝ)) :
    (shellLevelCount p δ : ℝ) * p *
      (16384 * Real.log (2 * (N : ℝ)) + 40960 * Real.log 2 +
        81920 * (shellWordBaseLength p δ : ℝ) * Real.log (4 * (N : ℝ) + 1)) ≤
      δ ^ 2 * (m : ℝ) / 100 := by
  have hδne := hδ.ne'
  have hs := mul_le_mul_of_nonneg_left hsample (sq_nonneg δ)
  have heq : δ ^ 2 * (1000000000000 * p * δ⁻¹ ^ 2 *
      Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2) =
      100 * (10000000000 * p * Real.log (Real.exp 1 * (N : ℝ)) *
        Real.log (p / δ) ^ 2) := by field_simp; ring
  rw [heq] at hs
  exact (shell_total_budget_le hN hδ hpδ).trans (by linarith)

theorem sqrt_shell_budget_le {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    {p δ : ℝ} (hδ : 0 < δ) (hpδ : 4 * δ ≤ p)
    (hsample : 1000000000000 * p * δ⁻¹ ^ 2 *
      Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2 ≤ (m : ℝ)) :
    Real.sqrt ((shellLevelCount p δ : ℝ) * p *
      (16384 * Real.log (2 * (N : ℝ)) + 40960 * Real.log 2 +
        81920 * (shellWordBaseLength p δ : ℝ) * Real.log (4 * (N : ℝ) + 1))) ≤
      δ / 10 * Real.sqrt (m : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have h := shell_budget_le_distortion hN hm hδ hpδ hsample
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    nlinarith

/-- The source sampling premise controls the explicit envelope for the
entire entropy budget as well as the actual summed shell budget. -/
theorem concentration_budget_le_distortion {N m : ℕ} {p δ : ℝ} (hδ : 0 < δ)
    (hsample : 1000000000000 * p * δ⁻¹ ^ 2 *
      Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2 ≤ (m : ℝ)) :
    10000000000 * p * Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2 ≤
      δ ^ 2 * (m : ℝ) / 100 := by
  have hs := mul_le_mul_of_nonneg_left hsample (sq_nonneg δ)
  have heq : δ ^ 2 * (1000000000000 * p * δ⁻¹ ^ 2 *
      Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2) =
      100 * (10000000000 * p * Real.log (Real.exp 1 * (N : ℝ)) *
        Real.log (p / δ) ^ 2) := by field_simp; ring
  rw [heq] at hs
  linarith

theorem sqrt_concentration_budget_le {N m : ℕ} {p δ : ℝ} (hδ : 0 < δ)
    (hsample : 1000000000000 * p * δ⁻¹ ^ 2 *
      Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2 ≤ (m : ℝ)) :
    Real.sqrt (10000000000 * p * Real.log (Real.exp 1 * (N : ℝ)) *
      Real.log (p / δ) ^ 2) ≤ δ / 10 * Real.sqrt (m : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have h := concentration_budget_le_distortion hδ hsample
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    nlinarith

end LeanNumDetect.BoundedRieszConcentration
