import General.Fourier.ExponentialCompanion
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Coefficient mass bounds for an annihilating polynomial. These estimates
remain uniform when roots coincide. -/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.UnitRootRecurrence
open ExponentialCompanion
noncomputable section

/-- The total coefficient mass of the annihilating polynomial, including
its monic leading coefficient. -/
theorem rootPolynomial_coefficient_mass_le {s : ℕ} (frequency : Fin s → ℂ)
    {r : ℝ} (_hr : 0 ≤ r) (hfrequency : ‖frequency‖ ≤ r) :
    ∑ k ∈ Finset.range (s + 1), ‖(rootPolynomial frequency).coeff k‖ ≤ (1 + r) ^ s := by
  have hcoeff (k : ℕ) (hk : k ≤ s) :
      ‖(rootPolynomial frequency).coeff k‖ ≤
        ∑ T ∈ (Finset.univ : Finset (Fin s)).powersetCard (s - k),
          ∏ _i ∈ T, r := by
    have heq : rootPolynomial frequency =
        ∏ i : Fin s, (Polynomial.X + Polynomial.C (-frequency i)) := by
      simp only [rootPolynomial, sub_eq_add_neg, map_neg Polynomial.C]
    rw [heq, Finset.prod_X_add_C_coeff Finset.univ (fun i => -frequency i) (by simpa)]
    simp only [Finset.card_univ, Fintype.card_fin]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro T hT
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro i hi
    simpa only [norm_neg] using (norm_le_pi_norm frequency i).trans hfrequency
  calc
    _ ≤ ∑ k ∈ Finset.range (s + 1),
        ∑ T ∈ (Finset.univ : Finset (Fin s)).powersetCard (s - k), ∏ _i ∈ T, r := by
      exact Finset.sum_le_sum fun k hk => hcoeff k (by simpa using Finset.mem_range.mp hk)
    _ = ∑ T ∈ (Finset.univ : Finset (Fin s)).powerset, ∏ _i ∈ T, r := by
      have hrefl := Finset.sum_range_reflect
        (fun k => ∑ T ∈ (Finset.univ : Finset (Fin s)).powersetCard k, ∏ _i ∈ T, r)
        (s + 1)
      simp only [Nat.add_sub_cancel] at hrefl
      rw [hrefl, Finset.sum_powerset]
      simp
    _ = (1 + r) ^ s := by
      rw [← Finset.prod_one_add]
      simp

theorem rootPolynomial_lower_coefficient_mass_le {s : ℕ} (frequency : Fin s → ℂ)
    {r : ℝ} (hr : 0 ≤ r) (hfrequency : ‖frequency‖ ≤ r) :
    ∑ j : Fin s, ‖(rootPolynomial frequency).coeff j.val‖ ≤ (1 + r) ^ s - 1 := by
  have h := rootPolynomial_coefficient_mass_le frequency hr hfrequency
  rw [Finset.sum_range_succ, rootPolynomial_coeff_degree, norm_one,
    ← Fin.sum_univ_eq_sum_range] at h
  linarith

end
end LeanNumDetect.UnitRootRecurrence
