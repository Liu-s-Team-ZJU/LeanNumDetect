import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Finite energy assembly for almost orthogonal subspaces, on any finite row type. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect.AlmostOrthogonalEnergy
noncomputable section

/-- Squared norm expansion with ordered cross terms. -/
theorem clump_sum_norm_sq {A : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : Fin A → E) :
    ‖∑ a, v a‖ ^ 2 = ∑ a, ∑ b, (⟪v a, v b⟫_ℂ).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [sum_inner, inner_sum]
  change (∑ b, ∑ a, ⟪v a, v b⟫_ℂ).re = _
  rw [Finset.sum_comm]
  simp only [Complex.re_sum]

/-- Small pairwise correlations give both sides of the clump energy comparison. -/
theorem clump_sum_energy_bounds {A : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : Fin A → E) {ε : ℝ} (hε : 0 ≤ ε)
    (hcross : ∀ a b, a ≠ b → ‖⟪v a, v b⟫_ℂ‖ ≤ ε * ‖v a‖ * ‖v b‖) :
    (1 - ε * (A - 1 : ℝ)) * (∑ a, ‖v a‖ ^ 2) ≤ ‖∑ a, v a‖ ^ 2 ∧
    ‖∑ a, v a‖ ^ 2 ≤ (1 + ε * (A - 1 : ℝ)) * (∑ a, ‖v a‖ ^ 2) := by
  classical
  let q := fun a => ‖v a‖ ^ 2
  have hp (a b : Fin A) :
      |(⟪v a, v b⟫_ℂ).re - (if b = a then q a else 0)| ≤
        if b = a then 0 else ε / 2 * (q a + q b) := by
    by_cases hab : b = a
    · subst b
      have hdia : (⟪v a, v a⟫_ℂ).re = q a :=
        (norm_sq_eq_re_inner (𝕜 := ℂ) (v a)).symm
      simp only [ite_true, hdia, sub_self, abs_zero, le_refl]
    · rw [if_neg hab, if_neg hab, sub_zero]
      have hc := hcross a b (Ne.symm hab)
      have hr := Complex.abs_re_le_norm (⟪v a, v b⟫_ℂ)
      have hs : ‖v a‖ * ‖v b‖ ≤ (q a + q b) / 2 := by
        dsimp [q]
        nlinarith [sq_nonneg (‖v a‖ - ‖v b‖)]
      exact hr.trans (hc.trans (by nlinarith [mul_le_mul_of_nonneg_left hs hε]))
  have hsum := Finset.abs_sum_le_sum_abs (fun a : Fin A =>
    ∑ b : Fin A, ((⟪v a, v b⟫_ℂ).re - (if b = a then q a else 0))) Finset.univ
  have hinner (a : Fin A) :
      |∑ b : Fin A, ((⟪v a, v b⟫_ℂ).re - (if b = a then q a else 0))| ≤
        ∑ b : Fin A, if b = a then 0 else ε / 2 * (q a + q b) := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => hp a b)
  have hd : (∑ a : Fin A, ∑ b : Fin A,
      if b = a then 0 else ε / 2 * (q a + q b)) =
      ε * (A - 1 : ℝ) * ∑ a, q a := by
    have hrow (a : Fin A) : (∑ b : Fin A,
        if b = a then 0 else ε / 2 * (q a + q b)) =
        ε / 2 * (((A : ℝ) - 2) * q a + ∑ b, q b) := by
      have hA : 1 ≤ A := by have := a.isLt; omega
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
      simp only [ite_true, add_zero]
      have hz : (∑ b ∈ Finset.univ.erase a,
          if b = a then 0 else ε / 2 * (q a + q b)) =
          ε / 2 * (((A : ℝ) - 1) * q a + ((∑ b, q b) - q a)) := by
        rw [Finset.sum_congr rfl (fun b hb => if_neg (Finset.ne_of_mem_erase hb))]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_sub hA, Nat.cast_one,
          Finset.sum_erase_eq_sub (Finset.mem_univ a)]
      rw [hz]
      ring
    simp_rw [hrow]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have he : (∑ a : Fin A, ∑ b : Fin A,
      ((⟪v a, v b⟫_ℂ).re - (if b = a then q a else 0))) =
      ‖∑ a, v a‖ ^ 2 - ∑ a, q a := by
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [clump_sum_norm_sq]
  have habs : |‖∑ a, v a‖ ^ 2 - ∑ a, q a| ≤
      ε * (A - 1 : ℝ) * ∑ a, q a := by
    rw [← he, ← hd]
    exact hsum.trans (Finset.sum_le_sum fun a _ => hinner a)
  rcases abs_le.mp habs with ⟨hlo, hhi⟩
  dsimp [q] at hlo hhi
  constructor <;> nlinarith

/-- An absolute half-energy bound from correlations at the theorem's scale. -/
theorem clump_sum_half_energy {A n : ℕ} (hn : 0 < n) (hAn : A ≤ n)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : Fin A → E)
    (hcross : ∀ a b, a ≠ b →
      ‖⟪v a, v b⟫_ℂ‖ ≤ (1 / (2 * (n : ℝ))) * ‖v a‖ * ‖v b‖) :
    (1 / 2 : ℝ) * (∑ a, ‖v a‖ ^ 2) ≤ ‖∑ a, v a‖ ^ 2 ∧
    ‖∑ a, v a‖ ^ 2 ≤ (3 / 2 : ℝ) * (∑ a, ‖v a‖ ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := clump_sum_energy_bounds v (by positivity) hcross
  have hcoef : 1 / (2 * (n : ℝ)) * (A - 1 : ℝ) ≤ 1 / 2 := by
    have hAnR : (A : ℝ) ≤ n := by exact_mod_cast hAn
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).2
    exact (show (A : ℝ) - 1 ≤ (1 / 2) * (2 * (n : ℝ)) by linarith)
  have hq : 0 ≤ ∑ a, ‖v a‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hcoef hq]

/-- Combining local evaluation bounds and half-energy loses only a factor two. -/
theorem row_bound_of_clump_bounds {A : ℕ} {κ : Type*} [Fintype κ]
    (v : Fin A → EuclideanSpace ℂ κ) (L : Fin A → ℝ)
    (hL : ∀ a, 0 ≤ L a)
    (hlocal : ∀ a (k : κ), ‖v a k‖ ^ 2 ≤ L a * ‖v a‖ ^ 2)
    (henergy : (1 / 2 : ℝ) * (∑ a, ‖v a‖ ^ 2) ≤ ‖∑ a, v a‖ ^ 2)
    (k : κ) :
    ‖(∑ a, v a) k‖ ^ 2 ≤ 2 * (∑ a, L a) * ‖∑ a, v a‖ ^ 2 := by
  have hn (a : Fin A) : ‖v a k‖ ≤ Real.sqrt (L a) * ‖v a‖ := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
    rw [mul_pow, Real.sq_sqrt (hL a)]
    exact hlocal a k
  have he : (∑ a, v a) k = ∑ a, v a k := by simp
  rw [he]
  have ht : ‖∑ a, v a k‖ ≤ ∑ a, Real.sqrt (L a) * ‖v a‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hn a)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a => Real.sqrt (L a)) (fun a => ‖v a‖)
  simp only [Real.sq_sqrt (hL _)] at hs
  have hsq := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
    fun a _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2 ht
  have hsumL : 0 ≤ ∑ a, L a := Finset.sum_nonneg fun a _ => hL a
  exact (hsq.trans hs).trans (by
    nlinarith [mul_le_mul_of_nonneg_left henergy hsumL])

end
end LeanNumDetect.AlmostOrthogonalEnergy
