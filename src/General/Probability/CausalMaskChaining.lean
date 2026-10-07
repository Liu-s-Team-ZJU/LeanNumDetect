import General.Probability.NormalizedClippedMasks
import General.Probability.FiniteEntropy

/-!
# Cauchy--Schwarz assembly of causal mask processes

The path corresponding to one coefficient vector selects one mask per level.
Its weighted shell mass and the sum of normalized squared process maxima
control the entire path. This gives a square root of the number of levels,
without replacing the path shell weights by separate levelwise worst cases.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.FiniteEntropy

/-- Cauchy--Schwarz for square roots under arbitrary finite nonnegative
weights. No normalization of the weights is needed. -/
theorem weightedMean_sqrt_mul_sqrt_le
    {α : Type*} [Fintype α] (q U V : α → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hU : ∀ a, 0 ≤ U a) (hV : ∀ a, 0 ≤ V a) :
    weightedMean q (fun a => Real.sqrt (U a) * Real.sqrt (V a)) ≤
      Real.sqrt (weightedMean q U) * Real.sqrt (weightedMean q V) := by
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ
    (fun a => mul_nonneg (hq a) (hU a)) (fun a => mul_nonneg (hq a) (hV a))
  change (∑ a, Real.sqrt (q a * U a) * Real.sqrt (q a * V a)) ≤ _ at h
  have hid (a : α) : Real.sqrt (q a * U a) * Real.sqrt (q a * V a) =
      q a * (Real.sqrt (U a) * Real.sqrt (V a)) := by
    rw [Real.sqrt_mul (hq a), Real.sqrt_mul (hq a)]
    have hs := Real.sq_sqrt (hq a)
    calc
      _ = Real.sqrt (q a) ^ 2 * (Real.sqrt (U a) * Real.sqrt (V a)) := by ring
      _ = _ := by rw [hs]
  simpa only [hid, weightedMean] using h

/-- Jensen's square-root inequality for a finite probability law. -/
theorem weightedMean_sqrt_le
    {α : Type*} [Fintype α] (q U : α → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) (hU : ∀ a, 0 ≤ U a) :
    weightedMean q (fun a => Real.sqrt (U a)) ≤ Real.sqrt (weightedMean q U) := by
  have h := weightedMean_sqrt_mul_sqrt_le q U (fun _ => 1) hq hU (fun _ => by norm_num)
  simpa only [Real.sqrt_one, mul_one, weightedMean_const q hqs 1] using h

end LeanNumDetect.FiniteEntropy

namespace LeanNumDetect.FiniteMatrixSampling

open LeanNumDetect.FiniteEntropy

/-- Jensen's square-root inequality under the uniform finite law. -/
theorem finiteAverage_sqrt_le
    {α : Type*} [Fintype α] [Nonempty α] (U : α → ℝ) (hU : ∀ a, 0 ≤ U a) :
    finiteAverage (fun a => Real.sqrt (U a)) ≤ Real.sqrt (finiteAverage U) := by
  let q := fun _ : α => (Fintype.card α : ℝ)⁻¹
  have hq : ∀ a, 0 ≤ q a := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hqs : ∑ a, q a = 1 := by simp [q, hcard]
  have h := weightedMean_sqrt_le q U hq hqs hU
  simpa only [weightedMean, q, finiteAverage, smul_eq_mul, Finset.mul_sum] using h

/-- Pathwise Cauchy--Schwarz with scale radii and a uniform path mass
budget. Each path may have its own coefficients `A t l`. -/
theorem sum_path_process_le
    {T L : Type*} [Fintype L] (A : T → L → ℝ) (q H : L → ℝ)
    (hq : ∀ l, q l ≠ 0) {W : ℝ}
    (hweight : ∀ t, ∑ l, (q l * A t l) ^ 2 ≤ W) (t : T) :
    ∑ l, A t l * H l ≤ Real.sqrt W * Real.sqrt (∑ l, (H l / q l) ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun l => q l * A t l) (fun l => H l / q l)
  change (∑ l, (q l * A t l) * (H l / q l)) ≤
    Real.sqrt (∑ l, (q l * A t l) ^ 2) * Real.sqrt (∑ l, (H l / q l) ^ 2) at h
  have heq : (∑ l, A t l * H l) = ∑ l, (q l * A t l) * (H l / q l) := by
    apply Finset.sum_congr rfl
    intro l _
    field_simp [hq l]
  rw [heq]
  exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hweight t))
    (Real.sqrt_nonneg _))

/-- A causal shell path with bounded normalized second moments has an
expected absolute supremum controlled by the square root of the total
second-moment budget. In particular, a uniform per-level budget contributes
the square root of the number of levels. -/
theorem bernoulli_path_chaining_expectation_le
    {T L : Type*} [Nonempty T] [Fintype L] {m : ℕ}
    (z : T → Fin m → ℝ) (A : T → L → ℝ) (q : L → ℝ)
    (H : L → (Fin m → Bool) → ℝ) (hq : ∀ l, q l ≠ 0)
    {ε W : ℝ} (V : L → ℝ)
    (hweight : ∀ t, ∑ l, (q l * A t l) ^ 2 ≤ W)
    (hdecomp : ∀ t σ, |∑ i, finiteBernoulliSign (σ i) * z t i| ≤
      ε + ∑ l, A t l * H l σ)
    (hsecond : ∀ l, finiteAverage (fun σ : Fin m → Bool => H l σ ^ 2) ≤ V l) :
    finiteAverage (bernoulliAbsoluteSupremum z) ≤
      ε + Real.sqrt W * Real.sqrt (∑ l, V l / q l ^ 2) := by
  have hpoint (σ : Fin m → Bool) : bernoulliAbsoluteSupremum z σ ≤
      ε + Real.sqrt W * Real.sqrt (∑ l, (H l σ / q l) ^ 2) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    exact (hdecomp t σ).trans (add_le_add le_rfl (sum_path_process_le A q
      (fun l => H l σ) hq hweight t))
  have havg : finiteAverage (fun σ : Fin m → Bool => ∑ l, (H l σ / q l) ^ 2) ≤
      ∑ l, V l / q l ^ 2 := by
    rw [finiteAverage_sum]
    apply Finset.sum_le_sum
    intro l _
    have heq : finiteAverage (fun σ : Fin m → Bool => (H l σ / q l) ^ 2) =
        finiteAverage (fun σ : Fin m → Bool => H l σ ^ 2) / q l ^ 2 := by
      have hid : (fun σ : Fin m → Bool => (H l σ / q l) ^ 2) =
          (fun σ : Fin m → Bool => (q l ^ 2)⁻¹ • H l σ ^ 2) := by
        funext σ
        rw [div_pow]
        simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
      rw [hid, finiteAverage_smul]
      simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [heq]
    exact div_le_div_of_nonneg_right (hsecond l) (sq_nonneg _)
  calc
    _ ≤ finiteAverage (fun σ : Fin m → Bool => ε + Real.sqrt W *
        Real.sqrt (∑ l, (H l σ / q l) ^ 2)) := finiteAverage_mono hpoint
    _ = ε + Real.sqrt W * finiteAverage (fun σ : Fin m → Bool =>
        Real.sqrt (∑ l, (H l σ / q l) ^ 2)) := by
      rw [finiteAverage_add, finiteAverage_const]
      change (ε + finiteAverage (fun σ : Fin m → Bool => Real.sqrt W •
        Real.sqrt (∑ l, (H l σ / q l) ^ 2))) = _
      rw [finiteAverage_smul]
      rfl
    _ ≤ ε + Real.sqrt W * Real.sqrt
        (finiteAverage (fun σ : Fin m → Bool => ∑ l, (H l σ / q l) ^ 2)) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (finiteAverage_sqrt_le _ (fun σ => Finset.sum_nonneg fun l _ => sq_nonneg _))
        (Real.sqrt_nonneg _))
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt havg) (Real.sqrt_nonneg _))

end LeanNumDetect.FiniteMatrixSampling
