import General.Probability.FiniteProcessConcentration
import General.Probability.EmpiricalProcessReplacementVariance

/-! Variance-sensitive concentration of bounded nonnegative empirical
processes under a finite weighted independent product law. The class size
does not occur in the tail; its complexity enters only through the expected
supremum, which is kept explicit. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteEntropy

open EmpiricalProcessReplacementVariance

theorem finite_energy_supremum_replacement_variance {J α : Type*}
    [Fintype J] [Nonempty J] [Fintype α] {m : ℕ}
    (h : J → α → ℝ) (μ : J → ℝ) (q : α → ℝ)
    {p S : ℝ} (hp : 0 ≤ p) (hq : ∀ y, 0 ≤ q y) (hqs : ∑ y, q y = 1)
    (h_nonneg : ∀ j y, 0 ≤ h j y) (h_bound : ∀ j y, h j y ≤ p)
    (h_mean : ∀ j, μ j ≤ S) (h_population : ∀ j, weightedMean q (h j) ≤ S)
    (x : Fin m → α) :
    positiveReplacementVariance q (absoluteMaximum h μ : (Fin m → α) → ℝ) x ≤
      p * absoluteMaximum h μ x + p * (m : ℝ) * S := by
  have hvar := absolute_replacement_variance_bound h μ x q hp hq hqs
    h_nonneg h_bound h_mean h_population
  simpa only [positiveReplacementVariance, weightedMean, mul_add, mul_assoc] using hvar

/-- The absolute empirical-process supremum concentrates at the population
energy scale. This is a complete finite-law theorem, including entropy
tensorization, the replacement variance estimate, and the scalar Herbst
comparison. -/
theorem finite_energy_supremum_tail {J α : Type*}
    [Fintype J] [Nonempty J] [Fintype α] {m : ℕ}
    (h : J → α → ℝ) (μ : J → ℝ) (q : α → ℝ)
    {p S : ℝ} (hp : 0 < p) (hS : 0 ≤ S) (hq : ∀ y, 0 ≤ q y) (hqs : ∑ y, q y = 1)
    (h_nonneg : ∀ j y, 0 ≤ h j y) (h_bound : ∀ j y, h j y ≤ p)
    (h_mean : ∀ j, μ j ≤ S) (h_population : ∀ j, weightedMean q (h j) ≤ S)
    {u : ℝ} (hu : 0 < u) :
    weightedProbability (productWeight q) (fun x : Fin m → α =>
      weightedMean (productWeight q) (absoluteMaximum h μ : (Fin m → α) → ℝ) + u ≤ absoluteMaximum h μ x) ≤
      Real.exp (-u^2 / (4 * p *
        (weightedMean (productWeight q) (absoluteMaximum h μ : (Fin m → α) → ℝ) + (m : ℝ) * S + u))) := by
  have hEZ : 0 ≤ weightedMean (productWeight q) (absoluteMaximum h μ : (Fin m → α) → ℝ) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (productWeight_nonneg q hq x)
      (absoluteMaximum_nonneg h μ x)
  have hv : 0 ≤ p * weightedMean (productWeight q) (absoluteMaximum h μ : (Fin m → α) → ℝ) +
      p * (m : ℝ) * S := add_nonneg (mul_nonneg hp.le hEZ)
        (mul_nonneg (mul_nonneg hp.le (Nat.cast_nonneg m)) hS)
  have htail := weightedProbability_product_tail_linearVariance q hq hqs
    (absoluteMaximum h μ : (Fin m → α) → ℝ) hp
    (finite_energy_supremum_replacement_variance h μ q hp.le hq hqs
      h_nonneg h_bound h_mean h_population) hv hu
  convert htail using 1
  congr 1
  ring

theorem weightedMean_div {α : Type*} [Fintype α] (q f : α → ℝ) (c : ℝ) :
    weightedMean q (fun x => f x / c) = weightedMean q f / c := by
  simp only [weightedMean, mul_div_assoc, Finset.sum_div]

theorem weightedProbability_mono {α : Type*} [Fintype α] (q : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) {P Q : α → Prop} (hPQ : ∀ x, P x → Q x) :
    weightedProbability q P ≤ weightedProbability q Q := by
  classical
  unfold weightedProbability
  apply weightedMean_mono hq
  intro x
  by_cases hx : P x
  · simp only [if_pos hx, if_pos (hPQ x hx), le_refl]
  · simp only [if_neg hx]
    split_ifs <;> norm_num

/-- The same theorem for an empirical mean. Its exponent has the desired
linear row-envelope scale `m / p`. -/
theorem finite_energy_supremum_normalized_tail {J α : Type*}
    [Fintype J] [Nonempty J] [Fintype α] {m : ℕ} (hm : 0 < m)
    (h : J → α → ℝ) (μ : J → ℝ) (q : α → ℝ)
    {p S : ℝ} (hp : 0 < p) (hS : 0 ≤ S) (hq : ∀ y, 0 ≤ q y) (hqs : ∑ y, q y = 1)
    (h_nonneg : ∀ j y, 0 ≤ h j y) (h_bound : ∀ j y, h j y ≤ p)
    (h_mean : ∀ j, μ j ≤ S) (h_population : ∀ j, weightedMean q (h j) ≤ S)
    {u : ℝ} (hu : 0 < u) :
    weightedProbability (productWeight q) (fun x : Fin m → α =>
      weightedMean (productWeight q) (fun z : Fin m → α => absoluteMaximum h μ z / (m : ℝ)) + u ≤
        absoluteMaximum h μ x / (m : ℝ)) ≤
      Real.exp (-((m : ℝ) * u^2) / (4 * p *
        (weightedMean (productWeight q) (fun z : Fin m → α => absoluteMaximum h μ z / (m : ℝ)) + S + u))) := by
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have htail := finite_energy_supremum_tail (m := m) h μ q hp hS hq hqs
    h_nonneg h_bound h_mean h_population (mul_pos hmr hu)
  have hevent (x : Fin m → α) :
      weightedMean (productWeight q) (fun z : Fin m → α => absoluteMaximum h μ z / (m : ℝ)) + u ≤
        absoluteMaximum h μ x / (m : ℝ) ↔
      weightedMean (productWeight q) (absoluteMaximum h μ : (Fin m → α) → ℝ) + (m : ℝ) * u ≤ absoluteMaximum h μ x := by
    rw [weightedMean_div]
    rw [le_div_iff₀ hmr]
    have heq : (weightedMean (productWeight q) (absoluteMaximum h μ : (Fin m → α) → ℝ) / (m : ℝ) + u) * (m : ℝ) =
        weightedMean (productWeight q) (absoluteMaximum h μ : (Fin m → α) → ℝ) + (m : ℝ) * u := by
      field_simp [hmr.ne']
    rw [heq]
  have hprob : weightedProbability (productWeight q) (fun x : Fin m → α =>
      weightedMean (productWeight q) (fun z : Fin m → α => absoluteMaximum h μ z / (m : ℝ)) + u ≤
        absoluteMaximum h μ x / (m : ℝ)) =
      weightedProbability (productWeight q) (fun x : Fin m → α =>
        weightedMean (productWeight q) (absoluteMaximum h μ : (Fin m → α) → ℝ) + (m : ℝ) * u ≤ absoluteMaximum h μ x) := by
    classical
    unfold weightedProbability
    congr 1
    funext x
    simp only [hevent]
  rw [hprob]
  have hEZ : 0 ≤ weightedMean (productWeight q) (absoluteMaximum h μ : (Fin m → α) → ℝ) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (productWeight_nonneg q hq x)
      (absoluteMaximum_nonneg h μ x)
  have hden : 0 < weightedMean (productWeight q) (absoluteMaximum h μ : (Fin m → α) → ℝ) +
      (m : ℝ) * S + (m : ℝ) * u := by positivity
  convert htail using 1
  apply congrArg Real.exp
  rw [weightedMean_div]
  field_simp [hmr.ne', hp.ne', hden.ne']

end LeanNumDetect.FiniteEntropy
