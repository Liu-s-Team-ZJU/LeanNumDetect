import General.Probability.FiniteEmpiricalSupremumConcentration
import General.Probability.RelativeDeviationTailBounds

/-! Relative population-energy concentration from a bound for the expected
empirical supremum. The chaining estimate for that expectation is deliberately
kept as a separate hypothesis. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteEntropy

open EmpiricalProcessReplacementVariance

/-- An expected deviation at scale `a δ (1+S)` gives the exact envelope tail
`exp(-δ²m/p)` at an absolute multiple of the same relative-error scale. -/
theorem finite_energy_supremum_relative_tail {J α : Type*}
    [Fintype J] [Nonempty J] [Fintype α] {m : ℕ} (hm : 0 < m)
    (h : J → α → ℝ) (μ : J → ℝ) (q : α → ℝ)
    {p S a δ : ℝ} (hp : 0 < p) (hS : 0 ≤ S) (ha : 0 ≤ a)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hq : ∀ y, 0 ≤ q y) (hqs : ∑ y, q y = 1)
    (h_nonneg : ∀ j y, 0 ≤ h j y) (h_bound : ∀ j y, h j y ≤ p)
    (h_mean : ∀ j, μ j ≤ S) (h_population : ∀ j, weightedMean q (h j) ≤ S)
    (h_expectation : weightedMean (productWeight q)
      (fun x : Fin m → α => absoluteMaximum h μ x / (m : ℝ)) ≤ a * δ * (1 + S)) :
    weightedProbability (productWeight q) (fun x : Fin m → α =>
      (5 * a + 8) * δ * (1 + S) < absoluteMaximum h μ x / (m : ℝ)) ≤
      Real.exp (-(δ^2 * (m : ℝ) / p)) := by
  let D := fun x : Fin m → α => absoluteMaximum h μ x / (m : ℝ)
  let E := weightedMean (productWeight q) D
  let u := (4 * a + 8) * δ * (1 + S)
  have hu : 0 < u := by dsimp [u]; positivity
  have hmr : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun x _ =>
    mul_nonneg (productWeight_nonneg q hq x)
      (div_nonneg (absoluteMaximum_nonneg h μ x) hmr)
  have hE : E ≤ a * δ * (1 + S) := h_expectation
  have hthreshold : E + u ≤ (5 * a + 8) * δ * (1 + S) :=
    RelativeDeviationTailBounds.expected_plus_increment_le_relative_threshold hE
  have hmono := weightedProbability_mono (productWeight q) (productWeight_nonneg q hq)
    (P := fun x => (5 * a + 8) * δ * (1 + S) < D x)
    (Q := fun x => E + u ≤ D x) (fun x hx => by linarith [hthreshold])
  have htail := finite_energy_supremum_normalized_tail hm h μ q hp hS hq hqs
    h_nonneg h_bound h_mean h_population hu
  have hexp := RelativeDeviationTailBounds.relative_deviation_tail_exponent_le
    hE0 ha hδ hδ1 hS hp hmr hE
  change weightedProbability (productWeight q) (fun x => (5 * a + 8) * δ * (1 + S) < D x) ≤ _
  exact (hmono.trans htail).trans hexp

end LeanNumDetect.FiniteEntropy
