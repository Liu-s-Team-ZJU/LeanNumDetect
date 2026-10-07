import General.Probability.BoundedRowEstimates
import General.Probability.FiniteEmpiricalRelativeConcentration

/-! Finite-alphabet bounded-row concentration, with the population-energy
supremum and the empirical mean normalized exactly as in the arbitrary-law
bounded-row theorem. The expected-supremum input is separated from the fully
proved variance-sensitive tail implication. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.BoundedRieszConcentration

open FiniteEntropy EmpiricalProcessReplacementVariance

/-- Maximum population energy over a finite list of coefficient vectors. -/
noncomputable def finiteRowPopulationSup {N L J : ℕ}
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ) : ℝ :=
  sSup (Set.range fun j => weightedMean q (fun a => rowEnergy (f j) (X a)))

/-- Maximum absolute error of the normalized empirical energy over a finite list. -/
noncomputable def finiteRowDeviation {N L J m : ℕ}
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    (x : Fin m → Fin L) : ℝ :=
  sSup (Set.range fun j => |(m : ℝ)⁻¹ * (∑ i, rowEnergy (f j) (X (x i))) -
    weightedMean q (fun a => rowEnergy (f j) (X a))|)

/-- Concentration at fixed parameters for every finite row law and nonempty
finite target class. There is no restriction to uniform or rational weights. -/
def FiniteRowConcentrationAt (N m : ℕ) (s K δ B : ℝ) : Prop :=
  ∀ L J : ℕ, 0 < L → 0 < J →
    ∀ (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ),
      (∀ a k, ‖X a k‖ ≤ K) →
      (∀ j, coefficientL1Norm (f j) ≤ Real.sqrt s) →
      (∀ a, 0 ≤ q a) → (∑ a, q a = 1) →
      weightedProbability (productWeight q) (fun x : Fin m → Fin L =>
        B * δ * (1 + finiteRowPopulationSup X f q) < finiteRowDeviation X f q x) ≤
      Real.exp (-(δ^2 * (m : ℝ) / (s * K^2)))

theorem finiteRowPopulation_le_sup {N L J : ℕ}
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    (j : Fin J) :
    weightedMean q (fun a => rowEnergy (f j) (X a)) ≤ finiteRowPopulationSup X f q :=
  le_csSup (Set.finite_range _).bddAbove ⟨j, rfl⟩

theorem finiteRowPopulationSup_nonneg {N L J : ℕ} (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    (hq : ∀ a, 0 ≤ q a) : 0 ≤ finiteRowPopulationSup X f q := by
  have hzero : 0 ≤ weightedMean q (fun a => rowEnergy (f ⟨0, hJ⟩) (X a)) :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hq a) (rowEnergy_nonneg _ _)
  exact hzero.trans (finiteRowPopulation_le_sup X f q ⟨0, hJ⟩)

theorem finiteRowPopulationSup_le_radius {N L J : ℕ} (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hX : ∀ a k, ‖X a k‖ ≤ K) (hf : ∀ j, coefficientL1Norm (f j) ≤ Real.sqrt s)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) :
    finiteRowPopulationSup X f q ≤ s * K^2 := by
  letI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  have h := weightedMean_mono hq (fun a => rowEnergy_le_radius (f j) (X a)
    hs hK (hf j) (hX a))
  rw [weightedMean_const q hqs] at h
  exact h

/-- The normalized supremum agrees exactly with the unnormalized maximum
used in the replacement-variance theorem, divided by the sample count. -/
theorem finiteRowDeviation_eq_absoluteMaximum {N L J m : ℕ} (hm : 0 < m) (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    (x : Fin m → Fin L) :
    finiteRowDeviation X f q x =
      absoluteMaximum (fun j a => rowEnergy (f j) (X a))
        (fun j => weightedMean q (fun a => rowEnergy (f j) (X a))) x / (m : ℝ) := by
  letI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have hterm (j : Fin J) :
      |(m : ℝ)⁻¹ * (∑ i, rowEnergy (f j) (X (x i))) -
        weightedMean q (fun a => rowEnergy (f j) (X a))| =
      |(∑ i, rowEnergy (f j) (X (x i))) -
        (m : ℝ) * weightedMean q (fun a => rowEnergy (f j) (X a))| / (m : ℝ) := by
    have heq : (m : ℝ)⁻¹ * (∑ i, rowEnergy (f j) (X (x i))) -
        weightedMean q (fun a => rowEnergy (f j) (X a)) =
        ((∑ i, rowEnergy (f j) (X (x i))) -
          (m : ℝ) * weightedMean q (fun a => rowEnergy (f j) (X a))) / (m : ℝ) := by
      field_simp [hmr.ne']
    rw [heq, abs_div, abs_of_pos hmr]
  apply le_antisymm
  · obtain ⟨j, hj⟩ := finiteMaximum_attained (fun j : Fin J =>
      |(m : ℝ)⁻¹ * (∑ i, rowEnergy (f j) (X (x i))) -
        weightedMean q (fun a => rowEnergy (f j) (X a))|)
    change _ = finiteRowDeviation X f q x at hj
    rw [← hj, hterm]
    exact div_le_div_of_nonneg_right (le_finiteMaximum
      (fun j : Fin J => |(∑ i, rowEnergy (f j) (X (x i))) -
        (m : ℝ) * weightedMean q (fun a => rowEnergy (f j) (X a))|) j) hmr.le
  · obtain ⟨j, hj⟩ := finiteMaximum_attained (fun j : Fin J =>
      |(∑ i, rowEnergy (f j) (X (x i))) -
        (m : ℝ) * weightedMean q (fun a => rowEnergy (f j) (X a))|)
    change _ = absoluteMaximum (fun j a => rowEnergy (f j) (X a))
      (fun j => weightedMean q (fun a => rowEnergy (f j) (X a))) x at hj
    rw [← hj, ← hterm]
    exact le_finiteMaximum (fun j : Fin J =>
      |(m : ℝ)⁻¹ * (∑ i, rowEnergy (f j) (X (x i))) -
        weightedMean q (fun a => rowEnergy (f j) (X a))|) j

/-- The expectation estimate with coefficient `16` gives the exact relative
failure bound with threshold coefficient `88 = 5 * 16 + 8`. -/
theorem finiteRow_relative_tail_of_expected_deviation {N L J m : ℕ}
    (hm : 0 < m) (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    {s K δ : ℝ} (hs : 0 < s) (hK : 0 < K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hX : ∀ a k, ‖X a k‖ ≤ K) (hf : ∀ j, coefficientL1Norm (f j) ≤ Real.sqrt s)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    (h_expectation : weightedMean (productWeight q)
      (finiteRowDeviation X f q : (Fin m → Fin L) → ℝ) ≤
        16 * δ * (1 + finiteRowPopulationSup X f q)) :
    weightedProbability (productWeight q) (fun x : Fin m → Fin L =>
      88 * δ * (1 + finiteRowPopulationSup X f q) < finiteRowDeviation X f q x) ≤
      Real.exp (-(δ^2 * (m : ℝ) / (s * K^2))) := by
  letI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  have hS := finiteRowPopulationSup_nonneg hJ X f q hq
  have hp : 0 < s * K^2 := mul_pos hs (sq_pos_of_pos hK)
  have hmean (j : Fin J) := finiteRowPopulation_le_sup X f q j
  have hexp : weightedMean (productWeight q) (fun x : Fin m → Fin L =>
      absoluteMaximum (fun j a => rowEnergy (f j) (X a))
        (fun j => weightedMean q (fun a => rowEnergy (f j) (X a))) x / (m : ℝ)) ≤
      16 * δ * (1 + finiteRowPopulationSup X f q) := by
    simpa only [← finiteRowDeviation_eq_absoluteMaximum hm hJ X f q] using h_expectation
  have htail := finite_energy_supremum_relative_tail hm
    (fun j a => rowEnergy (f j) (X a))
    (fun j => weightedMean q (fun a => rowEnergy (f j) (X a))) q
    hp hS (a := 16) (δ := δ) (by norm_num) hδ hδ1 hq hqs
    (fun j a => rowEnergy_nonneg (f j) (X a))
    (fun j a => rowEnergy_le_radius (f j) (X a) hs.le hK.le (hf j) (hX a))
    hmean hmean hexp
  norm_num only at htail
  simpa only [← finiteRowDeviation_eq_absoluteMaximum hm hJ X f q] using htail

/-- A uniform finite-law expectation estimate discharges the fixed-parameter
finite concentration predicate. The expectation will be supplied by chaining. -/
theorem finiteRowConcentrationAt_of_expectation_bound {N m : ℕ} {s K δ : ℝ}
    (hm : 0 < m) (hs : 0 < s) (hK : 0 < K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hexp : ∀ L J : ℕ, 0 < L → 0 < J →
      ∀ (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ),
        (∀ a k, ‖X a k‖ ≤ K) →
        (∀ j, coefficientL1Norm (f j) ≤ Real.sqrt s) →
        (∀ a, 0 ≤ q a) → (∑ a, q a = 1) →
        weightedMean (productWeight q) (finiteRowDeviation X f q : (Fin m → Fin L) → ℝ) ≤
          16 * δ * (1 + finiteRowPopulationSup X f q)) :
    FiniteRowConcentrationAt N m s K δ 88 := by
  intro L J hL hJ X f q hX hf hq hqs
  exact finiteRow_relative_tail_of_expected_deviation hm hJ X f q hs hK hδ hδ1
    hX hf hq hqs (hexp L J hL hJ X f q hX hf hq hqs)

end LeanNumDetect.BoundedRieszConcentration
