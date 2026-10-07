import General.Probability.CausalWeakNetExpectation
import General.Probability.WeightedSymmetrization
import General.Probability.BoundedRowSelfConsistency
import General.Probability.FiniteBoundedRowConcentration
import General.Probability.FiniteBoundedRowSymmetrization
import General.Probability.FiniteBoundedRowZeroTarget

/-!
# Sharp expectation for finite bounded-row laws

The constructed causal weak-shell estimate is averaged under arbitrary
finite probability weights. Square-root Jensen preserves its energy
dependence; weighted symmetrization and the scalar self-consistency bound
then close the normalized expected deviation estimate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.BoundedRieszConcentration

open LeanNumDetect.FiniteMatrixSampling LeanNumDetect.FiniteEntropy

/-- Jensen averages the fixed-row weak-shell estimate under arbitrary
finite probability weights, retaining the expected empirical energy. -/
theorem weightedRows_bernoulli_expectation_le
    {N L J m : ℕ} (hN : 0 < N) (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    {s K δ : ℝ} (hs : 0 < s) (hK : 0 < K) (hδ : 0 < δ) (hpδ : 4 * δ ≤ s * K ^ 2)
    (hX : ∀ a k, ‖X a k‖ ≤ K) (hf : ∀ j, coefficientL1Norm (f j) ≤ Real.sqrt s)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    (j₀ : Fin J) (hfzero : f j₀ = 0) :
    weightedMean (productWeight q) (fun x : Fin m → Fin L =>
      finiteAverage (bernoulliAbsoluteSupremum (fun j i => rowEnergy (f j) (X (x i))))) ≤
      3 * δ * (m : ℝ) +
        Real.sqrt (10000000000 * (s * K ^ 2) * Real.log (Real.exp 1 * (N : ℝ)) *
          Real.log (s * K ^ 2 / δ) ^ 2) *
        Real.sqrt ((16 / 9 : ℝ) * weightedMean (productWeight q)
          (fun x : Fin m → Fin L => sSup (Set.range fun j => ∑ i, rowEnergy (f j) (X (x i)))) +
            δ * (m : ℝ)) := by
  letI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  let P := productWeight q (m := m)
  have hP : ∀ x, 0 ≤ P x := productWeight_nonneg q hq
  have hPs : ∑ x, P x = 1 := productWeight_sum q hqs m
  let Q := fun x : Fin m → Fin L => sSup (Set.range fun j => ∑ i, rowEnergy (f j) (X (x i)))
  let Z := 10000000000 * (s * K ^ 2) * Real.log (Real.exp 1 * (N : ℝ)) *
    Real.log (s * K ^ 2 / δ) ^ 2
  have hQ0 (x : Fin m → Fin L) : 0 ≤ Q x := by
    have h : (∑ i, rowEnergy (f j₀) (X (x i))) ≤ Q x :=
      le_csSup (Set.finite_range (fun j => ∑ i, rowEnergy (f j) (X (x i)))).bddAbove ⟨j₀, rfl⟩
    exact (Finset.sum_nonneg fun i _ => rowEnergy_nonneg _ _).trans h
  have hrow (x : Fin m → Fin L) : finiteAverage
      (bernoulliAbsoluteSupremum (fun j i => rowEnergy (f j) (X (x i)))) ≤
        3 * δ * (m : ℝ) + Real.sqrt Z * Real.sqrt ((16 / 9 : ℝ) * Q x + δ * (m : ℝ)) := by
    have h := boundedRows_bernoulli_expectation_le hN f (fun i => X (x i)) hs hK hδ hpδ hf
      (fun i => hX (x i)) j₀ hfzero
    simpa only [Q, Z, mul_comm (Real.sqrt Z)] using h
  have hJensen := weightedMean_sqrt_le P
    (fun x => (16 / 9 : ℝ) * Q x + δ * (m : ℝ)) hP hPs
      (fun x => by have h := hQ0 x; positivity)
  calc
    _ ≤ weightedMean P (fun x : Fin m → Fin L => 3 * δ * (m : ℝ) +
        Real.sqrt Z * Real.sqrt ((16 / 9 : ℝ) * Q x + δ * (m : ℝ))) := weightedMean_mono hP hrow
    _ = 3 * δ * (m : ℝ) + Real.sqrt Z * weightedMean P
        (fun x : Fin m → Fin L => Real.sqrt ((16 / 9 : ℝ) * Q x + δ * (m : ℝ))) := by
      rw [FiniteEntropy.weightedMean_add, weightedMean_const P hPs, weightedMean_mul]
    _ ≤ 3 * δ * (m : ℝ) + Real.sqrt Z * Real.sqrt
        (weightedMean P (fun x : Fin m → Fin L => (16 / 9 : ℝ) * Q x + δ * (m : ℝ))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hJensen (Real.sqrt_nonneg _))
    _ = _ := by rw [FiniteEntropy.weightedMean_add, weightedMean_mul, weightedMean_const P hPs]

/-- The sample-size condition controls the explicit square-root entropy
budget by one tenth of the prescribed distortion times `√m`. -/
theorem boundedRow_sampling_budget_sqrt_le {N m : ℕ}
    {p δ : ℝ} (hδ : 0 < δ)
    (hsample : 1000000000000 * p * δ⁻¹ ^ 2 *
      Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2 ≤ (m : ℝ)) :
    Real.sqrt (10000000000 * p * Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2) ≤
      δ / 10 * Real.sqrt (m : ℝ) := by
  have h := mul_le_mul_of_nonneg_left hsample (sq_nonneg δ)
  have heq : δ ^ 2 * (1000000000000 * p * δ⁻¹ ^ 2 *
      Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2) =
        100 * (10000000000 * p * Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2) := by
    field_simp
    ring
  rw [heq] at h
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    nlinarith

/-- Normalization of the raw symmetrized energy estimate gives the exact
scalar inequality used by self-consistency. -/
theorem boundedRow_raw_bound_normalization
    {m δ Z U : ℝ} (hm : 0 < m) (hδ : 0 < δ)
    (hZ : Real.sqrt Z ≤ δ / 10 * Real.sqrt m) :
    2 / m * (3 * δ * m + Real.sqrt Z * Real.sqrt (m * U)) ≤
      6 * δ + δ / 5 * Real.sqrt U := by
  apply (mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right hZ (Real.sqrt_nonneg _))) (by positivity : 0 ≤ 2 / m)).trans_eq
  rw [Real.sqrt_mul hm.le]
  have hs := Real.sq_sqrt hm.le
  field_simp [hm.ne']
  ring_nf
  rw [hs]

theorem finiteRowDeviation_nonneg {N L J m : ℕ} (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    (x : Fin m → Fin L) : 0 ≤ finiteRowDeviation X f q x := by
  exact (abs_nonneg _).trans (le_csSup (Set.finite_range _).bddAbove
    (Set.mem_range_self (f := fun j => |(m : ℝ)⁻¹ * (∑ i, rowEnergy (f j) (X (x i))) -
      weightedMean q (fun a => rowEnergy (f j) (X a))|) (⟨0, hJ⟩ : Fin J)))

/-- The trivial finite-law envelope retains the original normalization. -/
theorem finiteRowDeviation_le_radius {N L J m : ℕ} (hm : 0 < m) (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hX : ∀ a k, ‖X a k‖ ≤ K) (hf : ∀ j, coefficientL1Norm (f j) ≤ Real.sqrt s)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) (x : Fin m → Fin L) :
    finiteRowDeviation X f q x ≤ s * K ^ 2 := by
  letI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  dsimp only
  have hpop0 : 0 ≤ weightedMean q (fun a => rowEnergy (f j) (X a)) :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hq a) (rowEnergy_nonneg _ _)
  have hpop := weightedMean_mono hq (fun a => rowEnergy_le_radius (f j) (X a)
    hs hK (hf j) (hX a))
  rw [weightedMean_const q hqs] at hpop
  have hemp0 : 0 ≤ (m : ℝ)⁻¹ * ∑ i, rowEnergy (f j) (X (x i)) := by
    apply mul_nonneg (inv_nonneg.mpr hmr.le)
    exact Finset.sum_nonneg fun i _ => rowEnergy_nonneg _ _
  have hemp : (m : ℝ)⁻¹ * ∑ i, rowEnergy (f j) (X (x i)) ≤ s * K ^ 2 := by
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      rowEnergy_le_radius (f j) (X (x i)) hs hK (hf j) (hX (x i)))
    have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hmr.le)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ hmr.ne', one_mul] using h
  apply abs_le.mpr
  constructor <;> linarith

/-- The sharp expected deviation for a finite weighted law and a target
class containing zero, in the nontrivial logarithmic regime. -/
theorem finiteBoundedRow_expectation_of_zeroTarget
    {N L J m : ℕ} (hN : 0 < N) (hm : 0 < m) (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    {s K δ : ℝ} (hs : 0 < s) (hK : 0 < K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hpδ : 4 * δ ≤ s * K ^ 2)
    (hX : ∀ a k, ‖X a k‖ ≤ K) (hf : ∀ j, coefficientL1Norm (f j) ≤ Real.sqrt s)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    (j₀ : Fin J) (hfzero : f j₀ = 0)
    (hsample : 1000000000000 * (s * K ^ 2) * δ⁻¹ ^ 2 *
      Real.log (Real.exp 1 * (N : ℝ)) * Real.log (s * K ^ 2 / δ) ^ 2 ≤ (m : ℝ)) :
    weightedMean (productWeight q) (finiteRowDeviation X f q : (Fin m → Fin L) → ℝ) ≤
      16 * δ * (1 + finiteRowPopulationSup X f q) := by
  let e := weightedMean (productWeight q) (finiteRowDeviation X f q : (Fin m → Fin L) → ℝ)
  let S := finiteRowPopulationSup X f q
  let Z := 10000000000 * (s * K ^ 2) * Real.log (Real.exp 1 * (N : ℝ)) *
    Real.log (s * K ^ 2 / δ) ^ 2
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have he : 0 ≤ e := Finset.sum_nonneg fun x _ =>
    mul_nonneg (productWeight_nonneg q hq x) (finiteRowDeviation_nonneg hJ X f q x)
  have hS : 0 ≤ S := finiteRowPopulationSup_nonneg hJ X f q hq
  have hsym := finiteRowDeviation_symmetrization hm hJ X f q hq hqs
  have hraw := weightedRows_bernoulli_expectation_le (m := m) hN hJ X f q hs hK hδ hpδ hX hf hq hqs j₀ hfzero
  have hmass := weightedMean_finiteRowEnergySumSup_le hm hJ X f q hq hqs
  have hinner : (16 / 9 : ℝ) * weightedMean (productWeight q)
      (finiteRowEnergySumSup X f : (Fin m → Fin L) → ℝ) + δ * (m : ℝ) ≤
        (m : ℝ) * ((16 / 9 : ℝ) * (S + e) + δ) := by
    have h := mul_le_mul_of_nonneg_left hmass (by norm_num : (0 : ℝ) ≤ 16 / 9)
    dsimp only [S, e]
    nlinarith
  have hbudget : Real.sqrt Z ≤ δ / 10 * Real.sqrt (m : ℝ) :=
    boundedRow_sampling_budget_sqrt_le hδ hsample
  have hclosed : e ≤ 6 * δ + δ / 5 * Real.sqrt ((16 / 9 : ℝ) * (S + e) + δ) := by
    calc
      e ≤ 2 / (m : ℝ) * weightedMean (productWeight q) (fun x : Fin m → Fin L =>
          finiteAverage (bernoulliAbsoluteSupremum (fun j i => rowEnergy (f j) (X (x i))))) := hsym
      _ ≤ 2 / (m : ℝ) * (3 * δ * (m : ℝ) + Real.sqrt Z *
          Real.sqrt ((16 / 9 : ℝ) * weightedMean (productWeight q)
            (finiteRowEnergySumSup X f : (Fin m → Fin L) → ℝ) + δ * (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ ≤ 2 / (m : ℝ) * (3 * δ * (m : ℝ) + Real.sqrt Z *
          Real.sqrt ((m : ℝ) * ((16 / 9 : ℝ) * (S + e) + δ))) := by
        gcongr
      _ ≤ _ := boundedRow_raw_bound_normalization hmr hδ hbudget
  exact boundedRow_expectation_selfConsistency he hS hδ hδ1 hclosed

/-- The sharp finite weighted expectation estimate has the exact original
sample-size dependence and no extra hypothesis on the target class. -/
theorem finiteBoundedRow_expectation_le
    {N L J m : ℕ} (hN : 0 < N) (hm : 0 < m) (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    {s K δ : ℝ} (hs : 0 < s) (hK : 0 < K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hX : ∀ a k, ‖X a k‖ ≤ K) (hf : ∀ j, coefficientL1Norm (f j) ≤ Real.sqrt s)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    (hsample : 1000000000000 * (s * K ^ 2) * δ⁻¹ ^ 2 *
      Real.log (Real.exp 1 * (N : ℝ)) * Real.log (s * K ^ 2 / δ) ^ 2 ≤ (m : ℝ)) :
    weightedMean (productWeight q) (finiteRowDeviation X f q : (Fin m → Fin L) → ℝ) ≤
      16 * δ * (1 + finiteRowPopulationSup X f q) := by
  by_cases hpδ : 4 * δ ≤ s * K ^ 2
  · have h := finiteBoundedRow_expectation_of_zeroTarget hN hm (by omega : 0 < J + 1)
      X (zeroExtendedTarget f) q hs hK hδ hδ1 hpδ hX
      (coefficientL1Norm_cons_zero_bound f hs.le hf) hq hqs
      (⟨0, by omega⟩ : Fin (J + 1)) (by simp [zeroExtendedTarget]) hsample
    have hDfun : (finiteRowDeviation X (zeroExtendedTarget f) q : (Fin m → Fin L) → ℝ) =
        finiteRowDeviation X f q := funext (finiteRowDeviation_cons_zero hJ X f q)
    rwa [hDfun, finiteRowPopulationSup_cons_zero hJ X f q hq] at h
  · have hpop := finiteRowPopulationSup_nonneg hJ X f q hq
    have h := weightedMean_mono (productWeight_nonneg q hq)
      (finiteRowDeviation_le_radius hm hJ X f q hs.le hK.le hX hf hq hqs)
    rw [weightedMean_const _ (productWeight_sum q hqs m)] at h
    have hδS : 0 ≤ δ * finiteRowPopulationSup X f q := mul_nonneg hδ.le hpop
    nlinarith

end LeanNumDetect.BoundedRieszConcentration
