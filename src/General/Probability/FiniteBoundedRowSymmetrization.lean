import General.Probability.FiniteBoundedRowConcentration
import General.Probability.WeightedSymmetrization
import General.Probability.FiniteBernoulliChaining

/-! Exact finite-law energy symmetrization and the empirical-energy bootstrap
for bounded-row concentration. These deterministic/probabilistic reductions
have no row-complexity or concentration hypothesis. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.BoundedRieszConcentration

open FiniteEntropy FiniteMatrixSampling EmpiricalProcessReplacementVariance

/-- The largest unnormalized sampled energy over a finite coefficient list. -/
noncomputable def finiteRowEnergySumSup {N L J m : ℕ}
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N)
    (x : Fin m → Fin L) : ℝ :=
  sSup (Set.range fun j => ∑ i, rowEnergy (f j) (X (x i)))

/-- Nonnegative scaling commutes with the maximum of a nonempty finite family. -/
theorem finiteMaximum_mul_nonneg {J : Type*} [Fintype J] [Nonempty J]
    (z : J → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    finiteMaximum (fun j => r * z j) = r * finiteMaximum z := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := finiteMaximum_attained (fun j => r * z j)
    rw [← hj]
    exact mul_le_mul_of_nonneg_left (le_finiteMaximum z j) hr
  · obtain ⟨j, hj⟩ := finiteMaximum_attained z
    rw [← hj]
    exact le_finiteMaximum (fun j => r * z j) j

/-- Weighted iid symmetrization of the normalized finite energy deviation.
The constant is exactly `2/m`, with the sign average taken conditionally on
the sample rows. No envelope bound is needed for this finite-class step. -/
theorem finiteRowDeviation_symmetrization {N L J m : ℕ} (hm : 0 < m) (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) :
    weightedMean (productWeight q) (finiteRowDeviation X f q : (Fin m → Fin L) → ℝ) ≤
      (2 / (m : ℝ)) * weightedMean (productWeight q) (fun x : Fin m → Fin L =>
        finiteAverage (bernoulliAbsoluteSupremum (fun j i => rowEnergy (f j) (X (x i))))) := by
  letI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  let Y : Fin L → Fin J → ℝ := fun a j => rowEnergy (f j) (X a)
  let φ : Fin J → (Fin J → ℝ) →ₗ[ℝ] ℝ := fun j => LinearMap.proj j
  have hbounded (v : Fin J → ℝ) : BddAbove (Set.range fun j => |φ j v|) :=
    (Set.finite_range _).bddAbove
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  have hr : 0 ≤ (m : ℝ)⁻¹ := (inv_pos.mpr hmr).le
  have hcenter : weightedVectorMean (productWeight q)
      (fun x : Fin m → Fin L => (m : ℝ)⁻¹ • ∑ i, Y (x i)) = weightedVectorMean q Y := by
    rw [weightedVectorMean_smul, weightedVectorMean_iid_sum q hqs Y m,
      smul_smul, inv_mul_cancel₀ hmr.ne', one_smul]
  have hdeviation (x : Fin m → Fin L) :
      restrictedAbsoluteSup φ ((m : ℝ)⁻¹ • (∑ i, Y (x i)) -
        weightedVectorMean (productWeight q)
          (fun z : Fin m → Fin L => (m : ℝ)⁻¹ • ∑ i, Y (z i))) =
        finiteRowDeviation X f q x := by
    rw [hcenter]
    simp only [restrictedAbsoluteSup, finiteRowDeviation, φ, Y, LinearMap.proj_apply,
      Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, weightedVectorMean,
      weightedMean, smul_eq_mul]
  have hsigned (σ : Fin m → Bool) (x : Fin m → Fin L) :
      restrictedAbsoluteSup φ ((m : ℝ)⁻¹ •
        (∑ i, finiteBernoulliSign (σ i) • Y (x i))) =
      (m : ℝ)⁻¹ * bernoulliAbsoluteSupremum
        (fun j i => rowEnergy (f j) (X (x i))) σ := by
    have heq : (fun j => |φ j ((m : ℝ)⁻¹ •
        (∑ i, finiteBernoulliSign (σ i) • Y (x i)))|) =
        (fun j => (m : ℝ)⁻¹ *
          |∑ i, finiteBernoulliSign (σ i) * rowEnergy (f j) (X (x i))|) := by
      funext j
      simp only [φ, Y, LinearMap.proj_apply, Pi.smul_apply,
        Finset.sum_apply, smul_eq_mul, abs_mul, abs_of_nonneg hr]
    rw [restrictedAbsoluteSup, heq]
    exact finiteMaximum_mul_nonneg
      (fun j => |∑ i, finiteBernoulliSign (σ i) * rowEnergy (f j) (X (x i))|) hr
  have h := weightedIid_restrictedSup_symmetrization (m := m) q hq hqs Y φ hbounded (m : ℝ)⁻¹
  simp_rw [hdeviation, hsigned, weightedMean_mul] at h
  have hscale : finiteAverage (fun σ : Fin m → Bool =>
      (m : ℝ)⁻¹ * weightedMean (productWeight q) (fun x : Fin m → Fin L =>
        bernoulliAbsoluteSupremum (fun j i => rowEnergy (f j) (X (x i))) σ)) =
      (m : ℝ)⁻¹ * finiteAverage (fun σ : Fin m → Bool =>
        weightedMean (productWeight q) (fun x : Fin m → Fin L =>
          bernoulliAbsoluteSupremum (fun j i => rowEnergy (f j) (X (x i))) σ)) := by
    simpa only [smul_eq_mul] using finiteAverage_smul (m : ℝ)⁻¹
      (fun σ : Fin m → Bool => weightedMean (productWeight q) (fun x : Fin m → Fin L =>
        bernoulliAbsoluteSupremum (fun j i => rowEnergy (f j) (X (x i))) σ))
  rw [hscale, finiteAverage_weightedMean_comm] at h
  simpa only [div_eq_mul_inv, mul_assoc] using h

/-- The largest sampled energy is controlled pointwise by the population
supremum plus the maximal empirical-mean error. -/
theorem finiteRowEnergySumSup_le_population_add_deviation {N L J m : ℕ}
    (hm : 0 < m) (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    (x : Fin m → Fin L) :
    finiteRowEnergySumSup X f x ≤
      (m : ℝ) * (finiteRowPopulationSup X f q + finiteRowDeviation X f q x) := by
  letI : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  have hdev : |(m : ℝ)⁻¹ * (∑ i, rowEnergy (f j) (X (x i))) -
      weightedMean q (fun a => rowEnergy (f j) (X a))| ≤ finiteRowDeviation X f q x :=
    le_csSup (Set.finite_range _).bddAbove ⟨j, rfl⟩
  have hpop := finiteRowPopulation_le_sup X f q j
  have hmean : (m : ℝ)⁻¹ * (∑ i, rowEnergy (f j) (X (x i))) ≤
      finiteRowPopulationSup X f q + finiteRowDeviation X f q x := by
    have hle := (le_abs_self _).trans hdev
    linarith
  have hmul := mul_le_mul_of_nonneg_left hmean hmr.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hmr.ne', one_mul] using hmul

/-- Averaging the empirical-energy bootstrap preserves its population term
and its expected deviation exactly. -/
theorem weightedMean_finiteRowEnergySumSup_le {N L J m : ℕ}
    (hm : 0 < m) (hJ : 0 < J)
    (X : Fin L → ComplexVector N) (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) :
    weightedMean (productWeight q) (finiteRowEnergySumSup X f : (Fin m → Fin L) → ℝ) ≤
      (m : ℝ) * (finiteRowPopulationSup X f q +
        weightedMean (productWeight q) (finiteRowDeviation X f q : (Fin m → Fin L) → ℝ)) := by
  have h := weightedMean_mono (productWeight_nonneg q hq)
    (finiteRowEnergySumSup_le_population_add_deviation hm hJ X f q)
  simpa only [weightedMean_mul, FiniteEntropy.weightedMean_add,
    weightedMean_const _ (productWeight_sum q hqs m)] using h

end LeanNumDetect.BoundedRieszConcentration
