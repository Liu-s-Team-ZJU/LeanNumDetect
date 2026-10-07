import General.Probability.BoundedRieszConcentration
import General.Probability.FiniteUniformLaw
import General.Probability.BoundedAtomicRows

/-!
Fully proved conversion of the original bounded-row concentration theorem
to a finite complex dictionary. The population is uniform, the iid outcomes
are actual coordinate tuples, and the coefficient class may have a redundant
or singular covariance. The only external dependency is the original BDJR
Theorem 1.1; no specialized concentration result is admitted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section

/-- The function-valued random row in the source's complex pairing convention. -/
def atomicSourceRow {N Q : ℕ} (row : Fin N → Fin Q → ℂ) (k : Fin N) :
    BoundedRieszConcentration.ComplexVector Q := fun j => star (row k j)

/-- Exact agreement of the source's conjugate-linear pairing energy and
the bilinear dictionary evaluation. -/
theorem sourceRowEnergy_eq_atomicRowEnergy {N Q : ℕ}
    (row : Fin N → Fin Q → ℂ) (k : Fin N) (x : EuclideanSpace ℂ (Fin Q)) :
    BoundedRieszConcentration.rowEnergy (ofLp x) (atomicSourceRow row k) =
      atomicRowEnergy row k x := by
  unfold BoundedRieszConcentration.rowEnergy BoundedRieszConcentration.rowPairing
  have hstar : (∑ j, star (ofLp x j) * atomicSourceRow row k j) =
      star (∑ j, row k j * ofLp x j) := by
    simp only [atomicSourceRow, star_sum, star_mul, mul_comm]
  rw [hstar, norm_star]
  rfl

/-- The source's coefficient target is exactly the coordinate image of
the project's Euclidean coefficient class. -/
def atomicSourceClass {N Q : ℕ} (S : ℝ) (row : Fin N → Fin Q → ℂ) :
    Set (BoundedRieszConcentration.ComplexVector Q) :=
  ofLp '' atomicCoefficientClass S row

theorem atomicSourceClass_l1_le {N Q : ℕ} (S : ℝ)
    (row : Fin N → Fin Q → ℂ) :
    ∀ f ∈ atomicSourceClass S row,
      BoundedRieszConcentration.coefficientL1Norm f ≤ Real.sqrt S := by
  rintro _ ⟨x, hx, rfl⟩
  exact hx.1

section FiniteLaw

variable {N Q m : ℕ} [MeasurableSpace (Fin N)] [MeasurableSingletonClass (Fin N)]

theorem sourcePopulationEnergy_eq_atomicMeanEnergy
    (row : Fin N → Fin Q → ℂ) (x : EuclideanSpace ℂ (Fin Q)) :
    BoundedRieszConcentration.populationEnergy (finiteUniformMeasure (Fin N))
      (atomicSourceRow row) (ofLp x) = atomicMeanEnergy row x := by
  unfold BoundedRieszConcentration.populationEnergy atomicMeanEnergy
  rw [integral_finiteUniformMeasure]
  apply finiteAverage_congr
  intro k
  exact sourceRowEnergy_eq_atomicRowEnergy row k x

theorem sourcePopulationEnergySup_le_one (S : ℝ) (row : Fin N → Fin Q → ℂ) :
    BoundedRieszConcentration.populationEnergySup (finiteUniformMeasure (Fin N))
      (atomicSourceRow row) (atomicSourceClass S row) ≤ 1 := by
  apply csSup_le
    (show (BoundedRieszConcentration.populationEnergy (finiteUniformMeasure (Fin N))
        (atomicSourceRow row) '' atomicSourceClass S row).Nonempty from
      ⟨0, ⟨0, ⟨0, zero_mem_atomicCoefficientClass S row, rfl⟩, by simp⟩⟩)
  · rintro _ ⟨f, ⟨x, hx, rfl⟩, rfl⟩
    rw [sourcePopulationEnergy_eq_atomicMeanEnergy]
    exact hx.2

omit [MeasurableSpace (Fin N)] [MeasurableSingletonClass (Fin N)] in
theorem sourceEmpiricalEnergy_eq_atomicIidEnergy (row : Fin N → Fin Q → ℂ)
    (ω : Fin m → Fin N) (x : EuclideanSpace ℂ (Fin Q)) :
    BoundedRieszConcentration.empiricalEnergy
      (fun i ω => atomicSourceRow row (ω i)) ω (ofLp x) =
      finiteAverage (fun i => atomicRowEnergy row (ω i) x) := by
  unfold BoundedRieszConcentration.empiricalEnergy finiteAverage
  simp only [Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact sourceRowEnergy_eq_atomicRowEnergy row (ω i) x

theorem sourceRestrictedDeviation_eq_atomicIidDeviation (S : ℝ)
    (row : Fin N → Fin Q → ℂ) (ω : Fin m → Fin N) :
    BoundedRieszConcentration.restrictedDeviation (finiteUniformMeasure (Fin N))
      (atomicSourceRow row) (fun i ω => atomicSourceRow row (ω i))
      (atomicSourceClass S row) ω =
      atomicGramDeviation S row (atomicIidMeanGram row ω) := by
  unfold BoundedRieszConcentration.restrictedDeviation atomicGramDeviation
    restrictedAbsoluteSup
  congr 1
  ext r
  constructor
  · rintro ⟨f, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    dsimp only
    rw [atomicCoefficientTest_centered, quadratic_atomicIidMeanGram,
      sourceEmpiricalEnergy_eq_atomicIidEnergy, sourcePopulationEnergy_eq_atomicMeanEnergy]
  · rintro ⟨x, rfl⟩
    refine ⟨ofLp x.val, ⟨x.val, x.property, rfl⟩, ?_⟩
    dsimp only
    rw [atomicCoefficientTest_centered, quadratic_atomicIidMeanGram,
      sourceEmpiricalEnergy_eq_atomicIidEnergy, sourcePopulationEnergy_eq_atomicMeanEnergy]

end FiniteLaw

/-- Uniform iid concentration for a finite, possibly redundant, unit-bounded
dictionary. The constants are the original universal BDJR constants;
the full mean energy bound on the coefficient class is proved above. -/
theorem boundedAtomicIid_concentration :
    ∃ κ c₀ c₁ : ℝ, 0 < κ ∧ 0 < c₀ ∧ 0 < c₁ ∧
      ∀ (N Q m : ℕ), 0 < N → 0 < Q → 0 < m →
      ∀ (S δ : ℝ), 0 < S → 0 < δ → δ < κ →
      ∀ (row : Fin N → Fin Q → ℂ), (∀ k j, ‖row k j‖ ≤ 1) →
      c₀ * δ⁻¹ ^ 2 * S * Real.log (Real.exp 1 * (Q : ℝ)) *
        Real.log (S / δ) ^ 2 ≤ (m : ℝ) →
      probability (fun ω : Fin m → Fin N =>
        2 * c₁ * δ < atomicGramDeviation S row (atomicIidMeanGram row ω)) ≤
        2 * Real.exp (-(δ ^ 2 * (m : ℝ) / S)) := by
  classical
  obtain ⟨κ, c₀, c₁, hκ, hc₀, hc₁, hsource⟩ :=
    BoundedRieszConcentration.boundedRows_concentration.{0, 0}
  refine ⟨κ, c₀, c₁, hκ, hc₀, hc₁, ?_⟩
  intro N Q m hN hQ hm S δ hS hδ hδκ row hrow hrate
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  letI : MeasurableSpace (Fin N) := ⊤
  have hbase := hsource Q m hQ hm S 1 δ hS (by norm_num) hδ hδκ
    (Fin N) (Fin m → Fin N) (finiteUniformMeasure (Fin N))
    (finiteUniformMeasure (Fin m → Fin N))
    (finiteUniformMeasure_isProbability (Fin N))
    (finiteUniformMeasure_isProbability (Fin m → Fin N))
  have hiid : iIndepFun (fun (i : Fin m) (ω : Fin m → Fin N) =>
      atomicSourceRow row (ω i)) (finiteUniformMeasure (Fin m → Fin N)) :=
    by
      convert iIndepFun_finiteUniform_coordinates (ι := Fin m) (α := Fin N)
        (β := BoundedRieszConcentration.ComplexVector Q) (atomicSourceRow row) using 1
      congr!
  have hcopies : ∀ i : Fin m, IdentDistrib (fun ω : Fin m → Fin N =>
      atomicSourceRow row (ω i)) (atomicSourceRow row)
      (finiteUniformMeasure (Fin m → Fin N)) (finiteUniformMeasure (Fin N)) :=
    by
      convert identDistrib_finiteUniform_coordinate (ι := Fin m) (α := Fin N)
        (β := BoundedRieszConcentration.ComplexVector Q) (atomicSourceRow row) using 1
      congr!
  have hbound : ∀ j : Fin Q, ∀ᵐ k ∂finiteUniformMeasure (Fin N),
      ‖atomicSourceRow row k j‖ ≤ 1 := by
    intro j
    exact Filter.Eventually.of_forall (fun k => by simpa [atomicSourceRow] using hrow k j)
  have hgood := hbase (atomicSourceRow row) (fun i ω => atomicSourceRow row (ω i))
    hiid hcopies hbound (atomicSourceClass S row) (atomicSourceClass_l1_le S row)
    (by simpa using hrate)
  have hgood' : 1 - 2 * Real.exp (-(δ ^ 2 * (m : ℝ) / S)) <
      probability (fun ω : Fin m → Fin N =>
        atomicGramDeviation S row (atomicIidMeanGram row ω) ≤
          c₁ * (δ + δ * BoundedRieszConcentration.populationEnergySup
            (finiteUniformMeasure (Fin N)) (atomicSourceRow row) (atomicSourceClass S row))) := by
    rw [probability_eq_finiteUniformMeasure]
    simpa only [one_pow, mul_one, sourceRestrictedDeviation_eq_atomicIidDeviation] using hgood
  have hthreshold : c₁ * (δ + δ * BoundedRieszConcentration.populationEnergySup
      (finiteUniformMeasure (Fin N)) (atomicSourceRow row) (atomicSourceClass S row)) ≤
      2 * c₁ * δ := by
    have hmean := sourcePopulationEnergySup_le_one S row
    have hmul := mul_le_mul_of_nonneg_left hmean hδ.le
    nlinarith
  have hgood'' : 1 - 2 * Real.exp (-(δ ^ 2 * (m : ℝ) / S)) <
      probability (fun ω : Fin m → Fin N =>
        atomicGramDeviation S row (atomicIidMeanGram row ω) ≤ 2 * c₁ * δ) :=
    hgood'.trans_le (probability_mono fun _ hω => hω.trans hthreshold)
  have hcompl := probability_not (fun ω : Fin m → Fin N =>
    atomicGramDeviation S row (atomicIidMeanGram row ω) ≤ 2 * c₁ * δ)
  simp only [not_le] at hcompl
  linarith

end

end LeanNumDetect.FiniteMatrixSampling
