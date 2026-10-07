import General.Probability.FiniteBoundedRowExpectation
import General.Probability.BoundedRowsFiniteReduction

/-!
# Concentration for arbitrary bounded independent complex rows

Original source: S. Brugiapaglia, S. Dirksen, H. C. Jung, and H. Rauhut,
*Sparse recovery in bounded Riesz systems with applications to numerical
methods for PDEs*, Applied and Computational Harmonic Analysis 53 (2021),
231--269. Theorem 1.1, pages 2--3 of the author's manuscript and
arXiv:2005.06994v1, page 2.

The result below retains arbitrary bounded row distributions, independent
identically distributed samples, an arbitrary target subset of the complex
ℓ¹ ball, all three universal constants, the original sample rate, and the
original additive-plus-covariance deviation. No Riesz, orthogonality,
isotropy, atomic dictionary, or finite-population hypothesis is inserted.

The two probability spaces allow the reference row and the sampled rows
to be represented on their own spaces. `IdentDistrib` includes their
almost-everywhere measurability. The source's complex inner product is
written explicitly as a finite sum with conjugation in the first variable.

The proof is complete. Causal weak atomic nets bound the expected
empirical supremum at the original squared-logarithm rate; weighted
replacement entropy gives its variance-sensitive tail. Finite measurable
quantization and finite subsets of the actual coefficient class transfer
the result to arbitrary laws and targets without changing the hypotheses.
-/

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory ProbabilityTheory

universe u v

namespace LeanNumDetect.BoundedRieszConcentration

/-- Original bounded-row concentration theorem of Brugiapaglia--Dirksen--
Jung--Rauhut, Theorem 1.1 (arXiv:2005.06994v1, page 2).

The source states that the success probability *exceeds*
`1 - 2 exp(-δ² m / (s K²))`; the strict probability inequality is retained.
The sample condition uses `log(e N)` and `log(s K² / δ)` literally, without
replacing them by project-specific logarithmic envelopes. The sparsity-radius
parameter `s` is positive real: this theorem concerns the radius of a whole
ℓ¹ ball, not only an integer support size.

The constants are quantified before all dimensions, probability spaces,
random variables, sets, and remaining parameters. Their numerical values in
Remark 1.2 are not used. -/
theorem boundedRows_concentration :
    ∃ κ c₀ c₁ : ℝ, 0 < κ ∧ 0 < c₀ ∧ 0 < c₁ ∧
      ∀ (N m : ℕ), 0 < N → 0 < m →
      ∀ (s K δ : ℝ), 0 < s → 0 < K → 0 < δ → δ < κ →
      ∀ (Ω : Type u) (Ω' : Type v) [MeasurableSpace Ω] [MeasurableSpace Ω']
        (μ : Measure Ω) (ν : Measure Ω'),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      ∀ (X : Ω → ComplexVector N) (rows : Fin m → Ω' → ComplexVector N),
      iIndepFun rows ν → (∀ i, IdentDistrib (rows i) X ν μ) →
      (∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) →
      ∀ (T : Set (ComplexVector N)),
      (∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s) →
      c₀ * K ^ 2 * δ⁻¹ ^ 2 * s * Real.log (Real.exp 1 * (N : ℝ)) *
        Real.log (s * K ^ 2 / δ) ^ 2 ≤ (m : ℝ) →
      1 - 2 * Real.exp (-(δ ^ 2 * (m : ℝ) / (s * K ^ 2))) <
        (ν {ω | restrictedDeviation μ X rows T ω ≤
          c₁ * (δ + δ * populationEnergySup μ X T)}).toReal := by
  refine ⟨1, 1000000000000, 178, by norm_num, by norm_num, by norm_num, ?_⟩
  intro N m hN hm s K δ hs hK hδ hδκ Ω Ω' instΩ instΩ' μ ν hμ hν
    X rows hindep hcopy hbound T hT hsample
  letI : IsProbabilityMeasure μ := hμ
  letI : IsProbabilityMeasure ν := hν
  have hδ1 : δ ≤ 1 := hδκ.le
  have hsample' : 1000000000000 * (s * K ^ 2) * δ⁻¹ ^ 2 *
      Real.log (Real.exp 1 * (N : ℝ)) * Real.log (s * K ^ 2 / δ) ^ 2 ≤ (m : ℝ) := by
    convert hsample using 1 <;> ring
  have hfinite : FiniteRowConcentrationAt N m s K δ 88 := by
    apply finiteRowConcentrationAt_of_expectation_bound hm hs hK hδ hδ1
    intro L J _hL hJ X₀ f q hX₀ hf hq hqs
    exact finiteBoundedRow_expectation_le hN hm hJ X₀ f q hs hK hδ hδ1
      hX₀ hf hq hqs hsample'
  have h := boundedRows_concentration_of_finite hm hs hK hδ hδ1
    (B := 88) (by norm_num) hfinite μ ν X rows hindep hcopy hbound T hT
  simpa only [show (2 * (88 : ℝ) + 2) = 178 by norm_num] using h

end LeanNumDetect.BoundedRieszConcentration
