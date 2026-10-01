import Mathlib.Probability.IdentDistribIndep
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

The only admission in this file is the original concentration theorem.
Conversions to particular dictionaries or sampling laws belong in fully
proved modules outside `External`.
-/

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory ProbabilityTheory

universe u v

namespace LeanNumDetect.BoundedRieszConcentration

/-- The source's complex coordinate space `ℂ^N`. The theorem uses its
coordinate ℓ¹ norm and complex pairing, rather than the ambient Pi norm. -/
abbrev ComplexVector (N : ℕ) := Fin N → ℂ

/-- The coordinate ℓ¹ norm in the source's target-set hypothesis. -/
noncomputable def coefficientL1Norm {N : ℕ} (f : ComplexVector N) : ℝ := ∑ j, ‖f j‖

/-- Complex inner product, conjugate-linear in its first variable. -/
def rowPairing {N : ℕ} (f x : ComplexVector N) : ℂ :=
  ∑ j, star (f j) * x j

/-- Squared magnitude of one row measurement. -/
noncomputable def rowEnergy {N : ℕ} (f x : ComplexVector N) : ℝ := ‖rowPairing f x‖ ^ 2

/-- Expected squared row measurement, with the original row distribution. -/
noncomputable def populationEnergy {N : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ComplexVector N) (f : ComplexVector N) : ℝ :=
  ∫ ω, rowEnergy f (X ω) ∂μ

/-- The source's supremum of the population energy over its arbitrary target set. -/
noncomputable def populationEnergySup {N : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ComplexVector N) (T : Set (ComplexVector N)) : ℝ :=
  sSup (populationEnergy μ X '' T)

/-- Average of the sampled squared measurements, normalized by the number
of samples exactly as in the source. The concentration result requires `m > 0`. -/
noncomputable def empiricalEnergy {N m : ℕ} {Ω : Type u}
    (rows : Fin m → Ω → ComplexVector N) (ω : Ω) (f : ComplexVector N) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i, rowEnergy f (rows i ω)

/-- The absolute supremum of the empirical energy error. Empty target sets
have deviation zero, in accord with the vacuous uniform estimate. -/
noncomputable def restrictedDeviation {N m : ℕ} {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ComplexVector N)
    (rows : Fin m → Ω' → ComplexVector N) (T : Set (ComplexVector N)) (ω : Ω') : ℝ :=
  sSup ((fun f => |empiricalEnergy rows ω f - populationEnergy μ X f|) '' T)

@[simp] theorem coefficientL1Norm_zero {N : ℕ} :
    coefficientL1Norm (0 : ComplexVector N) = 0 := by
  simp [coefficientL1Norm]

@[simp] theorem rowPairing_zero_left {N : ℕ} (x : ComplexVector N) :
    rowPairing 0 x = 0 := by
  simp [rowPairing]

@[simp] theorem rowPairing_zero_right {N : ℕ} (f : ComplexVector N) :
    rowPairing f 0 = 0 := by
  simp [rowPairing]

theorem rowEnergy_nonneg {N : ℕ} (f x : ComplexVector N) : 0 ≤ rowEnergy f x :=
  sq_nonneg _

@[simp] theorem rowEnergy_zero_left {N : ℕ} (x : ComplexVector N) :
    rowEnergy 0 x = 0 := by
  simp [rowEnergy]

@[simp] theorem rowEnergy_zero_right {N : ℕ} (f : ComplexVector N) :
    rowEnergy f 0 = 0 := by
  simp [rowEnergy]

@[simp] theorem populationEnergy_zero {N : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ComplexVector N) : populationEnergy μ X 0 = 0 := by
  simp [populationEnergy]

@[simp] theorem empiricalEnergy_zero {N m : ℕ} {Ω : Type u}
    (rows : Fin m → Ω → ComplexVector N) (ω : Ω) : empiricalEnergy rows ω 0 = 0 := by
  simp [empiricalEnergy]

@[simp] theorem populationEnergySup_empty {N : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ComplexVector N) : populationEnergySup μ X ∅ = 0 := by
  simp [populationEnergySup]

@[simp] theorem restrictedDeviation_empty {N m : ℕ} {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ComplexVector N)
    (rows : Fin m → Ω' → ComplexVector N) (ω : Ω') :
    restrictedDeviation μ X rows ∅ ω = 0 := by
  simp [restrictedDeviation]

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
  sorry

end LeanNumDetect.BoundedRieszConcentration
