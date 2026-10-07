import Mathlib.Probability.IdentDistribIndep
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Model and elementary analytic estimates for bounded complex random rows.
These statements retain arbitrary probability distributions and arbitrary
subsets of the coordinate ℓ¹ ball. They contain no concentration assumption. -/

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

end LeanNumDetect.BoundedRieszConcentration
