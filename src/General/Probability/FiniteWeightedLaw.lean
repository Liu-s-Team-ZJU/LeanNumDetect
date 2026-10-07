import General.Probability.FiniteProcessConcentration
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Pi

/-! Exact representation of finite probability measures by their singleton
weights, including their independent product laws. These identities transport
finite weighted inequalities to ordinary measures without a rational-weight
approximation or a uniform-law assumption. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open MeasureTheory

namespace LeanNumDetect.FiniteWeightedLaw

open FiniteEntropy

/-- The real probability mass of a singleton. -/
noncomputable def singletonWeight {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (a : α) : ℝ := (ν {a}).toReal

theorem singletonWeight_nonneg {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (a : α) : 0 ≤ singletonWeight ν a := ENNReal.toReal_nonneg

/-- Singleton masses are a probability simplex on a finite measurable space. -/
theorem singletonWeight_sum {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsProbabilityMeasure ν] :
    ∑ a, singletonWeight ν a = 1 := by
  unfold singletonWeight
  rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top ν {a})]
  have hsum : (∑ a, ν {a}) = ν Set.univ := by
    simpa only [Finset.coe_univ] using
      (sum_measure_singleton (μ := ν) (s := (Finset.univ : Finset α)))
  rw [hsum, measure_univ, ENNReal.toReal_one]

/-- Every real-valued function on a finite probability space is integrable. -/
theorem integrable_finite {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsFiniteMeasure ν]
    (f : α → ℝ) : Integrable f ν := Integrable.of_finite

/-- Finite-law integration is exactly the corresponding weighted sum. -/
theorem integral_eq_weightedMean {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Measure α) [IsFiniteMeasure ν] (f : α → ℝ) :
    (∫ a, f a ∂ν) = weightedMean (singletonWeight ν) f := by
  simpa only [weightedMean, singletonWeight, measureReal_def, smul_eq_mul] using
    integral_fintype (integrable_finite ν f)

/-- Every event in a finite discrete space agrees with its weighted indicator sum. -/
theorem event_probability_eq_weightedProbability {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsFiniteMeasure ν] (P : α → Prop) :
    (ν {a | P a}).toReal = weightedProbability (singletonWeight ν) P := by
  classical
  have hset : MeasurableSet {a | P a} := (Set.toFinite _).measurableSet
  have h := integral_indicator_one (μ := ν) hset
  rw [integral_eq_weightedMean ν] at h
  have hindicator : ({a | P a}.indicator (1 : α → ℝ)) =
      (fun a => if P a then (1 : ℝ) else 0) := by
    funext a
    by_cases ha : P a <;> simp [ha]
  rw [hindicator] at h
  exact h.symm

/-- Singleton probabilities under independent product measures multiply. -/
theorem pi_singletonWeight_eq {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (x : ι → α) :
    singletonWeight (Measure.pi (fun _ : ι => ν)) x = ∏ i, singletonWeight ν (x i) := by
  simp only [singletonWeight, Measure.pi_singleton, ENNReal.toReal_prod]

/-- The exact singleton law of `m` independent draws is `productWeight`. -/
theorem product_singletonWeight_eq {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (m : ℕ) (x : Fin m → α) :
    singletonWeight (Measure.pi (fun _ : Fin m => ν)) x =
      productWeight (singletonWeight ν) x := pi_singletonWeight_eq ν x

/-- Integration under a finite iid law agrees with the finite product-weight
expectation for every real test function. -/
theorem product_integral_eq_weightedMean {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsFiniteMeasure ν] (m : ℕ) (f : (Fin m → α) → ℝ) :
    (∫ x, f x ∂Measure.pi (fun _ : Fin m => ν)) =
      weightedMean (productWeight (singletonWeight ν)) f := by
  rw [integral_eq_weightedMean]
  congr 1
  funext x
  exact product_singletonWeight_eq ν m x

/-- Probabilities of arbitrary events in a finite iid tuple have exactly the
weighted-product form used by the finite concentration theorems. -/
theorem product_event_probability_eq_weightedProbability {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsFiniteMeasure ν] (m : ℕ) (P : (Fin m → α) → Prop) :
    ((Measure.pi (fun _ : Fin m => ν)) {x | P x}).toReal =
      weightedProbability (productWeight (singletonWeight ν)) P := by
  rw [event_probability_eq_weightedProbability]
  congr 1
  funext x
  exact product_singletonWeight_eq ν m x

/-- A measurable finite quantizer turns integrals on an arbitrary probability
space into the exact singleton-weight expectation of its pushforward law. -/
theorem integral_comp_eq_weightedMean {Ω α : Type*} [MeasurableSpace Ω]
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Q : Ω → α) (hQ : Measurable Q)
    (f : α → ℝ) :
    (∫ ω, f (Q ω) ∂μ) = weightedMean (singletonWeight (μ.map Q)) f := by
  letI : IsProbabilityMeasure (μ.map Q) := Measure.isProbabilityMeasure_map hQ.aemeasurable
  rw [← integral_map hQ.aemeasurable (Integrable.of_finite.aestronglyMeasurable),
    integral_eq_weightedMean]

/-- Pulling a finite event back through a measurable quantizer preserves its
weighted probability exactly. -/
theorem event_comp_probability_eq_weightedProbability {Ω α : Type*}
    [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Q : Ω → α) (hQ : Measurable Q)
    (P : α → Prop) :
    (μ {ω | P (Q ω)}).toReal = weightedProbability (singletonWeight (μ.map Q)) P := by
  letI : IsProbabilityMeasure (μ.map Q) := Measure.isProbabilityMeasure_map hQ.aemeasurable
  have hset : MeasurableSet {a | P a} := (Set.toFinite _).measurableSet
  rw [← event_probability_eq_weightedProbability, Measure.map_apply hQ hset]
  rfl

end LeanNumDetect.FiniteWeightedLaw
