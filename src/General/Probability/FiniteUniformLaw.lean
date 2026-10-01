import General.Probability.UniformCounting
import General.Probability.FiniteAverage
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Uniform finite laws, their independent coordinate copies, and their exact
conversion to the counting averages used by finite-population sampling. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section

open scoped Classical

def finiteUniformMeasure (α : Type*) [Fintype α] [MeasurableSpace α] : Measure α :=
  (Fintype.card α : ℝ≥0∞)⁻¹ • Measure.count

instance finiteUniformMeasure_isProbability (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] : IsProbabilityMeasure (finiteUniformMeasure α) := by
  constructor
  have hc : (Fintype.card α : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simpa [finiteUniformMeasure] using ENNReal.inv_mul_cancel hc (by finiteness)

theorem integral_finiteUniformMeasure {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → ℝ) :
    ∫ a, f a ∂finiteUniformMeasure α = finiteAverage f := by
  simp [finiteUniformMeasure, integral_smul_measure, finiteAverage]

theorem finiteUniformMeasure_eq_uniformPMF {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    finiteUniformMeasure α = (PMF.uniformOfFintype α).toMeasure := by
  apply Measure.ext_of_singleton
  intro a
  rw [PMF.toMeasure_uniformOfFintype_apply {a} (measurableSet_singleton a)]
  simp [finiteUniformMeasure]

theorem probability_eq_finiteUniformMeasure {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (P : α → Prop) :
    probability P = (finiteUniformMeasure α {a | P a}).toReal := by
  rw [finiteUniformMeasure_eq_uniformPMF]
  rw [PMF.toMeasure_uniformOfFintype_apply {a | P a} (Set.toFinite _).measurableSet]
  simp [probability, ENNReal.toReal_div, Fintype.card_subtype]

theorem pi_finiteUniformMeasure {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    Measure.pi (fun _ : ι => finiteUniformMeasure α) =
      finiteUniformMeasure (ι → α) := by
  classical
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.pi_singleton]
  simp [finiteUniformMeasure, ENNReal.inv_pow]

theorem iIndepFun_finiteUniform_coordinates {ι α β : Type*} [Fintype ι]
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (f : α → β) :
    iIndepFun (fun i (ω : ι → α) => f (ω i)) (finiteUniformMeasure (ι → α)) := by
  rw [← pi_finiteUniformMeasure]
  exact iIndepFun_pi (fun _ => (measurable_of_countable f).aemeasurable)

theorem identDistrib_finiteUniform_coordinate {ι α β : Type*} [Fintype ι]
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (f : α → β) (i : ι) :
    IdentDistrib (fun ω : ι → α => f (ω i)) f
      (finiteUniformMeasure (ι → α)) (finiteUniformMeasure α) := by
  classical
  rw [← pi_finiteUniformMeasure]
  refine ⟨(measurable_of_countable _).aemeasurable,
    (measurable_of_countable _).aemeasurable, ?_⟩
  change Measure.map (f ∘ (fun ω : ι → α => ω i)) _ = _
  rw [← Measure.map_map (measurable_of_countable f) (measurable_pi_apply i)]
  rw [Measure.pi_map_eval]
  simp

end

end LeanNumDetect.FiniteMatrixSampling
