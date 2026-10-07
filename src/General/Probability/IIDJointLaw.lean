import Mathlib.Probability.IdentDistribIndep

/-! Transport of independent identically distributed tuples to their exact
product law, on arbitrary probability spaces. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
universe u v w
namespace LeanNumDetect.IIDJointLaw

/-- The sampled tuple has the product of the reference row distribution. -/
theorem iid_tuple_map_eq_pi {ι : Type*} [Fintype ι]
    {Ω : Type u} {Ω' : Type v} {α : Type w}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
    (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → α) (rows : ι → Ω' → α)
    (hindep : iIndepFun rows ν) (hcopy : ∀ i, IdentDistrib (rows i) X ν μ) :
    ν.map (fun ω i => rows i ω) = Measure.pi (fun _ : ι => μ.map X) := by
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (hcopy i).aemeasurable_fst) hindep]
  congr 1
  funext i
  exact (hcopy i).map_eq

/-- Any measurable event of the sampled tuple has its exact product-law
probability. No finite population or atomic distribution is assumed. -/
theorem iid_tuple_event_measure_eq {ι : Type*} [Fintype ι]
    {Ω : Type u} {Ω' : Type v} {α : Type w}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
    (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → α) (rows : ι → Ω' → α)
    (hindep : iIndepFun rows ν) (hcopy : ∀ i, IdentDistrib (rows i) X ν μ)
    (S : Set (ι → α)) (hS : MeasurableSet S) :
    ν {ω | (fun i => rows i ω) ∈ S} = (Measure.pi (fun _ : ι => μ.map X)) S := by
  rw [← iid_tuple_map_eq_pi μ ν X rows hindep hcopy,
    Measure.map_apply_of_aemeasurable
      (aemeasurable_pi_lambda _ fun i => (hcopy i).aemeasurable_fst) hS]
  rfl

end LeanNumDetect.IIDJointLaw
