import General.Probability.FiniteMatrixSampling
import Mathlib.Probability.Distributions.Uniform

/-!
The finite counting probabilities used in matrix sampling are exactly the
probabilities of the uniform PMF.  For samples of a prescribed cardinality,
this gives the uniform law on all subsets of that cardinality.
-/

set_option autoImplicit false

namespace LeanNumDetect.FiniteMatrixSampling

/-- The real counting ratio agrees with the uniform PMF on every event. -/
theorem probability_eq_uniform_toOuterMeasure {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) :
    probability P = ((PMF.uniformOfFintype α).toOuterMeasure {x | P x}).toReal := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp [probability, ENNReal.toReal_div, Fintype.card_subtype]

/-- Uniform sampling without replacement means the uniform law on the finite
set of all `m`-element subsets, with no ordering of the sampled objects. -/
theorem sample_probability_eq_uniform_toOuterMeasure {N m : ℕ} (hm : m ≤ N)
    (P : Sample N m → Prop) :
    letI : Nonempty (Sample N m) := sample_nonempty hm
    probability P = ((PMF.uniformOfFintype (Sample N m)).toOuterMeasure {Ω | P Ω}).toReal := by
  letI : Nonempty (Sample N m) := sample_nonempty hm
  exact probability_eq_uniform_toOuterMeasure P

end LeanNumDetect.FiniteMatrixSampling
