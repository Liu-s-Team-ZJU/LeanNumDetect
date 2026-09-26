import General.Probability.MatrixChernoffBounds
import General.Probability.UniformCounting

/-!
Uniform sampling from a population indexed by an arbitrary finite type.
The sample outcomes are the actual subsets of that type. Reindexing the
population and its subsets preserves both the matrix sums and their uniform
probabilities, so the original matrix-Chernoff bounds need no new admission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ComplexOrder

namespace LeanNumDetect.FiniteMatrixSampling

/-- Uniform sampling without replacement from an arbitrary labelled population. -/
abbrev FiniteSample (κ : Type*) (m : ℕ) := {Ω : Finset κ // Ω.card = m}

/-- The mean of a finite matrix population. -/
noncomputable def finiteMean {κ : Type*} [Fintype κ] {d : ℕ}
    (X : κ → Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ((Fintype.card κ : ℂ)⁻¹) • ∑ k, X k

/-- The matrix sum over the actual sampled subset of the population. -/
noncomputable def finiteSampleSum {κ : Type*} {d m : ℕ}
    (X : κ → Matrix (Fin d) (Fin d) ℂ) (Ω : FiniteSample κ m) :
    Matrix (Fin d) (Fin d) ℂ := ∑ k ∈ Ω.val, X k

/-- The empirical mean over the actual sampled subset. -/
noncomputable def finiteSampleMean {κ : Type*} {d m : ℕ}
    (X : κ → Matrix (Fin d) (Fin d) ℂ) (Ω : FiniteSample κ m) :
    Matrix (Fin d) (Fin d) ℂ := ((m : ℂ)⁻¹) • finiteSampleSum X Ω

/-- A population bijection induces a bijection of subsets of each fixed size. -/
def finiteSampleEquiv {κ ι : Type*} (e : κ ≃ ι) (m : ℕ) :
    FiniteSample κ m ≃ FiniteSample ι m :=
  e.finsetCongr.subtypeEquiv (by intro Ω; simp [Equiv.finsetCongr_apply])

@[simp] theorem finiteSampleEquiv_val {κ ι : Type*} (e : κ ≃ ι) (m : ℕ)
    (Ω : FiniteSample κ m) :
    (finiteSampleEquiv e m Ω).val = Ω.val.map e.toEmbedding := rfl

/-- Uniform counting probabilities are invariant under a relabelling of outcomes. -/
theorem probability_comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : β → Prop) :
    probability (fun x => P (e x)) = probability P := by
  classical
  have hcard : Fintype.card {x : α // P (e x)} = Fintype.card {y : β // P y} :=
    Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))
  unfold probability
  rw [Fintype.card_congr e]
  congr 1
  exact_mod_cast (by simpa only [Fintype.card_subtype] using hcard)

/-- Relabelling an arbitrary finite population preserves its mean. -/
theorem finiteMean_comp_equiv {κ ι : Type*} [Fintype κ] [Fintype ι]
    (e : κ ≃ ι) {d : ℕ} (X : ι → Matrix (Fin d) (Fin d) ℂ) :
    finiteMean (fun k => X (e k)) = finiteMean X := by
  unfold finiteMean
  rw [Fintype.card_congr e, e.sum_comp X]

/-- Relabelling a subset preserves the sum of the sampled matrices. -/
theorem finiteSampleSum_comp_equiv {κ ι : Type*} (e : κ ≃ ι) {d m : ℕ}
    (X : ι → Matrix (Fin d) (Fin d) ℂ) (Ω : FiniteSample κ m) :
    finiteSampleSum (fun k => X (e k)) Ω =
      finiteSampleSum X (finiteSampleEquiv e m Ω) := by
  simp [finiteSampleSum]

/-- Relabelling a subset preserves the empirical mean. -/
theorem finiteSampleMean_comp_equiv {κ ι : Type*} (e : κ ≃ ι) {d m : ℕ}
    (X : ι → Matrix (Fin d) (Fin d) ℂ) (Ω : FiniteSample κ m) :
    finiteSampleMean (fun k => X (e k)) Ω =
      finiteSampleMean X (finiteSampleEquiv e m Ω) := by
  simp only [finiteSampleMean, finiteSampleSum_comp_equiv]

@[simp] theorem finiteMean_fin {N d : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) : finiteMean X = mean X := by
  simp only [finiteMean, mean, Fintype.card_fin]

@[simp] theorem finiteSampleMean_fin {N d m : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) (Ω : Sample N m) :
    finiteSampleMean X Ω = sampleMean X Ω := rfl

/-- A subset of any admissible size exists in every finite population. -/
theorem finiteSample_nonempty {κ : Type*} [Fintype κ] {m : ℕ}
    (hm : m ≤ Fintype.card κ) : Nonempty (FiniteSample κ m) := by
  classical
  obtain ⟨Ω, _, hΩ⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset κ)) (by simpa using hm)
  exact ⟨⟨Ω, hΩ⟩⟩

/-- The counting probability is literally the uniform PMF on subsets of the
original population, independently of the enumeration used in a proof. -/
theorem finiteSample_probability_eq_uniform_toOuterMeasure {κ : Type*}
    [Fintype κ] [DecidableEq κ] {m : ℕ} (hm : m ≤ Fintype.card κ)
    (P : FiniteSample κ m → Prop) :
    letI : Nonempty (FiniteSample κ m) := finiteSample_nonempty hm
    probability P =
      ((PMF.uniformOfFintype (FiniteSample κ m)).toOuterMeasure {Ω | P Ω}).toReal := by
  letI : Nonempty (FiniteSample κ m) := finiteSample_nonempty hm
  exact probability_eq_uniform_toOuterMeasure P

/-- The existing Chernoff estimate transferred to actual subsets of an
arbitrary finite population. All hypotheses and constants are preserved. -/
theorem finiteSampleMean_bounds_probability {κ : Type*} [Fintype κ] [DecidableEq κ]
    {d m : ℕ} (hκ : 0 < Fintype.card κ) (hd : 0 < d)
    (hm : 1 ≤ m) (hmκ : m ≤ Fintype.card κ)
    (X : κ → Matrix (Fin d) (Fin d) ℂ) {R a b δ : ℝ}
    (hR : 0 < R) (ha : 0 < a) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hX : ∀ k, (X k).PosSemidef)
    (hbound : ∀ k (x : EuclideanSpace ℂ (Fin d)),
      quadratic (X k) x ≤ R * ‖x‖ ^ 2)
    (hmean : ∀ x : EuclideanSpace ℂ (Fin d),
      a * ‖x‖ ^ 2 ≤ quadratic (finiteMean X) x ∧
      quadratic (finiteMean X) x ≤ b * ‖x‖ ^ 2) :
    1 - ((d : ℝ) * Real.exp (-((m : ℝ) * a * δ ^ 2) / (2 * R)) +
      (d : ℝ) * Real.exp (-((m : ℝ) * a * δ ^ 2) / (3 * R))) ≤
    probability (fun Ω : FiniteSample κ m => ∀ x : EuclideanSpace ℂ (Fin d),
      (1 - δ) * a * ‖x‖ ^ 2 ≤ quadratic (finiteSampleMean X Ω) x ∧
      quadratic (finiteSampleMean X Ω) x ≤ (1 + δ) * b * ‖x‖ ^ 2) := by
  classical
  let e := (Fintype.equivFin κ).symm
  have hMean : mean (fun k => X (e k)) = finiteMean X := by
    rw [← finiteMean_fin, finiteMean_comp_equiv e X]
  have h := sampleMean_bounds_probability hκ hd hm hmκ (fun k => X (e k))
    hR ha hδ0 hδ1 (fun k => hX (e k)) (fun k => hbound (e k)) (by
      simpa only [hMean] using hmean)
  have hSample (Ω : Sample (Fintype.card κ) m) :
      sampleMean (fun k => X (e k)) Ω =
        finiteSampleMean X (finiteSampleEquiv e m Ω) :=
    finiteSampleMean_comp_equiv e X Ω
  let P : FiniteSample κ m → Prop := fun Ω => ∀ x : EuclideanSpace ℂ (Fin d),
    (1 - δ) * a * ‖x‖ ^ 2 ≤ quadratic (finiteSampleMean X Ω) x ∧
    quadratic (finiteSampleMean X Ω) x ≤ (1 + δ) * b * ‖x‖ ^ 2
  have hprob := probability_comp_equiv (finiteSampleEquiv e m) P
  change _ ≤ probability P
  rw [← hprob]
  simpa only [P, hSample] using h

end LeanNumDetect.FiniteMatrixSampling
