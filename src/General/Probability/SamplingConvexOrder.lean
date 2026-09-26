import General.Probability.FiniteAverage
import General.Probability.FiniteMatrixSampling
import Mathlib.GroupTheory.Perm.Finite

/-!
The finite-population convex comparison of Hoeffding and Gross--Nesme.
The proof uses permutation symmetrization and finite Jensen: the population
has arbitrary vector values, and the only condition on the test function is
convexity. In particular no matrix concentration theorem is imported here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Equiv

namespace LeanNumDetect.FiniteMatrixSampling

/-- Averaging a transitive finite family of permutations gives the uniform
average on its orbit, without any fiber-cardinality computation. -/
theorem finiteAverage_transitive_action {G A E : Type*} [Group G] [Fintype G]
    [Fintype A] [Nonempty A] [AddCommGroup E] [Module ℝ E]
    (ρ : G → Equiv.Perm A)
    (hmul : ∀ g h a, ρ (g * h) a = ρ g (ρ h a))
    (htrans : ∀ a b, ∃ g, ρ g a = b) (f : A → E) (a : A) :
    finiteAverage (fun g => f (ρ g a)) = finiteAverage f := by
  let q : A → E := fun x => finiteAverage (fun g => f (ρ g x))
  have hq (x y : A) : q x = q y := by
    obtain ⟨g, rfl⟩ := htrans x y
    dsimp [q]
    symm
    calc
      finiteAverage (fun h => f (ρ h (ρ g x))) =
          finiteAverage (fun h => f (ρ (h * g) x)) :=
        finiteAverage_congr (fun h => congrArg f (hmul h g x).symm)
      _ = finiteAverage (fun h => f (ρ h x)) :=
        finiteAverage_comp_equiv (Equiv.mulRight g) (fun h => f (ρ h x))
  calc
    finiteAverage (fun g => f (ρ g a)) = finiteAverage (fun _ : A => q a) := by
      rw [finiteAverage_const]
    _ = finiteAverage q := finiteAverage_congr (fun b => hq a b)
    _ = finiteAverage (fun g => finiteAverage (fun b => f (ρ g b))) :=
      finiteAverage_comm (fun b g => f (ρ g b))
    _ = finiteAverage (fun _ : G => finiteAverage f) :=
      finiteAverage_congr (fun g => finiteAverage_comp_equiv (ρ g) f)
    _ = finiteAverage f := finiteAverage_const _

/-- A uniformly random permutation sends a fixed index to a uniform index. -/
theorem finiteAverage_perm_apply {A E : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    [AddCommGroup E] [Module ℝ E] (f : A → E) (a : A) :
    finiteAverage (fun σ : Equiv.Perm A => f (σ a)) = finiteAverage f := by
  classical
  exact finiteAverage_transitive_action (fun σ : Equiv.Perm A => σ)
    (fun _ _ _ => rfl) (fun a b => ⟨Equiv.swap a b, by simp⟩) f a

/-- A permutation of the population acts bijectively on subsets of a given size. -/
def samplePermutation {N : ℕ} (σ : Equiv.Perm (Fin N)) (m : ℕ) :
    Sample N m ≃ Sample N m :=
  σ.finsetCongr.subtypeEquiv (by intro Ω; simp [Equiv.finsetCongr_apply])

@[simp] theorem samplePermutation_val {N m : ℕ} (σ : Equiv.Perm (Fin N))
    (Ω : Sample N m) : (samplePermutation σ m Ω).val = Ω.val.map σ.toEmbedding := rfl

theorem samplePermutation_mul {N m : ℕ} (σ τ : Equiv.Perm (Fin N)) (Ω : Sample N m) :
    samplePermutation (σ * τ) m Ω = samplePermutation σ m (samplePermutation τ m Ω) := by
  apply Subtype.ext
  change Ω.val.map (σ * τ).toEmbedding = (Ω.val.map τ.toEmbedding).map σ.toEmbedding
  rw [Finset.map_map]
  congr 1

theorem samplePermutation_transitive {N m : ℕ} (Ω Ξ : Sample N m) :
    ∃ σ : Equiv.Perm (Fin N), samplePermutation σ m Ω = Ξ := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq Ω.val Ξ.val
    (Ω.property.trans Ξ.property.symm)
  exact ⟨σ, Subtype.ext hσ⟩

/-- Randomly permuting a fixed subset gives the uniform law on all subsets
of the same size. -/
theorem finiteAverage_samplePermutation {N m : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℝ E] (f : Sample N m → E) (Ω : Sample N m) :
    finiteAverage (fun σ : Equiv.Perm (Fin N) => f (samplePermutation σ m Ω)) =
      finiteAverage f := by
  letI : Nonempty (Sample N m) := ⟨Ω⟩
  exact finiteAverage_transitive_action (fun σ => samplePermutation σ m)
    samplePermutation_mul samplePermutation_transitive f Ω

/-- Conditional Jensen: any tuple contained in an `m`-element set has, after
uniformly permuting that set, barycenter equal to the sum of the set. -/
theorem convex_subset_sum_le_permutationAverage {N m : ℕ} (hm : 0 < m)
    {E : Type*} [AddCommGroup E] [Module ℝ E] (X : Fin N → E)
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (Ω : Sample N m)
    (ω : Fin m → Fin N) (hω : ∀ i, ω i ∈ Ω.val) :
    f (∑ k ∈ Ω.val, X k) ≤
      finiteAverage (fun σ : Equiv.Perm Ω.val =>
        f (∑ i, X (σ ⟨ω i, hω i⟩))) := by
  classical
  have hc : Fintype.card Ω.val = m := by simpa using Ω.property
  letI : Nonempty Ω.val := Fintype.card_pos_iff.mp (by simpa only [hc] using hm)
  have hbar : finiteAverage (fun σ : Equiv.Perm Ω.val =>
      ∑ i, X (σ ⟨ω i, hω i⟩)) = ∑ k ∈ Ω.val, X k := by
    rw [finiteAverage_sum]
    have hindex (i : Fin m) :
        finiteAverage (fun σ : Equiv.Perm Ω.val => X (σ ⟨ω i, hω i⟩)) =
          finiteAverage (fun k : Ω.val => X k) :=
      finiteAverage_perm_apply (fun k : Ω.val => X k) ⟨ω i, hω i⟩
    simp_rw [hindex]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ]
    unfold finiteAverage
    rw [hc, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hm.ne'), one_smul]
    exact Finset.sum_coe_sort Ω.val X
  have h := convex_finiteAverage_le hf
    (fun σ : Equiv.Perm Ω.val => ∑ i, X (σ ⟨ω i, hω i⟩))
  rwa [hbar] at h

/-- Every tuple has at least as large a permutation-averaged convex image as
a uniformly sampled subset. Repeated coordinates in the tuple are allowed. -/
theorem subsetAverage_le_permuted_tupleAverage {N m : ℕ}
    (hm : 0 < m) (hmN : m ≤ N) {E : Type*} [AddCommGroup E] [Module ℝ E]
    (X : Fin N → E) {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (ω : Fin m → Fin N) :
    finiteAverage (fun Ω : Sample N m => f (∑ k ∈ Ω.val, X k)) ≤
      finiteAverage (fun π : Equiv.Perm (Fin N) => f (∑ i, X (π (ω i)))) := by
  classical
  obtain ⟨S, hcover, _, hS⟩ := Finset.exists_subsuperset_card_eq
    (s := Finset.univ.image ω) (t := (Finset.univ : Finset (Fin N)))
    (Finset.subset_univ _) (by simpa using Finset.card_image_le (s := Finset.univ) (f := ω))
    (by simpa using hmN)
  let Ω : Sample N m := ⟨S, hS⟩
  have hω (i : Fin m) : ω i ∈ Ω.val := hcover (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  have hJ := finiteAverage_mono (fun π : Equiv.Perm (Fin N) =>
    convex_subset_sum_le_permutationAverage hm (fun k => X (π k)) hf Ω ω hω)
  have hleft : finiteAverage (fun π : Equiv.Perm (Fin N) => f (∑ k ∈ Ω.val, X (π k))) =
      finiteAverage (fun Ξ : Sample N m => f (∑ k ∈ Ξ.val, X k)) := by
    simpa only [samplePermutation_val, Finset.sum_map, Equiv.coe_toEmbedding] using
      finiteAverage_samplePermutation (fun Ξ : Sample N m => f (∑ k ∈ Ξ.val, X k)) Ω
  have hright : finiteAverage (fun π : Equiv.Perm (Fin N) =>
      finiteAverage (fun σ : Equiv.Perm Ω.val => f (∑ i, X (π (σ ⟨ω i, hω i⟩))))) =
      finiteAverage (fun π : Equiv.Perm (Fin N) => f (∑ i, X (π (ω i)))) := by
    rw [finiteAverage_comm]
    have hinner (σ : Equiv.Perm Ω.val) :
        finiteAverage (fun π : Equiv.Perm (Fin N) => f (∑ i, X (π (σ ⟨ω i, hω i⟩)))) =
        finiteAverage (fun π : Equiv.Perm (Fin N) => f (∑ i, X (π (ω i)))) := by
      let τ : Equiv.Perm (Fin N) := σ.extendDomain (Equiv.refl Ω.val)
      have hext (i : Fin m) : τ (ω i) = (σ ⟨ω i, hω i⟩ : Fin N) := by
        simpa [τ] using Equiv.Perm.extendDomain_apply_subtype σ (Equiv.refl Ω.val) (hω i)
      have hshift := finiteAverage_comp_equiv (Equiv.mulRight τ)
        (fun π : Equiv.Perm (Fin N) => f (∑ i, X (π (ω i))))
      change finiteAverage (fun π : Equiv.Perm (Fin N) => f (∑ i, X (π (τ (ω i))))) = _ at hshift
      simpa only [hext] using hshift
    calc
      _ = finiteAverage (fun _ : Equiv.Perm Ω.val =>
            finiteAverage (fun π : Equiv.Perm (Fin N) => f (∑ i, X (π (ω i))))) :=
        finiteAverage_congr hinner
      _ = _ := finiteAverage_const _
  rwa [hleft, hright] at hJ

/-- **Hoeffding--Gross--Nesme convex comparison**, including the empty sample.
For a finite population in a real vector space, a uniform sample without
replacement has no larger expected convex function of its sum than an iid
uniform sample of the same size. The outcomes on the left are actual subsets.

Source: Gross and Nesme, arXiv:1001.2738v2, Section D, page 3. The comparison
is proved here by finite Jensen and permutation averaging, with no admission. -/
theorem sampling_withoutReplacement_convex_le {N m : ℕ} (hmN : m ≤ N)
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (X : Fin N → E) {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    finiteAverage (fun Ω : Sample N m => f (∑ k ∈ Ω.val, X k)) ≤
      finiteAverage (fun ω : Fin m → Fin N => f (∑ i, X (ω i))) := by
  classical
  letI : Nonempty (Sample N m) := sample_nonempty hmN
  by_cases hm0 : m = 0
  · subst m
    letI : Nonempty (Fin 0 → Fin N) := ⟨Fin.elim0⟩
    have hleft : finiteAverage (fun Ω : Sample N 0 => f (∑ k ∈ Ω.val, X k)) = f 0 := by
      calc
        _ = finiteAverage (fun _ : Sample N 0 => f 0) := finiteAverage_congr (fun Ω => by
          rw [Finset.card_eq_zero.mp Ω.property]
          simp)
        _ = f 0 := finiteAverage_const _
    have hright : finiteAverage (fun ω : Fin 0 → Fin N => f (∑ i, X (ω i))) = f 0 := by
      simp
    rw [hleft, hright]
  have hm : 0 < m := Nat.pos_of_ne_zero hm0
  letI : Nonempty (Fin N) := ⟨⟨0, lt_of_lt_of_le hm hmN⟩⟩
  have h := finiteAverage_mono (fun ω : Fin m → Fin N =>
    subsetAverage_le_permuted_tupleAverage hm hmN X hf ω)
  rw [finiteAverage_const, finiteAverage_comm] at h
  have hperm (π : Equiv.Perm (Fin N)) :
      finiteAverage (fun ω : Fin m → Fin N => f (∑ i, X (π (ω i)))) =
        finiteAverage (fun ω : Fin m → Fin N => f (∑ i, X (ω i))) := by
    exact finiteAverage_comp_equiv (Equiv.piCongrRight (fun _ : Fin m => π))
      (fun ω : Fin m → Fin N => f (∑ i, X (ω i)))
  simpa only [hperm, finiteAverage_const] using h

end LeanNumDetect.FiniteMatrixSampling
