import MultiTuran.Preliminaries.Geometry

/-!
# Torus distinctness and positive minimum separation

For a finite node family with at least two nodes, positivity of the minimum
separation is exactly pairwise distinctness on the angular torus.  It does not
impose any positive numerical separation scale.
-/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

/-- A finite torus-distinct family has strictly positive minimum separation.
The statement provides no additional quantitative separation hypothesis. -/
theorem nodeSeparation_pos_of_pairwise_torusDistance_pos
    {d n : ℕ} (Y : Fin n → Point d) (hn : 2 ≤ n)
    (hpair : ∀ i j, i ≠ j → 0 < torusLInfDistance (Y i) (Y j)) :
    0 < nodeSeparation Y := by
  let S := {a : ℝ | ∃ i j : Fin n, i ≠ j ∧ a = torusLInfDistance (Y i) (Y j)}
  have hS : S.Finite := by
    apply (Set.finite_range (fun ij : Fin n × Fin n =>
      torusLInfDistance (Y ij.1) (Y ij.2))).subset
    rintro a ⟨i, j, _, rfl⟩
    exact ⟨(i, j), rfl⟩
  have hne : S.Nonempty := by
    refine ⟨_, ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, rfl⟩⟩
    intro h
    exact Nat.zero_ne_one (by simpa only [Fin.mk.injEq] using h)
  obtain ⟨i, j, hij, hmin⟩ := hne.csInf_mem hS
  change nodeSeparation Y = torusLInfDistance (Y i) (Y j) at hmin
  rw [hmin]
  exact hpair i j hij

/-- Positive minimum separation implies pairwise torus distinctness. -/
theorem pairwise_torusDistance_pos_of_nodeSeparation_pos
    {d n : ℕ} (Y : Fin n → Point d) (hsep : 0 < nodeSeparation Y) :
    ∀ i j, i ≠ j → 0 < torusLInfDistance (Y i) (Y j) := by
  intro i j hij
  exact hsep.trans_le (nodeSeparation_le_pair Y i j hij)

/-- Exact equivalence between the original finite torus-distinctness premise
and the positivity premise used by the explicit multi-clump lower bound. -/
theorem nodeSeparation_pos_iff_pairwise_torusDistance_pos
    {d n : ℕ} (Y : Fin n → Point d) (hn : 2 ≤ n) :
    0 < nodeSeparation Y ↔ ∀ i j, i ≠ j → 0 < torusLInfDistance (Y i) (Y j) :=
  ⟨pairwise_torusDistance_pos_of_nodeSeparation_pos Y,
    nodeSeparation_pos_of_pairwise_torusDistance_pos Y hn⟩


/-- The actual largest clump cardinality of a finite labeling.  Empty labels
are harmless and do not require an additional surjectivity hypothesis. -/
def largestClumpSize {n A : ℕ} (label : Fin n → Fin A) : ℕ :=
  Finset.univ.sup fun a : Fin A => (Finset.univ.filter fun j => label j = a).card

theorem clumpFiber_card_le_largestClumpSize {n A : ℕ}
    (label : Fin n → Fin A) (a : Fin A) :
    (Finset.univ.filter fun j => label j = a).card ≤ largestClumpSize label := by
  unfold largestClumpSize
  exact Finset.le_sup (f := fun a : Fin A =>
    (Finset.univ.filter fun j : Fin n => label j = a).card) (Finset.mem_univ a)

theorem largestClumpSize_le_sourceCount {n A : ℕ} (label : Fin n → Fin A) :
    largestClumpSize label ≤ n := by
  unfold largestClumpSize
  apply Finset.sup_le
  intro a _
  have h := Finset.card_le_card (Finset.filter_subset
    (s := (Finset.univ : Finset (Fin n))) (p := fun j => label j = a))
  simpa only [Finset.card_univ, Fintype.card_fin] using h

theorem largestClumpSize_pos {n A : ℕ} (label : Fin n → Fin A) (hn : 0 < n) :
    0 < largestClumpSize label := by
  let j : Fin n := ⟨0, hn⟩
  have hmem : j ∈ Finset.univ.filter (fun i => label i = label j) := by simp
  have hcard : 0 < (Finset.univ.filter fun i => label i = label j).card :=
    Finset.card_pos.mpr ⟨j, hmem⟩
  exact hcard.trans_le (clumpFiber_card_le_largestClumpSize label (label j))

/-- A largest nonempty clump exists whenever the node family is nonempty. -/
theorem exists_clumpFiber_card_eq_largestClumpSize {n A : ℕ}
    (label : Fin n → Fin A) (hn : 0 < n) :
    ∃ a : Fin A, (Finset.univ.filter fun j => label j = a).card = largestClumpSize label := by
  have hne : (Finset.univ : Finset (Fin A)).Nonempty :=
    ⟨label ⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup Finset.univ hne
    (fun a : Fin A => (Finset.univ.filter fun j => label j = a).card)
  exact ⟨a, ha.symm⟩

end
end LeanNumDetect.MultiTuran.MultiClump
