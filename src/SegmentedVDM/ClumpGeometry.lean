import SegmentedVDM.Localization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SegmentedVDM

/-- A partition together with an injective enumeration inside each clump.
The parameter `s` is an upper bound on clump cardinalities. -/
structure Clumps (n s : ℕ) where
  label : Fin n → ℕ
  slot : Fin n → Fin s
  injective : Function.Injective (fun j => (label j, slot j))

namespace Clumps
variable {n s : ℕ} (C : Clumps n s)

def colorClass (k : Fin n) (ℓ : Fin s) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j = k ∨ (C.label j ≠ C.label k ∧ C.slot j = ℓ))

@[simp] theorem mem_colorClass (k j : Fin n) (ℓ : Fin s) :
    j ∈ C.colorClass k ℓ ↔ j = k ∨ (C.label j ≠ C.label k ∧ C.slot j = ℓ) := by
  simp [colorClass]

theorem anchor_mem_colorClass (k : Fin n) (ℓ : Fin s) : k ∈ C.colorClass k ℓ := by simp

theorem colorClass_labels_ne (k : Fin n) (ℓ : Fin s)
    (i j : C.colorClass k ℓ) (hij : i ≠ j) : C.label i ≠ C.label j := by
  intro h
  have hi := (C.mem_colorClass k i ℓ).mp i.property
  have hj := (C.mem_colorClass k j ℓ).mp j.property
  apply hij
  apply Subtype.ext
  rcases hi with hi | ⟨hi, hsi⟩ <;> rcases hj with hj | ⟨hj, hsj⟩
  · exact hi.trans hj.symm
  · exact False.elim (hj (by simpa [hi] using h.symm))
  · exact False.elim (hi (by simpa [hj] using h))
  · exact C.injective (Prod.ext h (hsi.trans hsj.symm))

def neighbors (k : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ≠ k ∧ C.label j = C.label k)

@[simp] theorem mem_neighbors (k j : Fin n) :
    j ∈ C.neighbors k ↔ j ≠ k ∧ C.label j = C.label k := by simp [neighbors]

theorem neighbors_card (k : Fin n) : (C.neighbors k).card ≤ s-1 := by
  have hh : (C.neighbors k).card ≤ (Finset.univ.erase (C.slot k)).card := by
    apply Finset.card_le_card_of_injOn C.slot
    · intro j hj
      have h := (C.mem_neighbors k j).mp hj
      change C.slot j ∈ Finset.univ.erase (C.slot k)
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro he
      exact h.1 (C.injective (Prod.ext h.2 he))
    · intro i hi j hj he
      have hi' := (C.mem_neighbors k i).mp hi
      have hj' := (C.mem_neighbors k j).mp hj
      exact C.injective (Prod.ext (hi'.2.trans hj'.2.symm) he)
  simpa using hh

end Clumps
end SegmentedVDM
