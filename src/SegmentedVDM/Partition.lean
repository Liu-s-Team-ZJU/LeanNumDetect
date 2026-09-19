import SegmentedVDM.ClumpGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SegmentedVDM.Clumps

/-- A finite partition with clumps of size at most `s` admits the slot data
used in the interpolation construction. Slots add no geometric assumption. -/
theorem exists_of_label {n s : ℕ} (label : Fin n → ℕ)
    (hsize : ∀ a, (Finset.univ.filter (fun j => label j = a)).card ≤ s) :
    ∃ C : SegmentedVDM.Clumps n s, C.label = label := by
  classical
  let S (a : ℕ) := {j : Fin n // label j = a}
  have hc (a : ℕ) : Fintype.card (S a) ≤ Fintype.card (Fin s) := by
    simpa [S, Fintype.card_subtype] using hsize a
  let e (a : ℕ) : S a ↪ Fin s :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hc a))
  let slot (j : Fin n) := e (label j) ⟨j,rfl⟩
  refine ⟨{label := label, slot := slot, injective := ?_}, rfl⟩
  intro i j h
  have hl := congrArg Prod.fst h
  have he := congrArg Prod.snd h
  change label i = label j at hl
  change e (label i) ⟨i,rfl⟩ = e (label j) ⟨j,rfl⟩ at he
  have transport (a b : ℕ) (hab : a = b) (u : Fin n) (hu : label u = a) :
      e a ⟨u,hu⟩ = e b ⟨u,hu.trans hab⟩ := by subst b; rfl
  have he' : e (label j) ⟨i,hl⟩ = e (label j) ⟨j,rfl⟩ :=
    (transport (label i) (label j) hl i rfl).symm.trans he
  exact congrArg Subtype.val ((e (label j)).injective he')

end SegmentedVDM.Clumps
