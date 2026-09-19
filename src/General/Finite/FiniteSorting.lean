import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
set_option autoImplicit false
namespace LeanNumDetect

theorem exists_strictMono_reordering {q : ℕ} (t : Fin q → ℝ)
    (ht : Function.Injective t) :
    ∃ e : Equiv.Perm (Fin q), StrictMono (fun j => t (e j)) := by
  classical
  let S := Finset.univ.image t
  have hc : S.card = q := by simp [S, Finset.card_image_of_injective _ ht]
  let f : Fin q → S := fun j => ⟨t j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact ht (congrArg Subtype.val hij)
    · intro y
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp y.property
      exact ⟨j, Subtype.ext he⟩
  let e := Equiv.ofBijective f hf
  let o := S.orderIsoOfFin hc
  let σ := o.toEquiv.trans e.symm
  refine ⟨σ, ?_⟩
  have he : ∀ j, t (σ j) = (o j : ℝ) := by
    intro j
    exact congrArg Subtype.val (e.apply_symm_apply (o j))
  simp only [he]
  exact o.strictMono
end LeanNumDetect
