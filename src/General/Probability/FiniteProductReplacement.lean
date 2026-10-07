import General.Probability.FiniteEntropy
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Exchangeability of one-coordinate replacements under a finite weighted
independent product law. Zero population weights are permitted. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteEntropy

def replacementSwap {α : Type*} {m : ℕ} (i : Fin m)
    (p : (Fin m → α) × α) : (Fin m → α) × α :=
  (Function.update p.1 i p.2, p.1 i)

theorem replacementSwap_involutive {α : Type*} {m : ℕ} (i : Fin m) :
    Function.Involutive (replacementSwap (α := α) i) := by
  rintro ⟨x, y⟩
  apply Prod.ext
  · funext k
    by_cases hk : k = i
    · subst k
      simp [replacementSwap]
    · simp [replacementSwap]
  · simp [replacementSwap]

def replacementEquiv {α : Type*} {m : ℕ} (i : Fin m) :
    ((Fin m → α) × α) ≃ ((Fin m → α) × α) where
  toFun := replacementSwap i
  invFun := replacementSwap i
  left_inv := replacementSwap_involutive i
  right_inv := replacementSwap_involutive i

theorem replacement_weight_identity {α : Type*} (q : α → ℝ) {m : ℕ}
    (x : Fin m → α) (i : Fin m) (y : α) :
    productWeight q (Function.update x i y) * q (x i) = productWeight q x * q y := by
  have hupdate : (fun k => q (Function.update x i y k)) =
      Function.update (fun k => q (x k)) i (q y) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk]
  unfold productWeight
  rw [hupdate, Finset.prod_update_of_mem (Finset.mem_univ i)]
  have horig := Finset.prod_erase_mul Finset.univ (fun k => q (x k)) (Finset.mem_univ i)
  rw [← horig]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

/-- The original coordinate and its independent replacement can be exchanged
inside any weighted product expectation. -/
theorem weightedMean_replacement_exchange {α : Type*} [Fintype α]
    (q : α → ℝ) {m : ℕ} (i : Fin m) (g : (Fin m → α) → α → ℝ) :
    weightedMean (productWeight q) (fun x => weightedMean q (g x)) =
      weightedMean (productWeight q) (fun x => weightedMean q
        (fun y => g (Function.update x i y) (x i))) := by
  let e := replacementEquiv (α := α) i
  let F := fun p : (Fin m → α) × α => productWeight q p.1 * q p.2 * g p.1 p.2
  have hreindex := e.sum_comp F
  have hleft : (∑ p, F p) =
      weightedMean (productWeight q) (fun x => weightedMean q (g x)) := by
    simp only [F, weightedMean, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
  have hright : (∑ p, F (e p)) =
      weightedMean (productWeight q) (fun x => weightedMean q
        (fun y => g (Function.update x i y) (x i))) := by
    simp only [F, e, replacementEquiv, Equiv.coe_fn_mk,
      replacementSwap, Fintype.sum_prod_type, weightedMean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [replacement_weight_identity]
    ring
  rw [hleft, hright] at hreindex
  exact hreindex.symm

/-- Refreshing any one coordinate preserves the product law. -/
theorem weightedMean_coordinate_refresh {α : Type*} [Fintype α]
    (q : α → ℝ) (hqs : ∑ a, q a = 1) {m : ℕ} (i : Fin m)
    (g : (Fin m → α) → ℝ) :
    weightedMean (productWeight q) (fun x => weightedMean q
      (fun y => g (Function.update x i y))) = weightedMean (productWeight q) g := by
  rw [weightedMean_replacement_exchange q i]
  have hrestore (x : Fin m → α) (y : α) :
      Function.update (Function.update x i y) i (x i) = x := by
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk]
  simp only [hrestore]
  simp only [weightedMean_const q hqs]

end LeanNumDetect.FiniteEntropy
