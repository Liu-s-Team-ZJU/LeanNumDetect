import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic

/-! Uniform averages of vectors over finite sets, with reindexing and Jensen. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

/-- Uniform finite average, also for vector-valued functions. -/
noncomputable def finiteAverage {α E : Type*} [Fintype α] [AddCommGroup E]
    [Module ℝ E] (g : α → E) : E :=
  (Fintype.card α : ℝ)⁻¹ • ∑ a, g a

@[simp] theorem finiteAverage_const {α E : Type*} [Fintype α] [Nonempty α]
    [AddCommGroup E] [Module ℝ E] (x : E) :
    finiteAverage (fun _ : α => x) = x := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteAverage, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem finiteAverage_congr {α E : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E]
    {f g : α → E} (h : ∀ a, f a = g a) : finiteAverage f = finiteAverage g := by
  congr 1
  exact funext h

/-- Relabelling the finite sample space leaves its uniform average unchanged. -/
theorem finiteAverage_comp_equiv {α β E : Type*} [Fintype α] [Fintype β]
    [AddCommGroup E] [Module ℝ E] (e : α ≃ β) (g : β → E) :
    finiteAverage (fun a => g (e a)) = finiteAverage g := by
  unfold finiteAverage
  rw [Fintype.card_congr e, e.sum_comp g]

theorem finiteAverage_sum {α ι E : Type*} [Fintype α] [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (g : α → ι → E) :
    finiteAverage (fun a => ∑ i, g a i) = ∑ i, finiteAverage (fun a => g a i) := by
  unfold finiteAverage
  rw [Finset.sum_comm, Finset.smul_sum]

theorem finiteAverage_smul {α E : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E]
    (r : ℝ) (g : α → E) :
    finiteAverage (fun a => r • g a) = r • finiteAverage g := by
  simp only [finiteAverage, ← Finset.smul_sum, smul_smul]
  rw [mul_comm]

theorem finiteAverage_comm {α β E : Type*} [Fintype α] [Fintype β]
    [AddCommGroup E] [Module ℝ E] (g : α → β → E) :
    finiteAverage (fun a => finiteAverage (g a)) =
      finiteAverage (fun b => finiteAverage (fun a => g a b)) := by
  simp only [finiteAverage, ← Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, mul_comm]

/-- Uniform averaging on a product is iterated uniform averaging. -/
theorem finiteAverage_prod {α β E : Type*} [Fintype α] [Fintype β]
    [AddCommGroup E] [Module ℝ E] (g : α → β → E) :
    finiteAverage (fun p : α × β => g p.1 p.2) =
      finiteAverage (fun a => finiteAverage (g a)) := by
  simp only [finiteAverage, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.smul_sum, smul_smul]
  rw [mul_comm]

theorem finiteAverage_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : finiteAverage f ≤ finiteAverage g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Jensen's inequality for the uniform law on a nonempty finite space. -/
theorem convex_finiteAverage_le {α E : Type*} [Fintype α] [Nonempty α]
    [AddCommGroup E] [Module ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (g : α → E) :
    f (finiteAverage g) ≤ finiteAverage (fun a => f (g a)) := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := hf.map_sum_le (t := Finset.univ)
    (w := fun _ : α => (Fintype.card α : ℝ)⁻¹) (p := g)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by simp [hcard]) (fun _ _ => Set.mem_univ _)
  simpa only [finiteAverage, Finset.smul_sum, smul_eq_mul, Finset.mul_sum] using h

end LeanNumDetect.FiniteMatrixSampling
