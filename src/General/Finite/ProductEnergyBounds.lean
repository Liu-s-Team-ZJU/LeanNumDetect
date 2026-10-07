import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-!
# Energy estimates from coordinate sections

A point-evaluation bound on every coordinate section iterates with the exact
product constant. A cross-inner-product bound along one coordinate lifts to
the whole product by Cauchy--Schwarz on the other coordinates. The separating
coordinate may be chosen separately for each pair of spaces.
-/

set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open WithLp

namespace LeanNumDetect.ProductEnergyBounds

theorem sum_finSucc_functions {κ A : Type*} [Fintype κ] [AddCommMonoid A]
    {d : ℕ} (F : (Fin (d + 1) → κ) → A) :
    (∑ x, F x) = ∑ a : κ, ∑ y : Fin d → κ, F (Fin.cons a y) := by
  classical
  simpa only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk] using
    ((Fin.consEquiv (fun _ : Fin (d + 1) => κ)).sum_comp F).symm

/-- Iterating one-coordinate row estimates preserves their exact constant.
The normalization `Q` can be any nonnegative real number. -/
theorem product_row_energy_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    {d : ℕ} (F : (Fin d → κ) → ℂ) {Q B : ℝ} (hQ : 0 ≤ Q) (hB : 0 ≤ B)
    (hsection : ∀ (q : Fin d) (x : Fin d → κ),
      Q * ‖F x‖ ^ 2 ≤ B * ∑ a : κ, ‖F (Function.update x q a)‖ ^ 2)
    (x : Fin d → κ) :
    Q ^ d * ‖F x‖ ^ 2 ≤ B ^ d * ∑ y : Fin d → κ, ‖F y‖ ^ 2 := by
  classical
  induction d with
  | zero =>
    have hx : x = default := Subsingleton.elim _ _
    simp [hx]
  | succ d ih =>
    let y := Fin.tail x
    have hx : x = Fin.cons (x 0) y := (Fin.cons_self_tail x).symm
    have hhead : Q * ‖F x‖ ^ 2 ≤ B * ∑ a : κ, ‖F (Fin.cons a y)‖ ^ 2 := by
      have h := hsection 0 (Fin.cons (x 0) y)
      rw [← hx] at h
      convert h using 1
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [hx, Fin.update_cons_zero]
    have htail (a : κ) : Q ^ d * ‖F (Fin.cons a y)‖ ^ 2 ≤
        B ^ d * ∑ z : Fin d → κ, ‖F (Fin.cons a z)‖ ^ 2 := by
      apply ih (F := fun z => F (Fin.cons a z))
      intro q z
      simpa only [Fin.cons_update] using hsection q.succ (Fin.cons a z)
    calc
      Q ^ (d + 1) * ‖F x‖ ^ 2 = Q ^ d * (Q * ‖F x‖ ^ 2) := by ring
      _ ≤ Q ^ d * (B * ∑ a : κ, ‖F (Fin.cons a y)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hhead (pow_nonneg hQ _)
      _ = B * ∑ a : κ, Q ^ d * ‖F (Fin.cons a y)‖ ^ 2 := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ ≤ B * ∑ a : κ, B ^ d * ∑ z : Fin d → κ, ‖F (Fin.cons a z)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => htail a) hB
      _ = B ^ (d + 1) * ∑ z : Fin (d + 1) → κ, ‖F z‖ ^ 2 := by
        rw [sum_finSucc_functions, ← Finset.mul_sum]
        ring

/-- Splitting off any chosen coordinate gives an exact sum identity. -/
theorem sum_split_coordinate {I κ A : Type*} [Fintype I] [DecidableEq I]
    [Fintype κ] [AddCommMonoid A] (q : I) (F : (I → κ) → A) :
    (∑ x, F x) = ∑ y : {i : I // i ≠ q} → κ, ∑ a : κ,
      F ((Equiv.funSplitAt q κ).symm (a, y)) := by
  classical
  rw [← (Equiv.funSplitAt q κ).symm.sum_comp F, Fintype.sum_prod_type,
    Finset.sum_comm]

/-- A relative inner-product estimate along one coordinate section suffices
for the same estimate on the full finite product. -/
theorem product_cross_inner_bound {I κ : Type*} [Fintype I] [DecidableEq I]
    [Fintype κ] (q : I) (u v : (I → κ) → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsection : ∀ y : {i : I // i ≠ q} → κ,
      ‖∑ a : κ, star (u ((Equiv.funSplitAt q κ).symm (a, y))) *
          v ((Equiv.funSplitAt q κ).symm (a, y))‖ ≤
        ε * Real.sqrt (∑ a : κ, ‖u ((Equiv.funSplitAt q κ).symm (a, y))‖ ^ 2) *
          Real.sqrt (∑ a : κ, ‖v ((Equiv.funSplitAt q κ).symm (a, y))‖ ^ 2)) :
    ‖∑ x : I → κ, star (u x) * v x‖ ≤
      ε * Real.sqrt (∑ x : I → κ, ‖u x‖ ^ 2) *
        Real.sqrt (∑ x : I → κ, ‖v x‖ ^ 2) := by
  classical
  let U := fun y : {i : I // i ≠ q} → κ =>
    ∑ a : κ, ‖u ((Equiv.funSplitAt q κ).symm (a, y))‖ ^ 2
  let V := fun y : {i : I // i ≠ q} → κ =>
    ∑ a : κ, ‖v ((Equiv.funSplitAt q κ).symm (a, y))‖ ^ 2
  have hU y : 0 ≤ U y := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hV y : 0 ≤ V y := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun y => Real.sqrt (U y)) (fun y => Real.sqrt (V y))
  simp_rw [Real.sq_sqrt (hU _), Real.sq_sqrt (hV _)] at hcs
  rw [sum_split_coordinate q]
  calc
    _ ≤ ∑ y : {i : I // i ≠ q} → κ,
        ‖∑ a : κ, star (u ((Equiv.funSplitAt q κ).symm (a, y))) *
          v ((Equiv.funSplitAt q κ).symm (a, y))‖ := norm_sum_le _ _
    _ ≤ ∑ y : {i : I // i ≠ q} → κ,
        ε * Real.sqrt (U y) * Real.sqrt (V y) :=
      Finset.sum_le_sum fun y _ => hsection y
    _ = ε * ∑ y : {i : I // i ≠ q} → κ, Real.sqrt (U y) * Real.sqrt (V y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ ε * (Real.sqrt (∑ y, U y) * Real.sqrt (∑ y, V y)) :=
      mul_le_mul_of_nonneg_left hcs hε
    _ = _ := by
      rw [sum_split_coordinate q (fun x : I → κ => ‖u x‖ ^ 2),
        sum_split_coordinate q (fun x : I → κ => ‖v x‖ ^ 2)]
      dsimp only [U, V]
      ring

end LeanNumDetect.ProductEnergyBounds
