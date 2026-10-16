import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-! # Consecutive windows inside a measured integer block

The first sample of the cell indexed by `k` is `min k (L-n)`. Every sample
occurs in at most `2*n-1` cell windows; the weighted form below is the form
needed by the actual block-energy estimate.
-/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

def windowStart (L n k : ℕ) : ℕ := min k (L - n)

def windowIndex {L n : ℕ} (_hn : 0 < n) (hnL : n ≤ L)
    (k : Fin L) (j : Fin n) : Fin L :=
  ⟨windowStart L n k.val + j.val, by
    have hs : windowStart L n k.val ≤ L - n := Nat.min_le_right _ _
    have hj := j.isLt
    omega⟩

theorem windowStart_le_cell (L n k : ℕ) : windowStart L n k ≤ k :=
  Nat.min_le_left _ _

theorem cell_sub_windowStart_lt {L n : ℕ} (hn : 0 < n) (hnL : n ≤ L)
    (k : Fin L) : k.val - windowStart L n k.val < n := by
  dsimp [windowStart]
  omega

theorem cell_offset_mem_window {L n : ℕ} (hn : 0 < n) (hnL : n ≤ L)
    (k : Fin L) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ (k.val : ℝ) + u - windowStart L n k.val ∧
      (k.val : ℝ) + u - windowStart L n k.val ≤ n := by
  have hs : (windowStart L n k.val : ℝ) ≤ k.val :=
    Nat.cast_le.mpr (windowStart_le_cell L n k.val)
  have hdiff : k.val + 1 ≤ windowStart L n k.val + n := by
    have := cell_sub_windowStart_lt hn hnL k
    have := windowStart_le_cell L n k.val
    omega
  have hdiff' : (k.val : ℝ) + 1 ≤ windowStart L n k.val + n := by exact_mod_cast hdiff
  constructor <;> linarith

private theorem late_cell_card_le {L n : ℕ} (hn : 0 < n) (hnL : n ≤ L) :
    (Finset.univ.filter (fun k : Fin L => ¬ k.val ≤ L - n)).card ≤ n - 1 := by
  let T := {k : Fin L // ¬ k.val ≤ L - n}
  let f : T → Fin (n - 1) := fun k => ⟨k.val.val - (L - n + 1), by
    have hk := k.val.isLt
    have ht := k.property
    omega⟩
  have hf : Function.Injective f := by
    intro k l h
    apply Subtype.ext
    apply Fin.ext
    have he := congrArg Fin.val h
    dsimp [f] at he
    have hk := k.property
    have hl := l.property
    omega
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [T, Fintype.card_subtype, Fintype.card_fin] using hcard

private theorem early_window_sum_le {L n : ℕ} (hn : 0 < n) (hnL : n ≤ L)
    (f : Fin L → ℝ) (hf : ∀ k, 0 ≤ f k) (j : Fin n) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin L => k.val ≤ L - n),
      f (windowIndex hn hnL k j)) ≤ ∑ k, f k := by
  classical
  let E := Finset.univ.filter (fun k : Fin L => k.val ≤ L - n)
  have hinj : Set.InjOn (fun k => windowIndex hn hnL k j) E := by
    intro k hk l hl he
    have hk' := (Finset.mem_filter.mp hk).2
    have hl' := (Finset.mem_filter.mp hl).2
    have he' := congrArg Fin.val he
    simp only [windowIndex, windowStart, Nat.min_eq_left hk', Nat.min_eq_left hl'] at he'
    exact Fin.ext (by omega)
  calc
    _ = ∑ k ∈ E.image (fun k => windowIndex hn hnL k j), f k :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ k, f k := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun k _ _ => hf k)

private theorem one_window_sum_le {L n : ℕ} (hn : 0 < n) (hnL : n ≤ L)
    (f : Fin L → ℝ) (hf : ∀ k, 0 ≤ f k) (k : Fin L) :
    (∑ j, f (windowIndex hn hnL k j)) ≤ ∑ k, f k := by
  classical
  have hinj : Function.Injective (fun j => windowIndex hn hnL k j) := by
    intro i j he
    apply Fin.ext
    have he' := congrArg Fin.val he
    dsimp [windowIndex] at he'
    omega
  calc
    _ = ∑ j ∈ Finset.univ.image (fun j => windowIndex hn hnL k j), f j :=
      (Finset.sum_image (fun i _ j _ h => hinj h)).symm
    _ ≤ ∑ k, f k := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun k _ _ => hf k)

/-- The complete cell-to-sample counting estimate, including the repeated
rightmost window. Its constant is the literal `2*n-1`. -/
theorem window_weighted_sum_le {L n : ℕ} (hn : 0 < n) (hnL : n ≤ L)
    (f : Fin L → ℝ) (hf : ∀ k, 0 ≤ f k) :
    (∑ k : Fin L, ∑ j : Fin n, f (windowIndex hn hnL k j)) ≤
      (2 * (n : ℝ) - 1) * ∑ k, f k := by
  classical
  let E := Finset.univ.filter (fun k : Fin L => k.val ≤ L - n)
  let T := Finset.univ.filter (fun k : Fin L => ¬ k.val ≤ L - n)
  have htotal : 0 ≤ ∑ k, f k := Finset.sum_nonneg fun k _ => hf k
  have hearly : (∑ k ∈ E, ∑ j, f (windowIndex hn hnL k j)) ≤
      (n : ℝ) * ∑ k, f k := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _ : Fin n, ∑ k, f k :=
        Finset.sum_le_sum fun j _ => early_window_sum_le hn hnL f hf j
      _ = _ := by simp
  have hlate : (∑ k ∈ T, ∑ j, f (windowIndex hn hnL k j)) ≤
      ((n : ℝ) - 1) * ∑ k, f k := by
    calc
      _ ≤ ∑ _ ∈ T, ∑ k, f k :=
        Finset.sum_le_sum fun k _ => one_window_sum_le hn hnL f hf k
      _ = (T.card : ℝ) * ∑ k, f k := by simp
      _ ≤ ((n : ℝ) - 1) * ∑ k, f k := by
        apply mul_le_mul_of_nonneg_right _ htotal
        have hc := late_cell_card_le hn hnL
        have hc' : (T.card : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hc
        simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using hc'
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun k : Fin L => k.val ≤ L - n) (fun k => ∑ j, f (windowIndex hn hnL k j))
  change (∑ k ∈ E, ∑ j, f (windowIndex hn hnL k j)) +
    (∑ k ∈ T, ∑ j, f (windowIndex hn hnL k j)) = _ at hsplit
  rw [← hsplit]
  nlinarith

/-- Explicit multiplicity of any measured sample in all consecutive cell
windows, including the repeated rightmost window. -/
theorem window_multiplicity_le {L n : ℕ} (hn : 0 < n) (hnL : n ≤ L) (m : Fin L) :
    (Finset.univ.filter (fun p : Fin L × Fin n =>
      windowIndex hn hnL p.1 p.2 = m)).card ≤ 2*n-1 := by
  classical
  let f : Fin L → ℝ := fun k => if k=m then 1 else 0
  have h := window_weighted_sum_le hn hnL f (fun k => by dsimp [f]; split <;> norm_num)
  have htotal : (∑ k, f k) = 1 := by simp [f]
  rw [htotal, mul_one] at h
  let T := Finset.univ.filter (fun p : Fin L × Fin n => windowIndex hn hnL p.1 p.2 = m)
  have hcard : (T.card : ℝ) = ∑ k : Fin L, ∑ j : Fin n, f (windowIndex hn hnL k j) := by
    rw [← Fintype.sum_prod_type']
    dsimp [f]
    rw [← Finset.sum_filter]
    simp [T]
  rw [← hcard] at h
  have hsub : (2 * (n : ℝ) - 1) = ((2*n-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*n)]
    norm_num
  rw [hsub] at h
  exact_mod_cast h

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
