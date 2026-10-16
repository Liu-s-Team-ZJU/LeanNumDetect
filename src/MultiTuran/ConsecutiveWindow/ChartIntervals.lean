import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! # A finite circular configuration has a large empty gap -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

theorem exists_short_chart_of_ordered_points {k n : ℕ} {p : ℝ}
    (hp : 0 < p) (hn : 0 < n) (hkn : k + 1 ≤ n)
    (x : Fin (k + 1) → ℝ) (hmono : Monotone x)
    (hzero : ∀ i, 0 ≤ x i) (hperiod : ∀ i, x i < p) :
    ∃ center : ℝ, ∀ i, ∃ winding : ℤ,
      |x i - center - p * (winding : ℝ)| ≤ p / 2 - p / (2 * n) := by
  classical
  let gap (i : Fin (k + 1)) : ℝ :=
    x (finRotate (k + 1) i) - x i + if i = Fin.last k then p else 0
  have hsum : (∑ i, gap i) = p := by
    simp only [gap, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [Equiv.sum_comp (finRotate (k + 1)) x]
    simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalf : p / (2 * (n : ℝ)) = (p / n) / 2 := by ring
  rw [hhalf]
  have hcount : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hkn
  obtain ⟨i, hi⟩ : ∃ i : Fin (k + 1), p / n ≤ gap i := by
    by_contra h
    have hlt : ∀ i : Fin (k + 1), gap i < p / n := by
      intro i
      have := not_exists.mp h i
      linarith
    have hltSum : (∑ i, gap i) < ∑ _i : Fin (k + 1), p / n := by
      apply Finset.sum_lt_sum
      · intro i _; exact (hlt i).le
      · exact ⟨0, Finset.mem_univ _, hlt 0⟩
    have hupper : (∑ _i : Fin (k + 1), p / n) ≤ p := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        _ ≤ (n : ℝ) * (p / n) := mul_le_mul_of_nonneg_right hcount (by positivity)
        _ = p := by field_simp
    rw [hsum] at hltSum
    exact (not_lt_of_ge hupper) hltSum
  by_cases hilast : i = Fin.last k
  · have hgap : p / n ≤ p + x 0 - x (Fin.last k) := by
      simp only [gap, hilast, finRotate_last, if_true] at hi
      linarith
    refine ⟨(x 0 + x (Fin.last k)) / 2, ?_⟩
    intro j
    refine ⟨0, ?_⟩
    have hlo : x 0 ≤ x j := hmono (Fin.zero_le _)
    have hhi : x j ≤ x (Fin.last k) := hmono (Fin.le_last _)
    rw [Int.cast_zero, mul_zero, sub_zero, abs_le]
    constructor <;> linarith
  · have hiv : i.val < k := by
      have hne : i.val ≠ k := by intro h; exact hilast (Fin.ext h)
      omega
    let next : Fin (k + 1) := ⟨i.val + 1, by omega⟩
    have hnext : finRotate (k + 1) i = next := by
      exact finRotate_of_lt hiv
    have hgap : p / n ≤ x next - x i := by
      simpa only [gap, hnext, if_neg hilast, add_zero] using hi
    refine ⟨(x next + x i + p) / 2, ?_⟩
    intro j
    by_cases hji : j ≤ i
    · refine ⟨-1, ?_⟩
      have hhi := hmono hji
      have hlo : x next ≤ x j + p := by linarith [hzero j, hperiod next]
      norm_num only [Int.cast_neg, Int.cast_one, mul_neg_one, sub_neg_eq_add]
      rw [abs_le]
      constructor <;> linarith
    · refine ⟨0, ?_⟩
      have hjnext : next ≤ j := by
        change i.val + 1 ≤ j.val
        have : ¬ j.val ≤ i.val := hji
        omega
      have hlo := hmono hjnext
      have hhi : x j ≤ x i + p := by linarith [hzero i, hperiod j]
      rw [Int.cast_zero, mul_zero, sub_zero, abs_le]
      constructor <;> linarith

theorem exists_short_chart_of_bounded_points {n : ℕ} {p : ℝ}
    (hp : 0 < p) (hn : 0 < n) (x : Fin n → ℝ)
    (hzero : ∀ i, 0 ≤ x i) (hperiod : ∀ i, x i < p) :
    ∃ center : ℝ, ∃ winding : Fin n → ℤ,
      ∀ i, |x i - center - p * (winding i : ℝ)| ≤ p / 2 - p / (2 * n) := by
  classical
  let S : Finset ℝ := Finset.univ.image x
  have hSpos : 0 < S.card := Finset.card_pos.mpr
    ⟨x ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, S.card = k + 1 := by
    exact ⟨S.card - 1, by omega⟩
  let e : Fin (k + 1) ≃o S := S.orderIsoOfFin hk
  let y : Fin (k + 1) → ℝ := fun i => (e i).val
  have hyzero (i : Fin (k + 1)) : 0 ≤ y i := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (e i).property
    simpa only [y, hj] using hzero j
  have hyperiod (i : Fin (k + 1)) : y i < p := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (e i).property
    simpa only [y, hj] using hperiod j
  have hcard : k + 1 ≤ n := by
    rw [← hk]
    exact (Finset.card_image_le).trans (by simp)
  obtain ⟨center, hcenter⟩ := exists_short_chart_of_ordered_points hp hn hcard y
    (fun _ _ hij => e.monotone hij) hyzero hyperiod
  let index (i : Fin n) : Fin (k + 1) :=
    e.symm ⟨x i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hyindex (i : Fin n) : y (index i) = x i := by
    simp only [y, index, OrderIso.apply_symm_apply]
  have hwind (i : Fin n) : ∃ w : ℤ,
      |x i - center - p * (w : ℝ)| ≤ p / 2 - p / (2 * n) := by
    simpa only [hyindex] using hcenter (index i)
  choose winding hw using hwind
  exact ⟨center, winding, hw⟩

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
