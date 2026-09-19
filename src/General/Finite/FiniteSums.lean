import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Reusable bounds for finite sums, products and spectral moments. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

open scoped BigOperators
open Finset

namespace LeanNumDetect

theorem traceless_sum_sq_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {a b : ℝ} (hx : ∀ i ∈ s, a ≤ x i ∧ x i ≤ b)
    (hzero : ∑ i ∈ s, x i = 0) :
    (∑ i ∈ s, x i ^ 2) ≤ (s.card : ℝ) * (b - a) ^ 2 / 4 := by
  have hi : ∀ i ∈ s, x i ^ 2 ≤ (a + b) * x i - a * b := by
    intro i hi
    have h := hx i hi
    nlinarith [mul_nonneg (sub_nonneg.mpr h.1) (sub_nonneg.mpr h.2)]
  have hs := sum_le_sum hi
  simp only [sum_sub_distrib, ← mul_sum, hzero, mul_zero, sum_const,
    nsmul_eq_mul, zero_sub] at hs
  have hn : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  nlinarith only [hs, mul_nonneg hn (sq_nonneg (a + b))]

theorem sum_sq_sq_le_card_mul_sum_fourth {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∑ i ∈ s, x i ^ 2) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, x i ^ 4 := by
  have h := sum_mul_sq_le_sq_mul_sq s (fun i => x i ^ 2) (fun _ => (1 : ℝ))
  simpa [← pow_mul, mul_comm] using h

theorem sum_sq_pos {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h : ∃ i ∈ s, x i ≠ 0) : 0 < ∑ i ∈ s, x i ^ 2 := by
  obtain ⟨i, hi, hxi⟩ := h
  exact sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, hi, sq_pos_of_ne_zero hxi⟩

theorem telescoping_product (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (∏ j ∈ range n, (x + j) / (x + j + 1)) = x / (x + n) := by
  induction n with
  | zero => simp [ne_of_gt hx]
  | succ n ih =>
    rw [prod_range_succ, ih]
    have hn : x + n ≠ 0 := ne_of_gt (by positivity)
    have hn₁ : x + n + 1 ≠ 0 := ne_of_gt (by positivity)
    push_cast
    field_simp
    ring

theorem one_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∏ i ∈ s, (1 - a i) ≤ ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (mem_insert_self i s)
    have has : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ 1 :=
      fun j hj => ha j (mem_insert_of_mem hj)
    have hp : 0 ≤ ∏ j ∈ s, (1 - a j) :=
      prod_nonneg fun j hj => sub_nonneg.mpr (has j hj).2
    have hs : 0 ≤ ∑ j ∈ s, a j := sum_nonneg fun j hj => (has j hj).1
    have hib := ih has
    rw [prod_insert hi, sum_insert hi]
    nlinarith [mul_nonneg hai.1 hs,
      mul_le_mul_of_nonneg_left hib (sub_nonneg.mpr hai.2)]

theorem sum_odds (n : ℕ) :
    (∑ h ∈ range n, (2 * (h : ℝ) + 1)) = (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Summing the scalar endpoint estimate over subarray rows introduces no loss. -/
theorem sum_endpoint_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (energy : ι → κ → ℝ) (endpoint : ι → ℝ) (L : ℝ)
    (h : ∀ k, endpoint k ≤ L * ∑ j, energy k j) :
    (∑ k, endpoint k) ≤ L * ∑ j, ∑ k, energy k j := by
  calc
    _ ≤ ∑ k, L * ∑ j, energy k j := sum_le_sum fun k _ => h k
    _ = _ := by rw [← mul_sum, sum_comm]

end LeanNumDetect
