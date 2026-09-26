import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Finite dyadic trace inequalities for the Golden--Thompson argument.  The proof
uses the Frobenius Cauchy--Schwarz inequality and induction on dyadic products.
The elementary proof follows the dyadic Holder and disentangling arguments
in James R. Lee, CSE 599I (Spring 2021), Lecture 3, Lemmas 1.2 and 1.4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators ComplexOrder

namespace LeanNumDetect.GoldenThompson

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An even Schatten moment, expressed without extracting a root. -/
def dyadicMoment (k : ℕ) (A : Matrix n n ℂ) : ℝ :=
  (Matrix.trace ((Aᴴ * A) ^ (2 ^ k))).re

lemma dyadicMoment_nonneg (k : ℕ) (A : Matrix n n ℂ) : 0 ≤ dyadicMoment k A := by
  exact (Complex.nonneg_iff.mp ((posSemidef_conjTranspose_mul_self A).pow (2 ^ k)).trace_nonneg).1

omit [DecidableEq n] in
lemma trace_conjTranspose_mul_re (A : Matrix n n ℂ) :
    (Matrix.trace (Aᴴ * A)).re = ∑ p : n × n, ‖A p.1 p.2‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [RCLike.star_def, Complex.conj_mul']
  norm_cast

lemma norm_trace_mul_sq_le (A B : Matrix n n ℂ) :
    ‖Matrix.trace (A * B)‖ ^ 2 ≤ dyadicMoment 0 A * dyadicMoment 0 B := by
  have ht : Matrix.trace (A * B) = ∑ p : n × n, A p.1 p.2 * B p.2 p.1 := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  have hn := norm_sum_le (Finset.univ : Finset (n × n))
    (fun p : n × n => A p.1 p.2 * B p.2 p.1)
  rw [← ht] at hn
  simp only [norm_mul] at hn
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (n × n))
    (fun p : n × n => ‖A p.1 p.2‖) (fun p : n × n => ‖B p.2 p.1‖)
  have hB : (∑ p : n × n, ‖B p.2 p.1‖ ^ 2) = ∑ p : n × n, ‖B p.1 p.2‖ ^ 2 := by
    simp only [Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hB] at hs
  unfold dyadicMoment
  simp only [pow_zero, pow_one, trace_conjTranspose_mul_re]
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs

lemma trace_mul_pow_cycle (A B : Matrix n n ℂ) (k : ℕ) :
    Matrix.trace ((A * B) ^ k) = Matrix.trace ((B * A) ^ k) := by
  cases k with
  | zero => simp
  | succ k =>
    rw [pow_succ, ← mul_assoc, Matrix.trace_mul_cycle, ← mul_pow_mul, mul_assoc, ← pow_succ]

lemma dyadicMoment_conjTranspose (k : ℕ) (A : Matrix n n ℂ) :
    dyadicMoment k Aᴴ = dyadicMoment k A := by
  simp only [dyadicMoment, conjTranspose_conjTranspose]
  rw [trace_mul_pow_cycle]

lemma dyadicMoment_gram (k : ℕ) (A : Matrix n n ℂ) :
    dyadicMoment k (Aᴴ * A) = dyadicMoment (k + 1) A := by
  simp only [dyadicMoment, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [← pow_two, ← pow_mul, pow_succ, Nat.mul_comm 2]

lemma dyadicMoment_cogram (k : ℕ) (A : Matrix n n ℂ) :
    dyadicMoment k (A * Aᴴ) = dyadicMoment (k + 1) A := by
  simpa only [conjTranspose_conjTranspose, dyadicMoment_conjTranspose] using
    dyadicMoment_gram k Aᴴ

lemma dyadicMoment_mul (k : ℕ) (A B : Matrix n n ℂ) :
    dyadicMoment k (A * B) =
      (Matrix.trace (((Aᴴ * A) * (B * Bᴴ)) ^ (2 ^ k))).re := by
  unfold dyadicMoment
  simp only [conjTranspose_mul]
  rw [show Bᴴ * Aᴴ * (A * B) = Bᴴ * ((Aᴴ * A) * B) by noncomm_ring,
    trace_mul_pow_cycle]
  congr 2
  noncomm_ring

private lemma exists_pair_products {α : Type*} [Monoid α]
    (P Q : α → Prop) (hPQ : ∀ a b, P a → P b → Q (a * b))
    (m : ℕ) (l : List α) (hlen : l.length = 2 * m) (hl : ∀ a ∈ l, P a) :
    ∃ t : List α, t.length = m ∧ t.prod = l.prod ∧ ∀ a ∈ t, Q a := by
  induction m generalizing l with
  | zero =>
    have he : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst l
    exact ⟨[], rfl, rfl, by simp⟩
  | succ m ih =>
    cases l with
    | nil => simp at hlen
    | cons a l =>
      cases l with
      | nil => simp at hlen; omega
      | cons b l =>
        have htail : l.length = 2 * m := by simp at hlen; omega
        obtain ⟨t, htlen, htprod, ht⟩ := ih l htail (fun c hc => hl c (by simp [hc]))
        refine ⟨a * b :: t, by simp [htlen], ?_, ?_⟩
        · simp [htprod, mul_assoc]
        · intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact hPQ a b (hl a (by simp)) (hl b (by simp))
          · exact ht c hc

/-- Normalized dyadic Hölder for a product of arbitrary complex matrices. -/
theorem norm_trace_prod_le_one_of_dyadicMoments (k : ℕ) (l : List (Matrix n n ℂ))
    (hlen : l.length = 2 ^ (k + 1))
    (hl : ∀ A ∈ l, dyadicMoment k A ≤ 1) : ‖Matrix.trace l.prod‖ ≤ 1 := by
  induction k generalizing l with
  | zero =>
    cases l with
    | nil => simp at hlen
    | cons A l =>
      cases l with
      | nil => simp at hlen
      | cons B l =>
        have htail : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        subst l
        have hA := hl A (by simp)
        have hB := hl B (by simp)
        have hAB : dyadicMoment 0 A * dyadicMoment 0 B ≤ 1 :=
          (mul_le_mul hA hB (dyadicMoment_nonneg 0 B) zero_le_one).trans_eq (by ring)
        have hcs := (norm_trace_mul_sq_le A B).trans hAB
        simp only [List.prod_cons, List.prod_nil, mul_one]
        nlinarith [norm_nonneg (Matrix.trace (A * B))]
  | succ k ih =>
    have hmul (A B : Matrix n n ℂ)
        (hA : dyadicMoment (k + 1) A ≤ 1) (hB : dyadicMoment (k + 1) B ≤ 1) :
        dyadicMoment k (A * B) ≤ 1 := by
      let t := (List.replicate (2 ^ k) [Aᴴ * A, B * Bᴴ]).flatten
      have htlen : t.length = 2 ^ (k + 1) := by simp [t, pow_succ]
      have ht : ∀ C ∈ t, dyadicMoment k C ≤ 1 := by
        intro C hC
        simp only [t, List.mem_flatten] at hC
        obtain ⟨r, hr, hCr⟩ := hC
        have hr' : r = [Aᴴ * A, B * Bᴴ] := (List.mem_replicate.mp hr).2
        subst r
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hCr
        rcases hCr with rfl | rfl
        · rwa [dyadicMoment_gram]
        · rwa [dyadicMoment_cogram]
      have hb := ih t htlen ht
      have htprod : t.prod = ((Aᴴ * A) * (B * Bᴴ)) ^ (2 ^ k) := by
        simp [t, List.prod_flatten]
      rw [htprod] at hb
      rw [dyadicMoment_mul]
      exact (Complex.re_le_norm _).trans hb
    obtain ⟨t, htlen, htprod, ht⟩ := exists_pair_products
      (fun A => dyadicMoment (k + 1) A ≤ 1)
      (fun A => dyadicMoment k A ≤ 1) hmul (2 ^ (k + 1)) l
      (by simpa only [pow_succ, Nat.mul_comm] using hlen) hl
    have h := ih t htlen ht
    rwa [htprod] at h

lemma dyadicMoment_real_smul (k : ℕ) (A : Matrix n n ℂ) (r : ℝ) :
    dyadicMoment k (r • A) = r ^ (2 ^ (k + 1)) * dyadicMoment k A := by
  simp only [dyadicMoment, conjTranspose_smul, star_trivial, smul_mul_smul_comm,
    smul_pow, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  congr 1
  rw [← pow_two, ← pow_mul, pow_succ, Nat.mul_comm 2]

/-- A dyadic trace power is bounded by the matching even Schatten moment. -/
theorem norm_trace_pow_le_dyadicMoment (k : ℕ) (A : Matrix n n ℂ) :
    ‖Matrix.trace (A ^ (2 ^ (k + 1)))‖ ≤ dyadicMoment k A := by
  by_contra! hlt
  let b := (‖Matrix.trace (A ^ (2 ^ (k + 1)))‖ + dyadicMoment k A) / 2
  have hb0 : 0 < b := by dsimp [b]; linarith [dyadicMoment_nonneg k A]
  have hbm : dyadicMoment k A < b := by dsimp [b]; linarith
  have hbt : b < ‖Matrix.trace (A ^ (2 ^ (k + 1)))‖ := by dsimp [b]; linarith
  let r := b ^ (((2 ^ (k + 1) : ℕ) : ℝ)⁻¹)
  have hr0 : 0 < r := Real.rpow_pos_of_pos hb0 _
  have hrp : r ^ (2 ^ (k + 1)) = b :=
    Real.rpow_inv_natCast_pow hb0.le (by positivity)
  have hm : dyadicMoment k (r⁻¹ • A) ≤ 1 := by
    rw [dyadicMoment_real_smul, inv_pow, hrp]
    exact (inv_mul_le_one₀ hb0).2 hbm.le
  have ht := norm_trace_prod_le_one_of_dyadicMoments k
    (List.replicate (2 ^ (k + 1)) (r⁻¹ • A)) (by simp)
    (fun B hB => by
      have he := (List.mem_replicate.mp hB).2
      simpa only [he] using hm)
  simp only [List.prod_replicate, smul_pow, Matrix.trace_smul, norm_smul,
    inv_pow, hrp, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hb0.le)] at ht
  have hle : ‖Matrix.trace (A ^ (2 ^ (k + 1)))‖ ≤ b := (inv_mul_le_one₀ hb0).1 ht
  exact (not_le.mpr hbt) hle

lemma dyadicMoment_mul_of_isHermitian (k : ℕ) {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    dyadicMoment k (A * B) = (Matrix.trace ((A ^ 2 * B ^ 2) ^ (2 ^ k))).re := by
  rw [dyadicMoment_mul, hA.eq, hB.eq, ← pow_two, ← pow_two]

/-- The finite dyadic sorting inequality for Hermitian matrices. -/
theorem norm_trace_mul_pow_dyadic_le (k : ℕ) {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖Matrix.trace ((A * B) ^ (2 ^ (k + 1)))‖ ≤
      (Matrix.trace (A ^ (2 ^ (k + 1)) * B ^ (2 ^ (k + 1)))).re := by
  induction k generalizing A B with
  | zero =>
    have h := norm_trace_pow_le_dyadicMoment 0 (A * B)
    rw [dyadicMoment_mul_of_isHermitian 0 hA hB] at h
    simpa only [Nat.zero_add, pow_zero, pow_one] using h
  | succ k ih =>
    have h := norm_trace_pow_le_dyadicMoment (k + 1) (A * B)
    rw [dyadicMoment_mul_of_isHermitian (k + 1) hA hB] at h
    have hi := ih (hA.pow 2) (hB.pow 2)
    simp only [← pow_mul, ← pow_succ'] at hi
    exact h.trans ((Complex.re_le_norm _).trans hi)

/-- The real-part formulation needed before the Lie--Trotter limit. -/
theorem trace_mul_pow_dyadic_le (k : ℕ) {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace ((A * B) ^ (2 ^ (k + 1)))).re ≤
      (Matrix.trace (A ^ (2 ^ (k + 1)) * B ^ (2 ^ (k + 1)))).re :=
  (Complex.re_le_norm _).trans (norm_trace_mul_pow_dyadic_le k hA hB)

end

end LeanNumDetect.GoldenThompson
