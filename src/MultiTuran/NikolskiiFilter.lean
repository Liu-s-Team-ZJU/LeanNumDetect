import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Polynomial filters for imaginary exponential sums

A product of elementary two-dimensional rotations gives the finite polynomial
filter needed for the constant `π / 2`. The construction and all of its bounds
are proved directly. No extremal-polynomial result is assumed.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace LeanNumDetect.MultiTuran.NikolskiiFilter
noncomputable section

/-- A polynomial unitary rotation, with a one-step delay in its second input. -/
def rotationPair (θ : ℝ) : ℕ → ℂ[X] × ℂ[X]
  | 0 => (1, 0)
  | k + 1 =>
    let p := rotationPair θ k
    (C (Real.cos θ : ℂ) * p.1 - C (Real.sin θ : ℂ) * X * p.2,
      C (Real.sin θ : ℂ) * p.1 + C (Real.cos θ : ℂ) * X * p.2)

theorem rotationPair_eval_zero_first (θ : ℝ) (k : ℕ) :
    ((rotationPair θ k).1).eval 0 = (Real.cos θ : ℂ) ^ k := by
  induction k with
  | zero => simp [rotationPair]
  | succ k ih =>
    simp only [rotationPair, eval_sub, eval_mul, eval_C, eval_X,
      mul_zero, zero_mul, sub_zero, ih, pow_succ]
    ring

theorem rotationPair_eval_one (θ : ℝ) (k : ℕ) :
    ((rotationPair θ k).1).eval 1 = (Real.cos ((k : ℝ) * θ) : ℂ) ∧
      ((rotationPair θ k).2).eval 1 = (Real.sin ((k : ℝ) * θ) : ℂ) := by
  induction k with
  | zero => simp [rotationPair]
  | succ k ih =>
    simp only [rotationPair, eval_sub, eval_add, eval_mul, eval_C, eval_X,
      mul_one, ih.1, ih.2]
    constructor
    · simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.cos_add]
      push_cast
      ring
    · simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.sin_add]
      push_cast
      ring

private theorem rotation_normSq_identity (c s : ℝ) (u v : ℂ) :
    Complex.normSq ((c : ℂ) * u - (s : ℂ) * v) +
        Complex.normSq ((s : ℂ) * u + (c : ℂ) * v) =
      (c ^ 2 + s ^ 2) * (Complex.normSq u + Complex.normSq v) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

/-- On the unit circle, the two output energies always add to one. -/
theorem rotationPair_circle_energy (θ : ℝ) (k : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    Complex.normSq (((rotationPair θ k).1).eval z) +
        Complex.normSq (((rotationPair θ k).2).eval z) = 1 := by
  induction k with
  | zero => simp [rotationPair]
  | succ k ih =>
    simp only [rotationPair, eval_sub, eval_add, eval_mul, eval_C, eval_X, mul_assoc]
    rw [rotation_normSq_identity, Real.cos_sq_add_sin_sq,
      Complex.normSq_mul, Complex.normSq_eq_norm_sq z, hz]
    simpa using ih

theorem rotationPair_circle_first_norm_le_one (θ : ℝ) (k : ℕ)
    (z : ℂ) (hz : ‖z‖ = 1) : ‖((rotationPair θ k).1).eval z‖ ≤ 1 := by
  have h := rotationPair_circle_energy θ k z hz
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  nlinarith [sq_nonneg ‖((rotationPair θ k).2).eval z‖,
    norm_nonneg (((rotationPair θ k).1).eval z)]

/-- After `k+1` rotations both components have degree at most `k`. -/
theorem rotationPair_natDegree (θ : ℝ) (k : ℕ) :
    ((rotationPair θ (k + 1)).1).natDegree ≤ k ∧
      ((rotationPair θ (k + 1)).2).natDegree ≤ k := by
  induction k with
  | zero => simp [rotationPair]
  | succ k ih =>
    have hX : (X * (rotationPair θ (k + 1)).2).natDegree ≤ k + 1 := by
      have h : (X * (rotationPair θ (k + 1)).2).natDegree ≤
          (X : ℂ[X]).natDegree + ((rotationPair θ (k + 1)).2).natDegree := natDegree_mul_le
      simp only [natDegree_X] at h
      omega
    change
      (C (Real.cos θ : ℂ) * (rotationPair θ (k + 1)).1 -
        C (Real.sin θ : ℂ) * X * (rotationPair θ (k + 1)).2).natDegree ≤ k + 1 ∧
      (C (Real.sin θ : ℂ) * (rotationPair θ (k + 1)).1 +
        C (Real.cos θ : ℂ) * X * (rotationPair θ (k + 1)).2).natDegree ≤ k + 1
    constructor
    · apply (natDegree_sub_le _ _).trans
      apply max_le
      · exact (natDegree_C_mul_le _ _).trans (ih.1.trans (Nat.le_succ k))
      · rw [mul_assoc]
        exact (natDegree_C_mul_le _ _).trans hX
    · apply (natDegree_add_le _ _).trans
      apply max_le
      · exact (natDegree_C_mul_le _ _).trans (ih.1.trans (Nat.le_succ k))
      · rw [mul_assoc]
        exact (natDegree_C_mul_le _ _).trans hX

def filterAngle (m : ℕ) : ℝ := Real.pi / (2 * ((m : ℝ) + 1))

theorem filterAngle_cos_pos {m : ℕ} (hm : 0 < m) :
    0 < Real.cos (filterAngle m) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hθpos : 0 < filterAngle m := by unfold filterAngle; positivity
  have hθlt : filterAngle m < Real.pi / 2 := by
    apply div_lt_div_of_pos_left Real.pi_pos (by norm_num)
    nlinarith
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθlt⟩

/-- The normalized degree-`m` annihilating filter. -/
def filterPolynomial (m : ℕ) : ℂ[X] :=
  C (((Real.cos (filterAngle m) : ℂ) ^ (m + 1))⁻¹) *
    (rotationPair (filterAngle m) (m + 1)).1

theorem filterPolynomial_natDegree (m : ℕ) :
    (filterPolynomial m).natDegree ≤ m :=
  (natDegree_C_mul_le _ _).trans (rotationPair_natDegree (filterAngle m) m).1

theorem filterPolynomial_eval_zero {m : ℕ} (hm : 0 < m) :
    (filterPolynomial m).eval 0 = 1 := by
  have hc : (Real.cos (filterAngle m) : ℂ) ≠ 0 := by
    exact_mod_cast (filterAngle_cos_pos hm).ne'
  simp only [filterPolynomial, eval_mul, eval_C, rotationPair_eval_zero_first]
  exact inv_mul_cancel₀ (pow_ne_zero _ hc)

theorem filterPolynomial_eval_one (m : ℕ) :
    (filterPolynomial m).eval 1 = 0 := by
  have hangle : ((m + 1 : ℕ) : ℝ) * filterAngle m = Real.pi / 2 := by
    unfold filterAngle
    push_cast
    field_simp
  rw [filterPolynomial, eval_mul, eval_C,
    (rotationPair_eval_one (filterAngle m) (m + 1)).1, hangle, Real.cos_pi_div_two]
  simp only [Complex.ofReal_zero, mul_zero]

/-- Its unit-circle bound is the precise one that yields `π / 2` asymptotically. -/
theorem filterPolynomial_circle_norm_le {m : ℕ} (hm : 0 < m)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(filterPolynomial m).eval z‖ ≤
      1 / (Real.cos (filterAngle m)) ^ (m + 1) := by
  have hc := filterAngle_cos_pos hm
  simp only [filterPolynomial, eval_mul, eval_C, norm_mul, norm_inv, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  simpa only [one_div, mul_one] using
    mul_le_mul_of_nonneg_left
      (rotationPair_circle_first_norm_le_one (filterAngle m) (m + 1) z hz)
      (by positivity : 0 ≤ ((Real.cos (filterAngle m)) ^ (m + 1))⁻¹)

/-- A coefficient-vector interface for finite convolution and Parseval proofs. -/
theorem exists_filter_coefficients (m : ℕ) (hm : 0 < m) :
    ∃ H : Fin (m + 1) → ℂ,
      H ⟨0, by omega⟩ = 1 ∧
      (∑ k, H k) = 0 ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ‖∑ k, H k * z ^ k.val‖ ≤
          1 / (Real.cos (filterAngle m)) ^ (m + 1) := by
  let P := filterPolynomial m
  have hrepr (z : ℂ) : P.eval z = ∑ k : Fin (m + 1), P.coeff k.val * z ^ k.val := by
    rw [Fin.sum_univ_eq_sum_range (fun k => P.coeff k * z ^ k) (m + 1)]
    exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (filterPolynomial_natDegree m)) z
  refine ⟨fun k => P.coeff k.val, ?_, ?_, ?_⟩
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using filterPolynomial_eval_zero hm
  · have h := (hrepr 1).symm.trans (filterPolynomial_eval_one m)
    simpa only [one_pow, mul_one] using h
  · intro z hz
    rw [← hrepr]
    exact filterPolynomial_circle_norm_le hm z hz

end
end LeanNumDetect.MultiTuran.NikolskiiFilter
