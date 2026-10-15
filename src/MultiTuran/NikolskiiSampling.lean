import MultiTuran.CardinalPackets
import MultiTuran.PolynomialCoefficientEnergy
import General.Fourier.ExponentialSums
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Finite annihilators and endpoint sampling

All statements here are finite algebraic inequalities. Polynomial filters
annihilate the sampled exponential sum exactly, and Cauchy--Schwarz bounds
the endpoint by the remaining coefficient and sample energies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Polynomial

namespace LeanNumDetect.MultiTuran.NikolskiiSampling
noncomputable section

private theorem sum_product_norm_sq_le {M : ℕ} (a b : Fin M → ℂ) :
    ‖∑ k, a k * b k‖ ^ 2 ≤ (∑ k, ‖a k‖ ^ 2) * ∑ k, ‖b k‖ ^ 2 := by
  have h := norm_sum_le Finset.univ (fun k => a k * b k)
  simp only [norm_mul] at h
  exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
    (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr h).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖a k‖) (fun k => ‖b k‖))

/-- A finite convolution annihilator controls its first sample. -/
theorem endpoint_sq_le_of_annihilator {M : ℕ} (q f : Fin (M + 1) → ℂ)
    (hq0 : q 0 = 1) (hzero : ∑ k, q k * f k = 0) {κ : ℝ}
    (henergy : ∑ k, ‖q k‖ ^ 2 ≤ 1 + κ) :
    ‖f 0‖ ^ 2 ≤ κ * ∑ k : Fin M, ‖f k.succ‖ ^ 2 := by
  have htail : (∑ k : Fin M, q k.succ * f k.succ) = -f 0 := by
    rw [Fin.sum_univ_succ, hq0, one_mul] at hzero
    linear_combination hzero
  have hqtail : ∑ k : Fin M, ‖q k.succ‖ ^ 2 ≤ κ := by
    rw [Fin.sum_univ_succ, hq0, norm_one, one_pow] at henergy
    linarith
  have h := sum_product_norm_sq_le (fun k : Fin M => q k.succ)
    (fun k : Fin M => f k.succ)
  change ‖∑ k : Fin M, q k.succ * f k.succ‖ ^ 2 ≤
    (∑ k : Fin M, ‖q k.succ‖ ^ 2) * ∑ k : Fin M, ‖f k.succ‖ ^ 2 at h
  rw [htail, norm_neg] at h
  exact h.trans (mul_le_mul_of_nonneg_right hqtail
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- Rotate the zero of one unit-circle filter onto every sampled frequency. -/
def annihilatingPolynomial {n : ℕ} (H : ℂ[X]) (step : ℝ) (frequency : Fin n → ℝ) :
    ℂ[X] :=
  ∏ j, H.comp (C (Complex.exp (Complex.I * ((-step * frequency j : ℝ) : ℂ))) * X)

theorem annihilatingPolynomial_eval_zero {n : ℕ} (H : ℂ[X]) (hH : H.eval 0 = 1)
    (step : ℝ) (frequency : Fin n → ℝ) :
    (annihilatingPolynomial H step frequency).eval 0 = 1 := by
  rw [annihilatingPolynomial, Polynomial.eval_prod]
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, mul_zero, hH, Finset.prod_const_one]

theorem annihilatingPolynomial_natDegree {n m : ℕ} (H : ℂ[X])
    (hH : H.natDegree ≤ m) (step : ℝ) (frequency : Fin n → ℝ) :
    (annihilatingPolynomial H step frequency).natDegree ≤ n * m := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin n, m := by
      apply Finset.sum_le_sum
      intro j _
      apply Polynomial.natDegree_comp_le.trans
      have hlin : (C (Complex.exp (Complex.I * ((-step * frequency j : ℝ) : ℂ))) *
          X).natDegree ≤ 1 :=
        (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      exact (Nat.mul_le_mul hH hlin).trans (by simp)
    _ = _ := by simp

theorem annihilatingPolynomial_eval_phase {n : ℕ} (H : ℂ[X]) (hH : H.eval 1 = 0)
    (step : ℝ) (frequency : Fin n → ℝ) (j : Fin n) :
    (annihilatingPolynomial H step frequency).eval
      (Complex.exp (Complex.I * ((step * frequency j : ℝ) : ℂ))) = 0 := by
  classical
  rw [annihilatingPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hphase : Complex.exp (Complex.I * ((-step * frequency j : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((step * frequency j : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have he : Complex.I * ((-step * frequency j : ℝ) : ℂ) +
        Complex.I * ((step * frequency j : ℝ) : ℂ) = 0 := by push_cast; ring
    rw [he, Complex.exp_zero]
  rw [hphase]
  exact hH

theorem annihilatingPolynomial_circle_norm_le {n : ℕ} (H : ℂ[X])
    {B : ℝ} (_hB : 0 ≤ B)
    (hH : ∀ z : ℂ, ‖z‖ = 1 → ‖H.eval z‖ ≤ B)
    (step : ℝ) (frequency : Fin n → ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(annihilatingPolynomial H step frequency).eval z‖ ≤ B ^ n := by
  rw [annihilatingPolynomial, Polynomial.eval_prod, norm_prod]
  calc
    _ ≤ ∏ _j : Fin n, B := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro j _
      rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      apply hH
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, hz, one_mul]
    _ = _ := by simp

/-- Evaluation of a polynomial at the sampled phases annihilates the complete
sampled exponential sum, with no frequency distinctness assumption. -/
theorem polynomial_sampled_exponentialSum_eq_zero {n M : ℕ} (P : ℂ[X])
    (hdegree : P.natDegree ≤ M) (step : ℝ) (frequency : Fin n → ℝ)
    (c : Fin n → ℂ)
    (hroot : ∀ j, P.eval (Complex.exp (Complex.I * ((step * frequency j : ℝ) : ℂ))) = 0) :
    (∑ k : Fin (M + 1), P.coeff k.val *
      ExponentialSumEstimates.exponentialSum frequency c ((k.val : ℝ) * step)) = 0 := by
  unfold ExponentialSumEstimates.exponentialSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  have he (k : Fin (M + 1)) :
      Complex.exp (Complex.I * ((((k.val : ℝ) * step) * frequency j : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((step * frequency j : ℝ) : ℂ)) ^ k.val := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [he]
  have hrepr := Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdegree)
    (Complex.exp (Complex.I * ((step * frequency j : ℝ) : ℂ)))
  rw [← Fin.sum_univ_eq_sum_range] at hrepr
  calc
    _ = c j * ∑ k : Fin (M + 1), P.coeff k.val *
        Complex.exp (Complex.I * ((step * frequency j : ℝ) : ℂ)) ^ k.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = c j * P.eval (Complex.exp (Complex.I * ((step * frequency j : ℝ) : ℂ))) := by
      rw [hrepr]
    _ = 0 := by rw [hroot, mul_zero]

/-- The finite sampling estimate for an arbitrary polynomial filter.
The grid has `n*m` subintervals and includes its right endpoint. -/
theorem endpoint_sample_bound_of_filter {n m : ℕ} (H : ℂ[X])
    (hH0 : H.eval 0 = 1) (hH1 : H.eval 1 = 0) (hdegree : H.natDegree ≤ m)
    {B : ℝ} (hbound : ∀ z : ℂ, ‖z‖ = 1 → ‖H.eval z‖ ≤ B)
    (step : ℝ) (frequency : Fin n → ℝ) (c : Fin n → ℂ) :
    ‖ExponentialSumEstimates.exponentialSum frequency c 0‖ ^ 2 ≤
      (B ^ (2 * n) - 1) * ∑ k : Fin (n * m),
        ‖ExponentialSumEstimates.exponentialSum frequency c
          (((k.val : ℝ) + 1) * step)‖ ^ 2 := by
  let P := annihilatingPolynomial H step frequency
  have hPdegree : P.natDegree ≤ n * m := annihilatingPolynomial_natDegree H hdegree step frequency
  have hB : 0 ≤ B := (norm_nonneg (H.eval 1)).trans (hbound 1 (by simp))
  have hPcircle : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ B ^ n :=
    fun z hz => annihilatingPolynomial_circle_norm_le H hB hbound step frequency z hz
  have hcoeff := polynomial_coefficient_energy_le P hPdegree hPcircle
  have hpow : (B ^ n) ^ 2 = B ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
  rw [hpow] at hcoeff
  have hzero := polynomial_sampled_exponentialSum_eq_zero P hPdegree step frequency c
    (fun j => annihilatingPolynomial_eval_phase H hH1 step frequency j)
  have hfirst : P.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact annihilatingPolynomial_eval_zero H hH0 step frequency
  have h := endpoint_sq_le_of_annihilator
    (fun k : Fin (n * m + 1) => P.coeff k.val)
    (fun k : Fin (n * m + 1) =>
      ExponentialSumEstimates.exponentialSum frequency c ((k.val : ℝ) * step))
    hfirst hzero (κ := B ^ (2 * n) - 1) (by linarith)
  simpa only [Fin.val_zero, Nat.cast_zero, zero_mul, Fin.val_succ,
    Nat.cast_add, Nat.cast_one] using h

end
end LeanNumDetect.MultiTuran.NikolskiiSampling
