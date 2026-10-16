import General.Fourier.ExponentialSums
import Mathlib.Tactic

/-! # Actual first-order pruning of imaginary exponential sums

The operators here are literal scalar derivatives. Removing one indexed term
does not require distinct frequencies or nonzero coefficients. The algebra is
the imaginary-spectrum version of Section 4 of arXiv:2606.24823.
-/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran
noncomputable section

open ExponentialSumEstimates

/-- The genuine normalized first-order pruning operator `(D-iλ_a)/ρ`. -/
def prunedExponentialSum {n : ℕ} (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    (a : Fin n) (ρ : ℝ) (t : ℝ) : ℂ :=
  (deriv (ExponentialSumEstimates.exponentialSum frequency c) t -
    (Complex.I * (frequency a : ℂ)) *
      ExponentialSumEstimates.exponentialSum frequency c t) / (ρ : ℂ)

/-- The coefficients after the selected indexed term has been removed. -/
def prunedCoefficients {n : ℕ} (frequency : Fin (n+1) → ℝ)
    (c : Fin (n+1) → ℂ) (a : Fin (n+1)) (ρ : ℝ) : Fin n → ℂ :=
  fun j => (Complex.I * ((frequency (a.succAbove j)-frequency a : ℝ) : ℂ) /
    (ρ : ℂ)) * c (a.succAbove j)

/-- Pruning has a presentation with exactly one fewer indexed term. -/
theorem prunedExponentialSum_eq_sum {n : ℕ} (frequency : Fin (n+1) → ℝ)
    (c : Fin (n+1) → ℂ) (a : Fin (n+1)) (ρ t : ℝ) :
    prunedExponentialSum frequency c a ρ t =
      ExponentialSumEstimates.exponentialSum (fun j => frequency (a.succAbove j))
        (prunedCoefficients frequency c a ρ) t := by
  have hall : prunedExponentialSum frequency c a ρ t =
      ∑ j, (Complex.I * ((frequency j-frequency a : ℝ) : ℂ) / (ρ : ℂ)) *
        c j * Complex.exp (Complex.I * ((t*frequency j : ℝ) : ℂ)) := by
    unfold prunedExponentialSum
    rw [(ExponentialSumEstimates.hasDerivAt_exponentialSum frequency c t).deriv]
    unfold ExponentialSumEstimates.exponentialSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [hall, Fin.sum_univ_succAbove _ a]
  simp only [sub_self, Complex.ofReal_zero, mul_zero, zero_div, zero_mul, zero_add]
  rfl

/-- Two pruning operators recover their frequency difference times the
original exponential sum. The identity remains true at `ρ=0`. -/
theorem prunedExponentialSum_sub {n : ℕ} (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    (a b : Fin n) (ρ t : ℝ) :
    prunedExponentialSum frequency c a ρ t - prunedExponentialSum frequency c b ρ t =
      (Complex.I * ((frequency b-frequency a : ℝ) : ℂ) / (ρ : ℂ)) *
        ExponentialSumEstimates.exponentialSum frequency c t := by
  unfold prunedExponentialSum
  push_cast
  ring

/-- Farthest spectral points give the pointwise triangle bound used in the
geometric-mean induction, with no multiplicative loss. -/
theorem norm_exponentialSum_le_pruned_pair {n : ℕ}
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) (a b : Fin n)
    {ρ : ℝ} (hρ : 0 < ρ) (hgap : |frequency b-frequency a| = ρ) (t : ℝ) :
    ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ≤
      ‖prunedExponentialSum frequency c a ρ t‖ +
        ‖prunedExponentialSum frequency c b ρ t‖ := by
  have hfactor : ‖Complex.I * ((frequency b-frequency a : ℝ) : ℂ) / (ρ : ℂ)‖ = 1 := by
    simp only [norm_div, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul, hgap, abs_of_pos hρ, div_self (ne_of_gt hρ)]
  calc
    _ = ‖prunedExponentialSum frequency c a ρ t -
        prunedExponentialSum frequency c b ρ t‖ := by
      rw [prunedExponentialSum_sub, norm_mul, hfactor, one_mul]
    _ ≤ _ := norm_sub_le _ _

/-- If the original function is identically zero then every genuine pruning
is identically zero, including for arbitrary repeated coefficient presentations. -/
theorem prunedExponentialSum_eq_zero_of_zero {n : ℕ} (frequency : Fin n → ℝ)
    (c : Fin n → ℂ) (a : Fin n) (ρ : ℝ)
    (hzero : ExponentialSumEstimates.exponentialSum frequency c = 0) :
    prunedExponentialSum frequency c a ρ = 0 := by
  funext t
  simp [prunedExponentialSum, hzero]

/-- Modulating by a purely imaginary frequency changes the spectrum by a
real translation and preserves every pointwise modulus. -/
theorem exponentialSum_frequency_sub {n : ℕ} (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    (a t : ℝ) :
    ExponentialSumEstimates.exponentialSum (fun j => frequency j-a) c t =
      Complex.exp (Complex.I * ((-t*a : ℝ) : ℂ)) *
        ExponentialSumEstimates.exponentialSum frequency c t := by
  unfold ExponentialSumEstimates.exponentialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : Complex.exp (Complex.I * ((t*(frequency j-a) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((-t*a : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((t*frequency j : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

theorem norm_exponentialSum_frequency_sub {n : ℕ} (frequency : Fin n → ℝ)
    (c : Fin n → ℂ) (a t : ℝ) :
    ‖ExponentialSumEstimates.exponentialSum (fun j => frequency j-a) c t‖ =
      ‖ExponentialSumEstimates.exponentialSum frequency c t‖ := by
  rw [exponentialSum_frequency_sub, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

end
end LeanNumDetect.MultiTuran
