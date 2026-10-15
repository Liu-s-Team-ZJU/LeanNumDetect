import MultiTuran.Nikolskii
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual interval inner products and integration by parts for finite
exponential sums. These are the analytic ingredients of the finite-dimensional
Bernstein argument. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexConjugate
open Set MeasureTheory
open LeanNumDetect.ExponentialSumEstimates

namespace LeanNumDetect.MultiTuran.ExponentialInterval
noncomputable section

theorem exponentialSum_add_coefficients {n : ℕ} (frequency : Fin n → ℝ)
    (a b : Fin n → ℂ) (t : ℝ) :
    exponentialSum frequency (a+b) t = exponentialSum frequency a t + exponentialSum frequency b t := by
  simp only [exponentialSum, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem exponentialSum_smul_coefficients {n : ℕ} (frequency : Fin n → ℝ)
    (z : ℂ) (a : Fin n → ℂ) (t : ℝ) :
    exponentialSum frequency (z • a) t = z*exponentialSum frequency a t := by
  simp only [exponentialSum, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- The actual complex `L²(0,1)` inner product of two exponential sums. -/
def coefficientInner {n : ℕ} (frequency : Fin n → ℝ) (a b : Fin n → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, conj (exponentialSum frequency a t) * exponentialSum frequency b t

theorem continuous_coefficientInner_integrand {n : ℕ} (frequency : Fin n → ℝ)
    (a b : Fin n → ℂ) :
    Continuous (fun t => conj (exponentialSum frequency a t) * exponentialSum frequency b t) :=
  (continuous_exponentialSum frequency a).star.mul (continuous_exponentialSum frequency b)

@[simp] theorem coefficientInner_self {n : ℕ} (frequency : Fin n → ℝ)
    (a : Fin n → ℂ) :
    coefficientInner frequency a a = (unitEnergy (exponentialSum frequency a) : ℂ) := by
  unfold coefficientInner unitEnergy
  have he (t : ℝ) : conj (exponentialSum frequency a t) * exponentialSum frequency a t =
      ((‖exponentialSum frequency a t‖^2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp_rw [he]
  exact intervalIntegral.integral_ofReal

@[simp] theorem coefficientInner_conj_symm {n : ℕ} (frequency : Fin n → ℝ)
    (a b : Fin n → ℂ) : conj (coefficientInner frequency b a) = coefficientInner frequency a b := by
  unfold coefficientInner intervalIntegral
  simp only [← integral_conj, map_sub, map_mul]
  congr 1 <;> apply integral_congr_ae <;>
    exact Filter.Eventually.of_forall (fun t => by simp [mul_comm])

@[simp] theorem coefficientInner_add_left {n : ℕ} (frequency : Fin n → ℝ)
    (a b c : Fin n → ℂ) :
    coefficientInner frequency (a+b) c = coefficientInner frequency a c + coefficientInner frequency b c := by
  unfold coefficientInner
  simp_rw [exponentialSum_add_coefficients, map_add, add_mul]
  exact intervalIntegral.integral_add
    ((continuous_coefficientInner_integrand frequency a c).intervalIntegrable _ _)
    ((continuous_coefficientInner_integrand frequency b c).intervalIntegrable _ _)

@[simp] theorem coefficientInner_smul_left {n : ℕ} (frequency : Fin n → ℝ)
    (a b : Fin n → ℂ) (z : ℂ) :
    coefficientInner frequency (z • a) b = conj z * coefficientInner frequency a b := by
  unfold coefficientInner
  simp_rw [exponentialSum_smul_coefficients, map_mul, mul_assoc]
  exact intervalIntegral.integral_const_mul _ _

/-- On the unit interval the true integral energy is bounded by the actual
closed-interval supremum squared. -/
theorem unitEnergy_le_unitSupNorm_sq {n : ℕ} (frequency : Fin n → ℝ)
    (c : Fin n → ℂ) :
    unitEnergy (exponentialSum frequency c) ≤ unitSupNorm (exponentialSum frequency c)^2 := by
  have hf := continuous_exponentialSum frequency c
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (hf.norm.pow 2 |>.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    (g := fun _ => unitSupNorm (exponentialSum frequency c)^2)
    (fun t ht => (sq_le_sq₀ (norm_nonneg _) (unitSupNorm_nonneg hf)).mpr
      (norm_le_unitSupNorm hf ht))
  change (∫ t in (0 : ℝ)..1, ‖exponentialSum frequency c t‖^2) ≤ _
  simpa only [Pi.pow_apply, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] using h

/-- The true integration-by-parts boundary identity. -/
theorem exponentialSum_boundary_form {n : ℕ} (frequency : Fin n → ℝ)
    (a b : Fin n → ℂ) :
    (∫ t in (0 : ℝ)..1,
      conj (deriv (exponentialSum frequency a) t) * exponentialSum frequency b t) +
    (∫ t in (0 : ℝ)..1,
      conj (exponentialSum frequency a t) * deriv (exponentialSum frequency b) t) =
    conj (exponentialSum frequency a 1) * exponentialSum frequency b 1 -
      conj (exponentialSum frequency a 0) * exponentialSum frequency b 0 := by
  let f := exponentialSum frequency a
  let g := exponentialSum frequency b
  have hfc := continuous_exponentialSum frequency a
  have hgc := continuous_exponentialSum frequency b
  have hf' := continuous_deriv_exponentialSum frequency a
  have hg' := continuous_deriv_exponentialSum frequency b
  have hder (t : ℝ) : HasDerivAt (fun x => conj (f x)*g x)
      (conj (deriv f t)*g t + conj (f t)*deriv g t) t := by
    have hfa := (differentiable_exponentialSum frequency a t).hasDerivAt.star
    have hga := (differentiable_exponentialSum frequency b t).hasDerivAt
    convert hfa.mul hga using 1 <;> rfl
  have hint1 : IntervalIntegrable (fun t => conj (deriv f t)*g t) volume 0 1 :=
    (hf'.star.mul hgc).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t => conj (f t)*deriv g t) volume 0 1 :=
    (hfc.star.mul hg').intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) (hint1.add hint2)
  rw [intervalIntegral.integral_add hint1 hint2] at h
  exact h

end
end LeanNumDetect.MultiTuran.ExponentialInterval
