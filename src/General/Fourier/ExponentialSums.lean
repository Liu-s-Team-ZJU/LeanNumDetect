import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Exponential sums and unit-interval norms

These are mathematical definitions and elementary calculus facts; no external
estimate is assumed. The closed-interval supremum is the actual supremum.
-/

set_option autoImplicit false
open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LeanNumDetect.ExponentialSumEstimates
noncomputable section

def exponentialSum {s : ℕ} (frequency : Fin s → ℝ) (coefficient : Fin s → ℂ)
    (t : ℝ) : ℂ :=
  ∑ j, coefficient j * Complex.exp (Complex.I * ((t * frequency j : ℝ) : ℂ))

def unitSupNorm (f : ℝ → ℂ) : ℝ := sSup ((fun t => ‖f t‖) '' Icc (0 : ℝ) 1)

def unitLpNorm (p : ℝ≥0∞) (f : ℝ → ℂ) : ℝ :=
  if p = ∞ then unitSupNorm f
  else (∫ t in (0 : ℝ)..1, ‖f t‖ ^ p.toReal) ^ (1 / p.toReal)

def reciprocalExponent (p : ℝ≥0∞) : ℝ := if p = ∞ then 0 else 1 / p.toReal

def unitEnergy (f : ℝ → ℂ) : ℝ := ∫ t in (0 : ℝ)..1, ‖f t‖^2

theorem unitEnergy_nonneg (f : ℝ → ℂ) : 0 ≤ unitEnergy f := by
  apply intervalIntegral.integral_nonneg_of_forall
  · norm_num
  · intro t
    positivity

theorem continuous_exponentialSum {s : ℕ} (frequency : Fin s → ℝ)
    (coefficient : Fin s → ℂ) : Continuous (exponentialSum frequency coefficient) := by
  unfold exponentialSum
  fun_prop

theorem hasDerivAt_exponentialSum {s : ℕ} (frequency : Fin s → ℝ)
    (coefficient : Fin s → ℂ) (t : ℝ) :
    HasDerivAt (exponentialSum frequency coefficient)
      (∑ j, coefficient j *
        (Complex.exp (Complex.I * ((t * frequency j : ℝ) : ℂ)) *
          (Complex.I * (frequency j : ℂ)))) t := by
  unfold exponentialSum
  apply HasDerivAt.fun_sum
  intro j _
  simpa [Complex.ofReal_mul] using
    (((((hasDerivAt_id (t : ℂ)).mul_const (frequency j : ℂ)).const_mul
      Complex.I).cexp).comp_ofReal).const_mul (coefficient j)

theorem differentiable_exponentialSum {s : ℕ} (frequency : Fin s → ℝ)
    (coefficient : Fin s → ℂ) : Differentiable ℝ (exponentialSum frequency coefficient) :=
  fun t => (hasDerivAt_exponentialSum frequency coefficient t).differentiableAt

theorem continuous_deriv_exponentialSum {s : ℕ} (frequency : Fin s → ℝ)
    (coefficient : Fin s → ℂ) : Continuous (deriv (exponentialSum frequency coefficient)) := by
  have heq : deriv (exponentialSum frequency coefficient) =
      fun t => ∑ j, coefficient j *
        (Complex.exp (Complex.I * ((t * frequency j : ℝ) : ℂ)) *
          (Complex.I * (frequency j : ℂ))) := by
    funext t
    exact (hasDerivAt_exponentialSum frequency coefficient t).deriv
  rw [heq]
  fun_prop

theorem norm_le_unitSupNorm {f : ℝ → ℂ} (hf : Continuous f) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖f t‖ ≤ unitSupNorm f :=
  le_csSup (isCompact_Icc.bddAbove_image hf.norm.continuousOn) ⟨t, ht, rfl⟩

theorem unitSupNorm_nonneg {f : ℝ → ℂ} (hf : Continuous f) : 0 ≤ unitSupNorm f :=
  (norm_nonneg (f 0)).trans (norm_le_unitSupNorm hf (by simp))

theorem unitSupNorm_le {f : ℝ → ℂ} (_hf : Continuous f) {B : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ B) : unitSupNorm f ≤ B := by
  apply csSup_le
  · exact ⟨‖f 0‖, ⟨0, by simp, rfl⟩⟩
  · rintro z ⟨t, ht, rfl⟩
    exact hbound t ht

end
end LeanNumDetect.ExponentialSumEstimates
