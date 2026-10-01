import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Explicit rates for bounded atomic sampling

These scalar inequalities absorb the accuracy rescaling in a bounded-row
concentration theorem and the prefactor introduced by convex hinge transfer.
The constants depend only on the source theorem's numerical constants.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section

/-- A fixed accuracy rescaling compatible with the source theorem and a
deviation threshold of one quarter of the requested accuracy. -/
def boundedAtomicAccuracyScale (κ c₁ : ℝ) : ℝ :=
  min (κ / 2) (min (1 / (4 * c₁)) (1 / 2))

/-- The entropy term in the sufficient bounded-atomic sampling rate. -/
def boundedAtomicEntropyFactor (S Q ρ : ℝ) : ℝ :=
  (1 + Real.log Q) * (1 + Real.log (S / ρ)) ^ 2

/-- The entropy and failure-probability terms in that rate. -/
def boundedAtomicSamplingLogFactor (S Q ρ η : ℝ) : ℝ :=
  boundedAtomicEntropyFactor S Q ρ + Real.log (2 / η)

/-- An explicit constant sufficient for both source concentration and
the tail prefactor incurred by sampling without replacement. -/
def boundedAtomicSamplingConstant (c₀ θ : ℝ) : ℝ :=
  (c₀ * (1 + Real.log (1 / θ)) ^ 2 + 4) / θ ^ 2

theorem boundedAtomicAccuracyScale_pos {κ c₁ : ℝ} (hκ : 0 < κ) (hc₁ : 0 < c₁) :
    0 < boundedAtomicAccuracyScale κ c₁ := by
  unfold boundedAtomicAccuracyScale
  positivity

theorem boundedAtomicAccuracyScale_le_half (κ c₁ : ℝ) :
    boundedAtomicAccuracyScale κ c₁ ≤ 1 / 2 :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem boundedAtomic_scaled_accuracy_bounds {κ c₁ ρ : ℝ}
    (hκ : 0 < κ) (hc₁ : 0 < c₁) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    0 < boundedAtomicAccuracyScale κ c₁ * ρ ∧
      boundedAtomicAccuracyScale κ c₁ * ρ < κ ∧
      4 * c₁ * (boundedAtomicAccuracyScale κ c₁ * ρ) ≤ ρ := by
  let θ := boundedAtomicAccuracyScale κ c₁
  have hθ0 : 0 < θ := boundedAtomicAccuracyScale_pos hκ hc₁
  have hθκ : θ ≤ κ / 2 := min_le_left _ _
  have hθc : θ ≤ 1 / (4 * c₁) := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨mul_pos hθ0 hρ0, ?_, ?_⟩
  · have hmul : θ * ρ < θ := by nlinarith
    linarith
  · have hprod : (4 * c₁) * θ ≤ 1 := by
      simpa only [mul_comm] using
        (le_div_iff₀ (by positivity : 0 < 4 * c₁)).mp hθc
    calc
      4 * c₁ * (θ * ρ) = ((4 * c₁) * θ) * ρ := by ring
      _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hprod hρ0.le
      _ = ρ := one_mul _

theorem boundedAtomicSamplingConstant_pos {c₀ θ : ℝ} (hc₀ : 0 ≤ c₀) (hθ : 0 < θ) :
    0 < boundedAtomicSamplingConstant c₀ θ := by
  unfold boundedAtomicSamplingConstant
  positivity

theorem boundedAtomic_entropy_nonneg {S Q ρ : ℝ} (hS : 1 ≤ S) (hQ : 1 ≤ Q)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    0 ≤ Real.log (S / ρ) ∧ 1 ≤ boundedAtomicEntropyFactor S Q ρ := by
  have hv : 0 ≤ Real.log (S / ρ) := Real.log_nonneg
    ((one_le_div hρ0).mpr (hρ1.trans hS))
  have hq : 0 ≤ Real.log Q := Real.log_nonneg hQ
  refine ⟨hv, ?_⟩
  unfold boundedAtomicEntropyFactor
  have hs : 1 ≤ (1 + Real.log (S / ρ)) ^ 2 := by nlinarith
  nlinarith [mul_nonneg hq (sq_nonneg (1 + Real.log (S / ρ)))]

/-- Rescaling accuracy by a fixed `θ ≤ 1` changes only the universal
constant in the squared logarithmic source rate. -/
theorem boundedAtomic_source_entropy_le {S Q ρ θ : ℝ}
    (hS : 1 ≤ S) (hQ : 1 ≤ Q) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    Real.log (Real.exp 1 * Q) * Real.log (S / (θ * ρ)) ^ 2 ≤
      (1 + Real.log (1 / θ)) ^ 2 * boundedAtomicEntropyFactor S Q ρ := by
  have hS0 : 0 < S := by linarith
  have hQ0 : 0 < Q := by linarith
  have hv := (boundedAtomic_entropy_nonneg hS hQ hρ0 hρ1).1
  have hu : 0 ≤ Real.log (1 / θ) :=
    Real.log_nonneg ((one_le_div hθ0).mpr hθ1)
  have hlog : Real.log (S / (θ * ρ)) = Real.log (S / ρ) + Real.log (1 / θ) := by
    rw [show S / (θ * ρ) = (S / ρ) / θ by ring,
      Real.log_div (div_pos hS0 hρ0).ne' hθ0.ne']
    simp [one_div, Real.log_inv, sub_eq_add_neg]
  have hsum : 0 ≤ Real.log (S / ρ) + Real.log (1 / θ) := add_nonneg hv hu
  have hle : Real.log (S / ρ) + Real.log (1 / θ) ≤
      (1 + Real.log (1 / θ)) * (1 + Real.log (S / ρ)) := by
    nlinarith [mul_nonneg hu hv]
  have hsq := pow_le_pow_left₀ hsum hle 2
  rw [Real.log_mul (Real.exp_pos 1).ne' hQ0.ne', Real.log_exp, hlog]
  unfold boundedAtomicEntropyFactor
  have hq0 : 0 ≤ 1 + Real.log Q := by linarith [Real.log_nonneg hQ]
  calc
    _ ≤ (1 + Real.log Q) *
        ((1 + Real.log (1 / θ)) * (1 + Real.log (S / ρ))) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hq0
    _ = _ := by ring

/-- The sufficient rate dominates the original bounded-row source rate. -/
theorem boundedAtomic_source_rate_le_of_sampleRate {S Q ρ η θ c₀ m : ℝ}
    (hS : 1 ≤ S) (hQ : 1 ≤ Q) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hc₀ : 0 ≤ c₀)
    (hrate : boundedAtomicSamplingConstant c₀ θ * S / ρ ^ 2 *
      boundedAtomicSamplingLogFactor S Q ρ η ≤ m) :
    c₀ * S / (θ * ρ) ^ 2 *
      (Real.log (Real.exp 1 * Q) * Real.log (S / (θ * ρ)) ^ 2) ≤ m := by
  have hS0 : 0 < S := by linarith
  have hlogη : 0 ≤ Real.log (2 / η) :=
    Real.log_nonneg ((one_le_div hη0).mpr (by linarith))
  have hA0 := (boundedAtomic_entropy_nonneg hS hQ hρ0 hρ1).2
  have hC0 := boundedAtomicSamplingConstant_pos hc₀ hθ0
  have hs := boundedAtomic_source_entropy_le hS hQ hρ0 hρ1 hθ0 hθ1
  have hC : c₀ * (1 + Real.log (1 / θ)) ^ 2 / θ ^ 2 ≤
      boundedAtomicSamplingConstant c₀ θ := by
    unfold boundedAtomicSamplingConstant
    apply div_le_div_of_nonneg_right _ (sq_nonneg θ)
    linarith
  calc
    _ ≤ c₀ * S / (θ * ρ) ^ 2 *
        ((1 + Real.log (1 / θ)) ^ 2 * boundedAtomicEntropyFactor S Q ρ) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (c₀ * (1 + Real.log (1 / θ)) ^ 2 / θ ^ 2) *
        S / ρ ^ 2 * boundedAtomicEntropyFactor S Q ρ := by ring
    _ ≤ boundedAtomicSamplingConstant c₀ θ * S / ρ ^ 2 *
        boundedAtomicEntropyFactor S Q ρ := by gcongr
    _ ≤ boundedAtomicSamplingConstant c₀ θ * S / ρ ^ 2 *
        boundedAtomicSamplingLogFactor S Q ρ η :=
      mul_le_mul_of_nonneg_left (by unfold boundedAtomicSamplingLogFactor; linarith)
        (by positivity)
    _ ≤ m := hrate

/-- A simple logarithmic bound for the prefactor generated by hinge
transfer; its cost is already contained in the entropy term. -/
theorem boundedAtomic_hinge_prefactor_log_le {S Q ρ : ℝ}
    (hS : 1 ≤ S) (hQ : 1 ≤ Q) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Real.log (8 * S / ρ) ≤ 3 * boundedAtomicEntropyFactor S Q ρ := by
  have hS0 : 0 < S := by linarith
  have hv := (boundedAtomic_entropy_nonneg hS hQ hρ0 hρ1).1
  have hq : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog8 : Real.log 8 ≤ 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith
  rw [show 8 * S / ρ = 8 * (S / ρ) by ring,
    Real.log_mul (by norm_num) (div_pos hS0 hρ0).ne']
  unfold boundedAtomicEntropyFactor
  nlinarith [mul_nonneg hq (sq_nonneg (1 + Real.log (S / ρ)))]

/-- The same rate absorbs the exact exponential failure prefactor
`8S/ρ` resulting from convex hinge transfer. -/
theorem boundedAtomic_hinge_tail_le_of_sampleRate {S Q ρ η θ c₀ m : ℝ}
    (hS : 1 ≤ S) (hQ : 1 ≤ Q) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hθ0 : 0 < θ)
    (hc₀ : 0 ≤ c₀)
    (hrate : boundedAtomicSamplingConstant c₀ θ * S / ρ ^ 2 *
      boundedAtomicSamplingLogFactor S Q ρ η ≤ m) :
    (8 * S / ρ) * Real.exp (-((θ * ρ) ^ 2 * m / S)) ≤ η := by
  have hS0 : 0 < S := by linarith
  have hρ2 : 0 < ρ ^ 2 := pow_pos hρ0 2
  have hA := (boundedAtomic_entropy_nonneg hS hQ hρ0 hρ1).2
  have hL : 0 ≤ Real.log (2 / η) :=
    Real.log_nonneg ((one_le_div hη0).mpr (by linarith))
  have hC : 4 ≤ θ ^ 2 * boundedAtomicSamplingConstant c₀ θ := by
    unfold boundedAtomicSamplingConstant
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 hθ0.ne')]
    nlinarith [mul_nonneg hc₀ (sq_nonneg (1 + Real.log (1 / θ)))]
  have hexp : 4 * boundedAtomicSamplingLogFactor S Q ρ η ≤ (θ * ρ) ^ 2 * m / S := by
    have hmul := mul_le_mul_of_nonneg_left hrate (by positivity : 0 ≤ θ ^ 2 * ρ ^ 2 / S)
    have hcancel : (θ ^ 2 * ρ ^ 2 / S) *
        (boundedAtomicSamplingConstant c₀ θ * S / ρ ^ 2 *
          boundedAtomicSamplingLogFactor S Q ρ η) =
        (θ ^ 2 * boundedAtomicSamplingConstant c₀ θ) *
          boundedAtomicSamplingLogFactor S Q ρ η := by field_simp
    rw [hcancel] at hmul
    calc
      _ ≤ (θ ^ 2 * boundedAtomicSamplingConstant c₀ θ) *
          boundedAtomicSamplingLogFactor S Q ρ η :=
        mul_le_mul_of_nonneg_right hC (by unfold boundedAtomicSamplingLogFactor; linarith)
      _ ≤ (θ ^ 2 * ρ ^ 2 / S) * m := hmul
      _ = _ := by ring
  have hpref := boundedAtomic_hinge_prefactor_log_le hS hQ hρ0 hρ1
  have hlogη : Real.log (1 / η) ≤ Real.log (2 / η) :=
    Real.log_le_log (by positivity) (by gcongr; norm_num)
  have hlogsum : Real.log (8 * S / ρ) + Real.log (1 / η) ≤ (θ * ρ) ^ 2 * m / S := by
    unfold boundedAtomicSamplingLogFactor at hexp
    linarith
  have hbound : Real.exp (-((θ * ρ) ^ 2 * m / S)) ≤ η / (8 * S / ρ) := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < η / (8 * S / ρ))).mp
    rw [Real.log_div hη0.ne' (by positivity)]
    rw [one_div, Real.log_inv] at hlogsum
    linarith
  exact (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq
    (mul_div_cancel₀ η (by positivity : 8 * S / ρ ≠ 0))

/-- Universal-constant form used to instantiate a bounded-row source
theorem. The one rate gives the admissible source accuracy, the requested
deviation threshold, the source sample size, and the final hinge tail. -/
theorem boundedAtomic_universal_rate {κ c₀ c₁ : ℝ}
    (hκ : 0 < κ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S Q ρ η m : ℝ),
      1 ≤ S → 1 ≤ Q → 0 < ρ → ρ < 1 → 0 < η → η < 1 →
      C * S / ρ ^ 2 * boundedAtomicSamplingLogFactor S Q ρ η ≤ m →
      let δ := boundedAtomicAccuracyScale κ c₁ * ρ
      0 < δ ∧ δ < κ ∧ 2 * c₁ * δ ≤ ρ / 2 ∧
        c₀ * S / δ ^ 2 *
          (Real.log (Real.exp 1 * Q) * Real.log (S / δ) ^ 2) ≤ m ∧
        (8 * S / ρ) * Real.exp (-(δ ^ 2 * m / S)) ≤ η := by
  let θ := boundedAtomicAccuracyScale κ c₁
  have hθ0 : 0 < θ := boundedAtomicAccuracyScale_pos hκ hc₁
  have hθ1 : θ ≤ 1 := (boundedAtomicAccuracyScale_le_half κ c₁).trans (by norm_num)
  refine ⟨boundedAtomicSamplingConstant c₀ θ,
    boundedAtomicSamplingConstant_pos hc₀.le hθ0, ?_⟩
  intro S Q ρ η m hS hQ hρ0 hρ1 hη0 hη1 hrate
  have hδ := boundedAtomic_scaled_accuracy_bounds hκ hc₁ hρ0 hρ1
  refine ⟨hδ.1, hδ.2.1, ?_, ?_, ?_⟩
  · linarith [hδ.2.2]
  · exact boundedAtomic_source_rate_le_of_sampleRate hS hQ hρ0 hρ1.le
      hη0 hη1.le hθ0 hθ1 hc₀.le hrate
  · exact boundedAtomic_hinge_tail_le_of_sampleRate hS hQ hρ0 hρ1.le
      hη0 hη1.le hθ0 hc₀.le hrate

end

end LeanNumDetect.FiniteMatrixSampling
