/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The sinc-square Fejer kernel

This file proves the Fourier pair

  `𝓕 (x ↦ max (1 - |x|) 0) = x ↦ sinc (πx)^2`

with Mathlib's `e^{-2πi x ξ}` normalization, and uses Fourier inversion
to obtain the full-line integral and cosine support of the sinc-square
kernel.
-/

import MathExtras.Analysis.Fourier.FejerTriangle
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

noncomputable section

namespace MathExtras
namespace Fourier

open MeasureTheory
open scoped FourierTransform Real

/-- The real sinc-square kernel `x ↦ sinc(πx)^2`. -/
noncomputable def sincSqPi (x : ℝ) : ℝ :=
  (Real.sinc (Real.pi * x)) ^ 2

theorem sincSqPi_nonneg (x : ℝ) : 0 ≤ sincSqPi x := by
  dsimp [sincSqPi]
  exact sq_nonneg _

theorem sincSqPi_continuous : Continuous sincSqPi := by
  change Continuous (fun x : ℝ => (Real.sinc (Real.pi * x)) ^ 2)
  exact (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2

/-- The sinc-square kernel is even. -/
theorem sincSqPi_neg (x : ℝ) : sincSqPi (-x) = sincSqPi x := by
  unfold sincSqPi
  rw [show Real.pi * (-x) = -(Real.pi * x) by ring, Real.sinc_neg]

theorem sincSqPi_complex_continuous :
    Continuous (fun x : ℝ => (sincSqPi x : ℂ)) :=
  Complex.ofRealCLM.continuous.comp sincSqPi_continuous

theorem sincSqPi_le_one (x : ℝ) : sincSqPi x ≤ 1 := by
  dsimp [sincSqPi]
  have h := Real.abs_sinc_le_one (Real.pi * x)
  have hsq : (Real.sinc (Real.pi * x)) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    sq_le_sq' (by linarith [abs_le.mp h]) (by linarith [abs_le.mp h])
  simpa using hsq

theorem sincSqPi_le_inv_pi_sq_mul_sq {x : ℝ} (hx : x ≠ 0) :
    sincSqPi x ≤ (Real.pi ^ 2 * x ^ 2)⁻¹ := by
  dsimp [sincSqPi]
  have hπx : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
  have hπx_abs_pos : 0 < |Real.pi * x| := abs_pos.mpr hπx
  have hle : |Real.sinc (Real.pi * x)| ≤ |Real.pi * x|⁻¹ := by
    rw [Real.sinc_of_ne_zero hπx, abs_div]
    rw [show (|Real.pi * x|⁻¹ : ℝ) = 1 / |Real.pi * x| from by field_simp]
    exact (div_le_div_iff_of_pos_right hπx_abs_pos).mpr
      (Real.abs_sin_le_one (Real.pi * x))
  have hinv_nn : (0 : ℝ) ≤ |Real.pi * x|⁻¹ :=
    inv_nonneg.mpr (abs_nonneg _)
  have hsq :
      (Real.sinc (Real.pi * x)) ^ 2 ≤ (|Real.pi * x|⁻¹) ^ 2 := by
    rw [sq_le_sq]
    rw [abs_of_nonneg hinv_nn]
    exact hle
  refine hsq.trans ?_
  rw [inv_pow]
  rw [show |Real.pi * x| ^ 2 = (Real.pi * x) ^ 2 from sq_abs _]
  rw [show (Real.pi * x) ^ 2 = Real.pi ^ 2 * x ^ 2 from by ring]

theorem sincSqPi_le_four_div_one_add_sq (x : ℝ) :
    sincSqPi x ≤ 4 * (1 + x ^ 2)⁻¹ := by
  have h1x2_pos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  by_cases hxU : |x| ≤ 1
  · have hK := sincSqPi_le_one x
    have h1x2_le_two : 1 + x ^ 2 ≤ 2 := by
      have hx2 : x ^ 2 ≤ 1 := by
        rw [show (1 : ℝ) = 1 ^ 2 from by norm_num]
        exact sq_le_sq' (by linarith [abs_le.mp hxU]) (by linarith [abs_le.mp hxU])
      linarith
    have h_inv : (2 : ℝ)⁻¹ ≤ (1 + x ^ 2)⁻¹ :=
      inv_anti₀ h1x2_pos h1x2_le_two
    have h_4inv : (4 : ℝ) * (2 : ℝ)⁻¹ ≤ 4 * (1 + x ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left h_inv (by norm_num)
    have h_4inv_eq : (4 : ℝ) * (2 : ℝ)⁻¹ = 2 := by norm_num
    rw [h_4inv_eq] at h_4inv
    linarith
  · push Not at hxU
    have hx_ne : x ≠ 0 := by
      intro h
      rw [h, abs_zero] at hxU
      linarith
    have hxsq_pos : (0 : ℝ) < x ^ 2 := by positivity
    have hxsq_ge_one : (1 : ℝ) ≤ x ^ 2 := by
      have habs_sq : (1 : ℝ) ≤ |x| ^ 2 := by
        have hmul : |x| * 1 ≤ |x| * |x| :=
          mul_le_mul_of_nonneg_left hxU.le (abs_nonneg _)
        rw [mul_one] at hmul
        calc (1 : ℝ) ≤ |x| := hxU.le
          _ ≤ |x| * |x| := hmul
          _ = |x| ^ 2 := by ring
      rwa [← sq_abs]
    have hK := sincSqPi_le_inv_pi_sq_mul_sq hx_ne
    have hπ2_ge_one : (1 : ℝ) ≤ Real.pi ^ 2 := by
      have hπ_ge_one : (1 : ℝ) ≤ Real.pi :=
        le_of_lt (by linarith [Real.pi_gt_three])
      have hsq : (1 : ℝ) ^ 2 ≤ Real.pi ^ 2 :=
        sq_le_sq' (by linarith) hπ_ge_one
      simpa using hsq
    have hπ2x2_ge : x ^ 2 ≤ Real.pi ^ 2 * x ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hπ2_ge_one hxsq_pos.le
      simpa using h
    have h_inv_step1 : (Real.pi ^ 2 * x ^ 2)⁻¹ ≤ (x ^ 2)⁻¹ :=
      inv_anti₀ hxsq_pos hπ2x2_ge
    have hK1 : sincSqPi x ≤ (x ^ 2)⁻¹ := hK.trans h_inv_step1
    have h_step2 : (x ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [show ((x ^ 2)⁻¹ : ℝ) = 1 / x ^ 2 from by rw [one_div]]
      rw [show (2 * (1 + x ^ 2)⁻¹ : ℝ) = 2 / (1 + x ^ 2) from by
        rw [div_eq_mul_inv, mul_comm]]
      rw [div_le_div_iff₀ hxsq_pos h1x2_pos]
      linarith [hxsq_ge_one]
    have h_step3 : 2 * (1 + x ^ 2)⁻¹ ≤ 4 * (1 + x ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr h1x2_pos.le)
    linarith

theorem sincSqPi_integrable :
    Integrable sincSqPi MeasureTheory.volume := by
  have hmeas : AEStronglyMeasurable sincSqPi MeasureTheory.volume :=
    sincSqPi_continuous.aestronglyMeasurable
  have hdom : ∀ x : ℝ, ‖sincSqPi x‖ ≤ 4 * (1 + x ^ 2)⁻¹ := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sincSqPi_nonneg x)]
    exact sincSqPi_le_four_div_one_add_sq x
  exact Integrable.mono' (integrable_inv_one_add_sq.const_mul 4) hmeas
    (ae_of_all _ hdom)

theorem sincSqPi_complex_integrable :
    Integrable (fun x : ℝ => (sincSqPi x : ℂ)) MeasureTheory.volume :=
  sincSqPi_integrable.ofReal

private theorem hasDerivAt_exp_mul_one_sub_antideriv
    (c : ℂ) (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun y : ℝ => Complex.exp (c * (y : ℂ)) *
        (((1 : ℂ) - y) / c + 1 / c ^ 2))
      (Complex.exp (c * (t : ℂ)) * ((1 : ℂ) - t)) t := by
  have hof : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) (1 : ℂ) t := by
    exact Complex.ofRealCLM.hasDerivAt (x := t)
  have hexp : HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)))
      (Complex.exp (c * (t : ℂ)) * c) t := by
    have hlin : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c t := by
      simpa using hof.const_mul c
    simpa using hlin.cexp
  have hlinpart :
      HasDerivAt (fun y : ℝ => (((1 : ℂ) - y) / c + 1 / c ^ 2))
        (-(1 : ℂ) / c) t := by
    have hsub : HasDerivAt (fun y : ℝ => (1 : ℂ) - y) (-(1 : ℂ)) t := by
      refine ((hasDerivAt_const (x := t) (c := (1 : ℂ))).sub hof).congr_deriv ?_; ring
    have hdiv : HasDerivAt (fun y : ℝ => ((1 : ℂ) - y) / c)
        (-(1 : ℂ) / c) t := hsub.div_const c
    have hconst : HasDerivAt (fun _ : ℝ => (1 : ℂ) / c ^ 2) 0 t :=
      hasDerivAt_const _ _
    refine (hdiv.add hconst).congr_deriv ?_; ring
  have hmul := hexp.mul hlinpart
  refine hmul.congr_deriv ?_
  field_simp [hc]
  ring

private theorem hasDerivAt_exp_mul_one_add_antideriv
    (c : ℂ) (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun y : ℝ => Complex.exp (c * (y : ℂ)) *
        (((1 : ℂ) + y) / c - 1 / c ^ 2))
      (Complex.exp (c * (t : ℂ)) * ((1 : ℂ) + t)) t := by
  have hof : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) (1 : ℂ) t := by
    exact Complex.ofRealCLM.hasDerivAt (x := t)
  have hexp : HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ)))
      (Complex.exp (c * (t : ℂ)) * c) t := by
    have hlin : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c t := by
      simpa using hof.const_mul c
    simpa using hlin.cexp
  have hlinpart :
      HasDerivAt (fun y : ℝ => (((1 : ℂ) + y) / c - 1 / c ^ 2))
        ((1 : ℂ) / c) t := by
    have hadd : HasDerivAt (fun y : ℝ => (1 : ℂ) + y) (1 : ℂ) t := by
      refine ((hasDerivAt_const (x := t) (c := (1 : ℂ))).add hof).congr_deriv ?_; ring
    have hdiv : HasDerivAt (fun y : ℝ => ((1 : ℂ) + y) / c)
        ((1 : ℂ) / c) t := hadd.div_const c
    have hconst : HasDerivAt (fun _ : ℝ => (1 : ℂ) / c ^ 2) 0 t :=
      hasDerivAt_const _ _
    refine (hdiv.sub hconst).congr_deriv ?_; ring
  have hmul := hexp.mul hlinpart
  refine hmul.congr_deriv ?_
  field_simp [hc]
  ring

private theorem integral_exp_mul_one_sub (c : ℂ) (hc : c ≠ 0) :
    (∫ t in (0 : ℝ)..1, Complex.exp (c * (t : ℂ)) * ((1 : ℂ) - t)) =
      Complex.exp c / c ^ 2 - 1 / c - 1 / c ^ 2 := by
  let F : ℝ → ℂ :=
    fun y => Complex.exp (c * (y : ℂ)) *
      (((1 : ℂ) - y) / c + 1 / c ^ 2)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt F (Complex.exp (c * (t : ℂ)) * ((1 : ℂ) - t)) t := by
    intro t _
    exact hasDerivAt_exp_mul_one_sub_antideriv c hc t
  have hint : IntervalIntegrable
      (fun t : ℝ => Complex.exp (c * (t : ℂ)) * ((1 : ℂ) - t))
      volume 0 1 := by
    exact (by
      fun_prop :
        Continuous (fun t : ℝ =>
          Complex.exp (c * (t : ℂ)) * ((1 : ℂ) - t))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  dsimp [F] at h
  rw [h]
  simp [Complex.exp_zero]
  field_simp [hc]
  ring_nf

private theorem integral_exp_mul_one_add (c : ℂ) (hc : c ≠ 0) :
    (∫ t in (-1 : ℝ)..0, Complex.exp (c * (t : ℂ)) * ((1 : ℂ) + t)) =
      1 / c - 1 / c ^ 2 + Complex.exp (-c) / c ^ 2 := by
  let F : ℝ → ℂ :=
    fun y => Complex.exp (c * (y : ℂ)) *
      (((1 : ℂ) + y) / c - 1 / c ^ 2)
  have hderiv : ∀ t ∈ Set.uIcc (-1 : ℝ) 0,
      HasDerivAt F (Complex.exp (c * (t : ℂ)) * ((1 : ℂ) + t)) t := by
    intro t _
    exact hasDerivAt_exp_mul_one_add_antideriv c hc t
  have hint : IntervalIntegrable
      (fun t : ℝ => Complex.exp (c * (t : ℂ)) * ((1 : ℂ) + t))
      volume (-1) 0 := by
    exact (by
      fun_prop :
        Continuous (fun t : ℝ =>
          Complex.exp (c * (t : ℂ)) * ((1 : ℂ) + t))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  dsimp [F] at h
  rw [h]
  simp [Complex.exp_zero, div_eq_mul_inv]

private theorem support_exp_mul_fejerTriangle_subset_Ioc (c : ℂ) :
    Function.support
        (fun t : ℝ => Complex.exp (c * (t : ℂ)) * (fejerTriangle t : ℂ)) ⊆
      Set.Ioc (-1 : ℝ) 1 := by
  intro t ht
  have httri : fejerTriangle t ≠ 0 := by
    intro hzero
    exact ht (by simp [hzero])
  exact fejerTriangle_support_subset_Ioc httri

private theorem continuous_exp_mul_fejerTriangle (c : ℂ) :
    Continuous
      (fun t : ℝ => Complex.exp (c * (t : ℂ)) * (fejerTriangle t : ℂ)) := by
  have htri : Continuous (fun t : ℝ => (fejerTriangle t : ℂ)) :=
    Complex.ofRealCLM.continuous.comp fejerTriangle_continuous
  exact (by
    fun_prop :
      Continuous (fun t : ℝ => Complex.exp (c * (t : ℂ)))).mul htri

private theorem integral_exp_mul_fejerTriangle_neg_one_zero (c : ℂ) :
    (∫ t in (-1 : ℝ)..0,
        Complex.exp (c * (t : ℂ)) * (fejerTriangle t : ℂ)) =
      ∫ t in (-1 : ℝ)..0, Complex.exp (c * (t : ℂ)) * ((1 : ℂ) + t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  have htIcc : t ∈ Set.Icc (-1 : ℝ) 0 := by
    rwa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at ht
  change Complex.exp (c * (t : ℂ)) * (fejerTriangle t : ℂ) =
    Complex.exp (c * (t : ℂ)) * ((1 : ℂ) + t)
  rw [fejerTriangle_eq_one_add_of_neg_one_le_of_nonpos htIcc.2 htIcc.1]
  simp

private theorem integral_exp_mul_fejerTriangle_zero_one (c : ℂ) :
    (∫ t in (0 : ℝ)..1,
        Complex.exp (c * (t : ℂ)) * (fejerTriangle t : ℂ)) =
      ∫ t in (0 : ℝ)..1, Complex.exp (c * (t : ℂ)) * ((1 : ℂ) - t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  change Complex.exp (c * (t : ℂ)) * (fejerTriangle t : ℂ) =
    Complex.exp (c * (t : ℂ)) * ((1 : ℂ) - t)
  rw [fejerTriangle_eq_one_sub_of_nonneg_of_le_one htIcc.1 htIcc.2]
  simp

/-- The compact triangle has elementary complex exponential integral. -/
theorem integral_exp_mul_fejerTriangle (c : ℂ) (hc : c ≠ 0) :
    (∫ t : ℝ, Complex.exp (c * (t : ℂ)) * (fejerTriangle t : ℂ)) =
      (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
  let f : ℝ → ℂ :=
    fun t => Complex.exp (c * (t : ℂ)) * (fejerTriangle t : ℂ)
  have hsupport :=
    intervalIntegral.integral_eq_integral_of_support_subset
      (f := f) (μ := volume) (a := (-1 : ℝ)) (b := 1)
      (support_exp_mul_fejerTriangle_subset_Ioc c)
  have hleft : IntervalIntegrable f volume (-1) 0 :=
    (continuous_exp_mul_fejerTriangle c).intervalIntegrable _ _
  have hright : IntervalIntegrable f volume 0 1 :=
    (continuous_exp_mul_fejerTriangle c).intervalIntegrable _ _
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals
      (a := (-1 : ℝ)) (b := 0) (c := 1) hleft hright
  rw [← hsupport, ← hadd]
  dsimp [f]
  rw [integral_exp_mul_fejerTriangle_neg_one_zero,
    integral_exp_mul_fejerTriangle_zero_one]
  rw [integral_exp_mul_one_add c hc, integral_exp_mul_one_sub c hc]
  field_simp [hc]
  ring_nf

private theorem fejer_exp_num (x : ℝ) :
    Complex.exp (((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I) +
        Complex.exp (-(((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) - 2 =
      ((2 * Real.cos (2 * Real.pi * x) - 2 : ℝ) : ℂ) := by
  have hneg : -(((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    norm_num
  rw [hneg]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp [Real.cos_neg, Real.sin_neg]
  ring

private theorem fejer_exp_den (x : ℝ) :
    (((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I) ^ 2 =
      ((-(2 * Real.pi * x) ^ 2 : ℝ) : ℂ) := by
  rw [show ((((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I) ^ 2) =
      (((-2 * Real.pi * x : ℝ) : ℂ) ^ 2) * Complex.I ^ 2 by ring]
  rw [Complex.I_sq]
  norm_num

private theorem fejer_sinc_real_identity {x : ℝ} (hx : x ≠ 0) :
    (2 * Real.cos (2 * Real.pi * x) - 2) / (-(2 * Real.pi * x) ^ 2) =
      (Real.sinc (Real.pi * x)) ^ 2 := by
  have hπx : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
  rw [Real.sinc_of_ne_zero hπx]
  have hcos :
      Real.cos (2 * (Real.pi * x)) =
        1 - 2 * Real.sin (Real.pi * x) ^ 2 := by
    rw [Real.cos_two_mul]
    have hs := Real.sin_sq_add_cos_sq (Real.pi * x)
    nlinarith
  rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring]
  rw [hcos]
  field_simp [hπx]
  ring

private theorem fejer_exp_sinc_identity {x : ℝ} (hx : x ≠ 0) :
    (Complex.exp (((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I) +
        Complex.exp (-(((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) - 2) /
        (((-2 * Real.pi * x : ℝ) : ℂ) * Complex.I) ^ 2 =
      ((Real.sinc (Real.pi * x)) ^ 2 : ℂ) := by
  rw [fejer_exp_num x, fejer_exp_den x]
  rw [← Complex.ofReal_div]
  simpa [Complex.ofReal_pow] using
    congrArg (fun y : ℝ => (y : ℂ)) (fejer_sinc_real_identity hx)

/-- Fourier transform of the triangle: the sinc-square kernel. -/
theorem fourier_fejerTriangle_eq_sincSqPi (ξ : ℝ) :
    𝓕 (fun t : ℝ => (fejerTriangle t : ℂ)) ξ =
      (sincSqPi ξ : ℂ) := by
  by_cases hξ : ξ = 0
  · subst hξ
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp
    rw [show (∫ v : ℝ, (fejerTriangle v : ℂ)) =
        (((∫ v : ℝ, fejerTriangle v) : ℝ) : ℂ) from by
      exact (@integral_ofReal ℝ _ volume ℂ _ fejerTriangle)]
    rw [integral_fejerTriangle]
    norm_num [sincSqPi, Real.sinc_zero]
  · let c : ℂ := (((-2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)
    have hc : c ≠ 0 := by
      have hreal : (-2 * Real.pi * ξ : ℝ) ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hξ
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hreal) Complex.I_ne_zero
    rw [Real.fourier_real_eq_integral_exp_smul]
    calc
      (∫ t : ℝ,
          Complex.exp (↑(-2 * Real.pi * t * ξ) * Complex.I) *
            (fejerTriangle t : ℂ))
          = ∫ t : ℝ, Complex.exp (c * (t : ℂ)) * (fejerTriangle t : ℂ) := by
            apply integral_congr_ae
            filter_upwards with t
            dsimp [c]
            congr 2
            norm_num
            ring
      _ = (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 :=
            integral_exp_mul_fejerTriangle c hc
      _ = (sincSqPi ξ : ℂ) := by
            dsimp [c, sincSqPi]
            simpa [Complex.ofReal_pow] using fejer_exp_sinc_identity hξ

theorem fourierInv_fejerTriangle_eq_sincSqPi (ξ : ℝ) :
    𝓕⁻ (fun t : ℝ => (fejerTriangle t : ℂ)) ξ =
      (sincSqPi ξ : ℂ) := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_fejerTriangle_eq_sincSqPi]
  simp [sincSqPi, Real.sinc_neg, mul_neg]

/-- Fourier transform of the sinc-square kernel: the triangular profile. -/
theorem fourier_sincSqPi_eq_fejerTriangle :
    𝓕 (fun x : ℝ => (sincSqPi x : ℂ)) =
      fun ξ : ℝ => (fejerTriangle ξ : ℂ) := by
  let triC : ℝ → ℂ := fun x => (fejerTriangle x : ℂ)
  have htri_cont : Continuous triC :=
    Complex.ofRealCLM.continuous.comp fejerTriangle_continuous
  have htri_int : Integrable triC volume :=
    fejerTriangle_integrable.ofReal
  have hFint : Integrable (𝓕 triC) volume := by
    have hEq : 𝓕 triC = fun x : ℝ => (sincSqPi x : ℂ) := by
      ext x
      exact fourier_fejerTriangle_eq_sincSqPi x
    rw [hEq]
    exact sincSqPi_complex_integrable
  have hinv : 𝓕 (𝓕⁻ triC) = triC :=
    Continuous.fourier_fourierInv_eq htri_cont htri_int hFint
  have hfinv : 𝓕⁻ triC = fun x : ℝ => (sincSqPi x : ℂ) := by
    ext x
    exact fourierInv_fejerTriangle_eq_sincSqPi x
  rw [hfinv] at hinv
  simpa [triC] using hinv

/-- The sinc-square kernel has full Fourier support contained in `[-1, 1]`. -/
theorem sincSqPi_fourierSupportLe {ξ : ℝ} (hξ : 1 < |ξ|) :
    𝓕 (fun x : ℝ => (sincSqPi x : ℂ)) ξ = 0 := by
  rw [fourier_sincSqPi_eq_fejerTriangle]
  change (fejerTriangle ξ : ℂ) = 0
  rw [fejerTriangle_eq_zero_of_one_le_abs (le_of_lt hξ)]
  norm_num

theorem integral_sincSqPi :
    (∫ x : ℝ, sincSqPi x) = 1 := by
  have h0 := congrFun fourier_sincSqPi_eq_fejerTriangle 0
  rw [Real.fourier_real_eq_integral_exp_smul] at h0
  simp [fejerTriangle_zero] at h0
  rw [show (∫ v : ℝ, (sincSqPi v : ℂ)) =
      (((∫ v : ℝ, sincSqPi v) : ℝ) : ℂ) from by
    exact (@integral_ofReal ℝ _ volume ℂ _ sincSqPi)] at h0
  exact Complex.ofReal_inj.mp h0

theorem fourier_sincSqPi_re_eq_cosine (ξ : ℝ) :
    (𝓕 (fun x : ℝ => (sincSqPi x : ℂ)) ξ).re =
      ∫ x : ℝ, sincSqPi x * Real.cos (2 * Real.pi * ξ * x) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ v : ℝ,
      Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) *
        (sincSqPi v : ℂ)).re =
    ∫ x : ℝ, sincSqPi x * Real.cos (2 * Real.pi * ξ * x)
  have hInt :
      Integrable
        (fun v : ℝ =>
          Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) *
            (sincSqPi v : ℂ)) volume := by
    have hchar :
        Integrable
          (fun v : ℝ => 𝐞 (-inner ℝ v ξ) • (sincSqPi v : ℂ)) volume :=
      (Real.fourierIntegral_convergent_iff
        (E := ℂ) (f := fun v : ℝ => (sincSqPi v : ℂ)) ξ).mpr
        sincSqPi_complex_integrable
    convert hchar using 1
    ext v
    rw [Circle.smul_def, Real.fourierChar_apply]
    congr 1
    rw [show inner ℝ v ξ = ξ * v by simp]
    ring_nf
  calc
    (∫ v : ℝ,
        Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) *
          (sincSqPi v : ℂ)).re
        = ∫ v : ℝ,
            (Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) *
              (sincSqPi v : ℂ)).re := by
          exact (integral_re hInt).symm
    _ = ∫ x : ℝ, sincSqPi x * Real.cos (2 * Real.pi * ξ * x) := by
          apply integral_congr_ae
          filter_upwards with v
          rw [Complex.exp_ofReal_mul_I]
          change ((↑(Real.cos (-2 * Real.pi * v * ξ)) +
                ↑(Real.sin (-2 * Real.pi * v * ξ)) * Complex.I) *
              (((Real.sinc (Real.pi * v)) ^ 2 : ℝ) : ℂ)).re =
            (Real.sinc (Real.pi * v)) ^ 2 * Real.cos (2 * Real.pi * ξ * v)
          simp [Real.cos_neg, Real.sin_neg, -Complex.ofReal_cos,
            -Complex.ofReal_sin, -Complex.ofReal_pow]
          ring_nf

/-- Exact real cosine-transform form of the sinc-square Fourier pair. -/
theorem integral_sincSqPi_mul_cos_eq_fejerTriangle (ξ : ℝ) :
    (∫ x : ℝ, sincSqPi x * Real.cos (2 * Real.pi * ξ * x)) =
      fejerTriangle ξ := by
  have hfour := congrFun fourier_sincSqPi_eq_fejerTriangle ξ
  have hre := congrArg Complex.re hfour
  rw [fourier_sincSqPi_re_eq_cosine ξ] at hre
  simpa using hre

/-- The sinc-square kernel is sine-orthogonal at every real frequency. -/
theorem integral_sincSqPi_mul_sin_eq_zero (ξ : ℝ) :
    (∫ x : ℝ, sincSqPi x * Real.sin (2 * Real.pi * ξ * x)) = 0 := by
  set f : ℝ → ℝ := fun x => sincSqPi x * Real.sin (2 * Real.pi * ξ * x) with hf
  have hodd : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    simp only [hf]
    rw [sincSqPi_neg]
    rw [show 2 * Real.pi * ξ * (-x) = -(2 * Real.pi * ξ * x) by ring,
      Real.sin_neg]
    ring
  have hmp := MeasureTheory.Measure.measurePreserving_neg
    (MeasureTheory.volume : MeasureTheory.Measure ℝ)
  have hcomp : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := by
    have :=
      MeasureTheory.MeasurePreserving.integral_comp'
        (f := (Homeomorph.neg ℝ).toMeasurableEquiv) hmp f
    simpa [Homeomorph.neg, Equiv.neg, MeasurableEquiv.coe_mk,
      Function.comp_def] using this
  have heq : (∫ x : ℝ, f x) = -(∫ x : ℝ, f x) := by
    calc (∫ x : ℝ, f x)
        = ∫ x : ℝ, f (-x) := hcomp.symm
      _ = ∫ x : ℝ, -f x := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun x => hodd x)
      _ = -(∫ x : ℝ, f x) := MeasureTheory.integral_neg _
  have hzero : (∫ x : ℝ, f x) = 0 := by linarith
  simpa [hf] using hzero

theorem sincSqPi_cosineFourierSupportLe :
    ∀ {ξ : ℝ}, 1 < |ξ| →
      (∫ x : ℝ, sincSqPi x * Real.cos (2 * Real.pi * ξ * x)) = 0 := by
  intro ξ hξ
  rw [integral_sincSqPi_mul_cos_eq_fejerTriangle ξ,
    fejerTriangle_eq_zero_of_one_le_abs hξ.le]

end Fourier
end MathExtras
