/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The triangular Fejer profile

This file isolates the compactly supported triangle

  `x ↦ max (1 - |x|) 0`,

the Fourier-side profile of the sinc-square Fejer kernel
`(sin (πx) / (πx))^2`.
-/

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

noncomputable section

namespace MathExtras
namespace Fourier

open MeasureTheory
open scoped Real

/-- The triangular Fejer profile `max (1 - |x|) 0`. -/
noncomputable def fejerTriangle (x : ℝ) : ℝ :=
  max (1 - |x|) 0

@[simp] theorem fejerTriangle_zero : fejerTriangle 0 = 1 := by
  simp [fejerTriangle]

theorem fejerTriangle_nonneg (x : ℝ) : 0 ≤ fejerTriangle x := by
  unfold fejerTriangle
  exact le_max_right _ _

theorem fejerTriangle_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    fejerTriangle x = 0 := by
  unfold fejerTriangle
  rw [max_eq_right]
  linarith

theorem fejerTriangle_eq_one_sub_abs_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    fejerTriangle x = 1 - |x| := by
  unfold fejerTriangle
  rw [max_eq_left]
  linarith

theorem fejerTriangle_eq_one_sub_of_nonneg_of_le_one
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    fejerTriangle x = 1 - x := by
  have hxabs : |x| ≤ 1 := by
    rwa [abs_of_nonneg hx0]
  rw [fejerTriangle_eq_one_sub_abs_of_abs_le_one hxabs, abs_of_nonneg hx0]

theorem fejerTriangle_eq_one_add_of_neg_one_le_of_nonpos
    {x : ℝ} (hx0 : x ≤ 0) (hx1 : -1 ≤ x) :
    fejerTriangle x = 1 + x := by
  have hxabs : |x| ≤ 1 := by
    rw [abs_of_nonpos hx0]
    linarith
  rw [fejerTriangle_eq_one_sub_abs_of_abs_le_one hxabs, abs_of_nonpos hx0]
  ring

theorem fejerTriangle_continuous : Continuous fejerTriangle := by
  unfold fejerTriangle
  exact (continuous_const.sub continuous_abs).max continuous_const

theorem fejerTriangle_hasCompactSupport : HasCompactSupport fejerTriangle := by
  refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc ?_
  intro x hx
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hxlt | hxgt
  · have hxabs : 1 ≤ |x| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    exact fejerTriangle_eq_zero_of_one_le_abs hxabs
  · have hxabs : 1 ≤ |x| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact fejerTriangle_eq_zero_of_one_le_abs hxabs

theorem fejerTriangle_integrable :
    Integrable fejerTriangle MeasureTheory.volume :=
  fejerTriangle_continuous.integrable_of_hasCompactSupport
    fejerTriangle_hasCompactSupport

theorem fejerTriangle_support_subset_Ioc :
    Function.support fejerTriangle ⊆ Set.Ioc (-1 : ℝ) 1 := by
  intro x hx
  change fejerTriangle x ≠ 0 at hx
  constructor
  · by_contra hle
    have hxle : x ≤ -1 := by linarith
    have hxabs : 1 ≤ |x| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    exact hx (fejerTriangle_eq_zero_of_one_le_abs hxabs)
  · by_contra hle
    have hxgt : 1 < x := by linarith
    have hxabs : 1 ≤ |x| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact hx (fejerTriangle_eq_zero_of_one_le_abs hxabs)

private theorem integral_one_add_on_neg_one_zero :
    (∫ x in (-1 : ℝ)..0, (1 + x)) = (1 / 2 : ℝ) := by
  have hderiv :
      ∀ x ∈ Set.uIcc (-1 : ℝ) 0,
        HasDerivAt (fun y : ℝ => y + y ^ 2 / 2) (1 + x) x := by
    intro x _hx
    have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h2half : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      refine (h2.div_const 2).congr_deriv ?_
      ring
    exact h1.add h2half
  have hint : IntervalIntegrable (fun x : ℝ => 1 + x) volume (-1) 0 :=
    (continuous_const.add continuous_id).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  norm_num at h ⊢
  exact h

private theorem integral_one_sub_on_zero_one :
    (∫ x in (0 : ℝ)..1, (1 - x)) = (1 / 2 : ℝ) := by
  have hderiv :
      ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun y : ℝ => y - y ^ 2 / 2) (1 - x) x := by
    intro x _hx
    have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h2half : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      refine (h2.div_const 2).congr_deriv ?_
      ring
    exact h1.sub h2half
  have hint : IntervalIntegrable (fun x : ℝ => 1 - x) volume 0 1 :=
    (continuous_const.sub continuous_id).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  norm_num at h ⊢
  exact h

theorem integral_fejerTriangle_neg_one_zero :
    (∫ x in (-1 : ℝ)..0, fejerTriangle x) = (1 / 2 : ℝ) := by
  rw [intervalIntegral.integral_congr]
  · exact integral_one_add_on_neg_one_zero
  · intro x hx
    have hxIcc : x ∈ Set.Icc (-1 : ℝ) 0 := by
      rwa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
    exact fejerTriangle_eq_one_add_of_neg_one_le_of_nonpos hxIcc.2 hxIcc.1

theorem integral_fejerTriangle_zero_one :
    (∫ x in (0 : ℝ)..1, fejerTriangle x) = (1 / 2 : ℝ) := by
  rw [intervalIntegral.integral_congr]
  · exact integral_one_sub_on_zero_one
  · intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact fejerTriangle_eq_one_sub_of_nonneg_of_le_one hxIcc.1 hxIcc.2

theorem intervalIntegral_fejerTriangle_neg_one_one :
    (∫ x in (-1 : ℝ)..1, fejerTriangle x) = 1 := by
  have hleft : IntervalIntegrable fejerTriangle volume (-1) 0 :=
    fejerTriangle_continuous.intervalIntegrable _ _
  have hright : IntervalIntegrable fejerTriangle volume 0 1 :=
    fejerTriangle_continuous.intervalIntegrable _ _
  have h :=
    intervalIntegral.integral_add_adjacent_intervals
      (a := (-1 : ℝ)) (b := 0) (c := 1) hleft hright
  rw [integral_fejerTriangle_neg_one_zero,
    integral_fejerTriangle_zero_one] at h
  norm_num at h
  exact h.symm

theorem integral_fejerTriangle :
    (∫ x : ℝ, fejerTriangle x) = 1 := by
  have h :=
    intervalIntegral.integral_eq_integral_of_support_subset
      (f := fejerTriangle) (μ := MeasureTheory.volume)
      fejerTriangle_support_subset_Ioc
  rw [← h]
  exact intervalIntegral_fejerTriangle_neg_one_one

end Fourier
end MathExtras
