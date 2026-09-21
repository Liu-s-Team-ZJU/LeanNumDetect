/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.SelbergIntervalMajorantClosed

/-!
# Fourier support of the closed Selberg interval majorant

The Fourier transform of the interval half-step is cancelled exactly by the
two translated Beurling defects.  This is the analytic bridge from the closed
Vaaler Corollary 7 to the real-endpoint large sieve.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology Complex
open scoped FourierTransform BigOperators

namespace MathExtras.NumberTheory.Analysis.SelbergIntervalFourierClosed

open VaalerThm16Mechanism
open VaalerCor7RouteB
open VaalerJFTviaHN
open VaalerCor7Closed
open SelbergIntervalMajorantClosed

theorem integrable_ofReal_mul_echar {f : ℝ → ℝ} (hf : Integrable f) (t : ℝ) :
    Integrable (fun x => (f x : ℂ) * echar t x) := by
  refine hf.ofReal.mul_bdd (c := 1) (aestronglyMeasurable_echar t) ?_
  filter_upwards with x
  rw [norm_echar]

/-- Fourier transform of the half-weight step.  Its endpoint values are
irrelevant to the integral, so this is the ordinary transform of `1_(a,b]`. -/
theorem intervalSignPair_echar_integral
    {a b t : ℝ} (hab : a ≤ b) (ht : t ≠ 0) :
    (∫ x : ℝ, (intervalSignPair a b x : ℂ) * echar t x) =
      echarAntideriv t b - echarAntideriv t a := by
  have hae := intervalSignPair_ae_eq_indicator hab
  have hc : (fun x : ℝ => (intervalSignPair a b x : ℂ) * echar t x) =ᵐ[volume]
      (Set.Ioc a b).indicator (fun x => echar t x) := by
    filter_upwards [hae] with x hx
    by_cases hmem : x ∈ Set.Ioc a b
    · rw [hx, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      simp
    · rw [hx, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      simp
  rw [integral_congr_ae hc, MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    exact hasDerivAt_echar_antideriv ht x
  · exact (by unfold echar; fun_prop : Continuous (echar t)).intervalIntegrable a b

/-- Translation law for the right-hand Beurling defect. -/
theorem scaled_shift_right_echar_integral (δ t a : ℝ) :
    (∫ x : ℝ, (vaalerBeurlingMajorant_closed.scaled δ (x - a) : ℂ) * echar t x) =
      echar t a *
        ∫ y : ℝ, (vaalerBeurlingMajorant_closed.scaled δ y : ℂ) * echar t y := by
  have hself := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun x : ℝ =>
      (vaalerBeurlingMajorant_closed.scaled δ x : ℂ) * echar t (x + a)) a
  have hlhs : (∫ x : ℝ, (fun x : ℝ =>
      (vaalerBeurlingMajorant_closed.scaled δ x : ℂ) * echar t (x + a)) (x - a)) =
      ∫ x : ℝ,
        (vaalerBeurlingMajorant_closed.scaled δ (x - a) : ℂ) * echar t x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [show x - a + a = x by ring]
  rw [hlhs] at hself
  rw [hself, ← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [echar_add]
  ring

/-- Reflection/translation law for the left-hand Beurling defect. -/
theorem scaled_shift_left_echar_integral (δ t b : ℝ) :
    (∫ x : ℝ, (vaalerBeurlingMajorant_closed.scaled δ (b - x) : ℂ) * echar t x) =
      echar t b *
        ∫ y : ℝ, (vaalerBeurlingMajorant_closed.scaled δ y : ℂ) * echar (-t) y := by
  have hself := integral_sub_left_eq_self
    (fun y : ℝ =>
      (vaalerBeurlingMajorant_closed.scaled δ y : ℂ) * echar t (b - y))
    (volume : Measure ℝ) b
  have hlhs : (∫ x : ℝ, (fun y : ℝ =>
      (vaalerBeurlingMajorant_closed.scaled δ y : ℂ) * echar t (b - y)) (b - x)) =
      ∫ x : ℝ,
        (vaalerBeurlingMajorant_closed.scaled δ (b - x) : ℂ) * echar t x := by
    apply integral_congr_ae
    filter_upwards with x
    congr 2
    ring
  rw [hlhs] at hself
  rw [hself, ← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  have he : echar t (b - y) = echar t b * echar (-t) y := by
    unfold echar
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- The two defect transforms cancel the transform of the interval exactly at
and beyond the band edge. -/
theorem selbergIntervalMajorant_echar_integral_eq_zero
    {a b δ t : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (htfar : δ ≤ |t|) :
    (∫ x : ℝ, (selbergIntervalMajorant a b δ x : ℂ) * echar t x) = 0 := by
  have ht : t ≠ 0 := by
    intro h
    subst t
    simp at htfar
    linarith
  have hstep := integrable_ofReal_mul_echar (intervalSignPair_integrable hab) t
  have hleft := integrable_ofReal_mul_echar ((scaled_integrable hδ).comp_sub_left b) t
  have hright := integrable_ofReal_mul_echar ((scaled_integrable hδ).comp_sub_right a) t
  have hfun :
      (fun x : ℝ => (selbergIntervalMajorant a b δ x : ℂ) * echar t x) =
        fun x => (intervalSignPair a b x : ℂ) * echar t x +
          ((1 / (2 * δ) : ℝ) : ℂ) *
            ((vaalerBeurlingMajorant_closed.scaled δ (b - x) : ℂ) * echar t x +
             (vaalerBeurlingMajorant_closed.scaled δ (x - a) : ℂ) * echar t x) := by
    funext x
    rw [selbergIntervalMajorant_eq_signPair_add_scaled hδ]
    push_cast
    ring
  rw [hfun]
  let fs : ℝ → ℂ := fun x => (intervalSignPair a b x : ℂ) * echar t x
  let fl : ℝ → ℂ := fun x =>
    (vaalerBeurlingMajorant_closed.scaled δ (b - x) : ℂ) * echar t x
  let fr : ℝ → ℂ := fun x =>
    (vaalerBeurlingMajorant_closed.scaled δ (x - a) : ℂ) * echar t x
  let fb : ℝ → ℂ := fun x =>
    ((1 / (2 * δ) : ℝ) : ℂ) * (fl x + fr x)
  have hfs : Integrable fs := hstep
  have hfl : Integrable fl := hleft
  have hfr : Integrable fr := hright
  have hfb : Integrable fb := (hfl.add hfr).const_mul _
  have hfsval : (∫ x, fs x) = echarAntideriv t b - echarAntideriv t a :=
    intervalSignPair_echar_integral hab ht
  have hflval : (∫ x, fl x) = echar t b *
      ∫ y : ℝ, (vaalerBeurlingMajorant_closed.scaled δ y : ℂ) * echar (-t) y :=
    scaled_shift_left_echar_integral δ t b
  have hfrval : (∫ x, fr x) = echar t a *
      ∫ y : ℝ, (vaalerBeurlingMajorant_closed.scaled δ y : ℂ) * echar t y :=
    scaled_shift_right_echar_integral δ t a
  have hfbval : (∫ x, fb x) = ((1 / (2 * δ) : ℝ) : ℂ) *
      (echar t b * (-((δ : ℂ)) / ((π : ℂ) * Complex.I * ((-t : ℝ) : ℂ))) +
       echar t a * (-((δ : ℂ)) / ((π : ℂ) * Complex.I * (t : ℂ)))) := by
    dsimp only [fb]
    rw [MeasureTheory.integral_const_mul]
    have hadd : (∫ x, fl x + fr x) = (∫ x, fl x) + ∫ x, fr x :=
      MeasureTheory.integral_add hfl hfr
    rw [hadd, hflval, hfrval,
      vaalerBeurlingMajorant_closed.scaled_ftFar hδ
        (by simpa using htfar : δ ≤ |-t|),
      vaalerBeurlingMajorant_closed.scaled_ftFar hδ htfar]
  change (∫ x, fs x + fb x) = 0
  rw [MeasureTheory.integral_add hfs hfb, hfsval, hfbval]
  unfold echarAntideriv
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hpic : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp [htc, hδc, hpic, Complex.I_ne_zero]
  ring

/-- Mathlib's real Fourier integral uses the same character convention as
`echar`. -/
theorem fourier_eq_echar_integral (f : ℝ → ℂ) (t : ℝ) :
    𝓕 f t = ∫ x, f x * echar t x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

/-- Fourier support of the interval majorant, including vanishing at the band
edge (which is useful for the sharp spacing constant). -/
theorem fourier_selbergIntervalMajorant_eq_zero
    {a b δ t : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (htfar : δ ≤ |t|) :
    𝓕 (fun x => (selbergIntervalMajorant a b δ x : ℂ)) t = 0 := by
  rw [fourier_eq_echar_integral]
  exact selbergIntervalMajorant_echar_integral_eq_zero hab hδ htfar

end MathExtras.NumberTheory.Analysis.SelbergIntervalFourierClosed

end
