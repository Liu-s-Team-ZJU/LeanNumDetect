/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCor7Closed

/-!
# The closed Selberg majorant of a real interval

This file turns the concrete Beurling defect whose Fourier transform was closed
in `VaalerCor7Closed` into Selberg's continuous majorant of a real interval.
The normalization is tailored to the real-endpoint large sieve: the majorant of
`(a,b]` has mass `(b-a)+delta^{-1}` and Fourier support in the `delta` band.

Only the pointwise, continuity, integrability, and mass parts are established
here.  The Fourier cancellation and Poisson summation are kept in the consumer
leaf so each analytic seam can be source-checked independently.
-/

noncomputable section

open MeasureTheory Real Set Filter Topology Complex
open scoped BigOperators FourierTransform

namespace MathExtras.NumberTheory.Analysis.SelbergIntervalMajorantClosed

open VaalerBeurlingNonneg
open VaalerBeurlingFT
open VaalerExcessFT
open VaalerInterpHContinuous
open VaalerThm16Mechanism
open VaalerCor7Closed

/-- The concrete continuous Beurling majorant `B = H + K`. -/
def beurlingBClosed (x : ℝ) : ℝ := interpH x + fejerK x

/-- The half-weight interval step.  It equals `1_(a,b]` away from the two
endpoints and is the sign part of Selberg's continuous majorant. -/
def intervalSignPair (a b x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.sign (b - x) + Real.sign (x - a))

/-- Selberg's band-`delta` majorant of the real interval `(a,b]`. -/
def selbergIntervalMajorant (a b δ x : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (beurlingBClosed (δ * (b - x)) + beurlingBClosed (δ * (x - a)))

@[simp] theorem phi_zero : phi 0 = 1 := by
  simp [phi, interpH, fejerK]

theorem sign_mul_pos {c : ℝ} (hc : 0 < c) (x : ℝ) :
    Real.sign (c * x) = Real.sign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [Real.sign_of_neg hx, Real.sign_of_neg (mul_neg_of_pos_of_neg hc hx)]
  · subst x
    simp
  · rw [Real.sign_of_pos hx, Real.sign_of_pos (mul_pos hc hx)]

theorem beurlingBClosed_eq_sign_add_phi (x : ℝ) :
    beurlingBClosed x = Real.sign x + phi x := by
  unfold beurlingBClosed phi
  ring

/-- The useful decomposition into the compact half-step and two nonnegative
copies of the Beurling defect. -/
theorem selbergIntervalMajorant_eq_signPair_add_phi
    {a b δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    selbergIntervalMajorant a b δ x =
      intervalSignPair a b x +
        (1 / 2 : ℝ) * (phi (δ * (b - x)) + phi (δ * (x - a))) := by
  unfold selbergIntervalMajorant intervalSignPair
  rw [beurlingBClosed_eq_sign_add_phi, beurlingBClosed_eq_sign_add_phi,
    sign_mul_pos hδ, sign_mul_pos hδ]
  ring

/-- The same decomposition in terms of the unit-mass scaled defects. -/
theorem selbergIntervalMajorant_eq_signPair_add_scaled
    {a b δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    selbergIntervalMajorant a b δ x =
      intervalSignPair a b x + (1 / (2 * δ)) *
        (vaalerBeurlingMajorant_closed.scaled δ (b - x) +
          vaalerBeurlingMajorant_closed.scaled δ (x - a)) := by
  rw [selbergIntervalMajorant_eq_signPair_add_phi hδ]
  change intervalSignPair a b x + (1 / 2 : ℝ) *
      (phi (δ * (b - x)) + phi (δ * (x - a))) =
    intervalSignPair a b x + (1 / (2 * δ)) *
      (δ * phi (δ * (b - x)) + δ * phi (δ * (x - a)))
  field_simp [hδ.ne']
  <;> ring

theorem beurlingBClosed_continuous : Continuous beurlingBClosed := by
  exact interpH_continuous.add fejerK_continuous

theorem selbergIntervalMajorant_continuous (a b δ : ℝ) :
    Continuous (selbergIntervalMajorant a b δ) := by
  unfold selbergIntervalMajorant
  exact continuous_const.mul
    ((beurlingBClosed_continuous.comp
      (continuous_const.mul (continuous_const.sub continuous_id))).add
    (beurlingBClosed_continuous.comp
      (continuous_const.mul (continuous_id.sub continuous_const))))

theorem intervalSignPair_nonneg {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    0 ≤ intervalSignPair a b x := by
  unfold intervalSignPair
  rcases lt_trichotomy x a with hxa | hxa | hax
  · have hxb : x < b := lt_of_lt_of_le hxa hab
    rw [Real.sign_of_pos (sub_pos.mpr hxb), Real.sign_of_neg (sub_neg.mpr hxa)]
    norm_num
  · subst x
    by_cases hab' : a = b
    · subst b
      simp
    · have hablt : a < b := lt_of_le_of_ne hab hab'
      rw [Real.sign_of_pos (sub_pos.mpr hablt)]
      simp
  · rcases lt_trichotomy x b with hxb | hxb | hbx
    · rw [Real.sign_of_pos (sub_pos.mpr hxb), Real.sign_of_pos (sub_pos.mpr hax)]
      norm_num
    · subst x
      rw [Real.sign_of_pos (sub_pos.mpr (lt_of_le_of_ne hab (Ne.symm (ne_of_gt hax))))]
      simp
    · rw [Real.sign_of_neg (sub_neg.mpr hbx), Real.sign_of_pos (sub_pos.mpr
        (lt_of_le_of_lt hab hbx))]
      norm_num

theorem intervalSignPair_eq_one {a b x : ℝ} (hax : a < x) (hxb : x < b) :
    intervalSignPair a b x = 1 := by
  unfold intervalSignPair
  rw [Real.sign_of_pos (sub_pos.mpr hxb), Real.sign_of_pos (sub_pos.mpr hax)]
  norm_num

theorem intervalSignPair_right_endpoint {a b : ℝ} (hab : a < b) :
    intervalSignPair a b b = 1 / 2 := by
  unfold intervalSignPair
  rw [Real.sign_of_pos (sub_pos.mpr hab)]
  simp

/-- The Selberg function is nonnegative on the whole line. -/
theorem selbergIntervalMajorant_nonneg
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (x : ℝ) :
    0 ≤ selbergIntervalMajorant a b δ x := by
  rw [selbergIntervalMajorant_eq_signPair_add_phi hδ]
  have hs := intervalSignPair_nonneg hab x
  have h1 : 0 ≤ phi (δ * (b - x)) :=
    vaalerBeurlingMajorant_closed.nonneg (δ * (b - x))
  have h2 : 0 ≤ phi (δ * (x - a)) :=
    vaalerBeurlingMajorant_closed.nonneg (δ * (x - a))
  positivity

/-- The majorant is at least one at every point of `(a,b]`, including the
right endpoint where the half-step is completed by `phi(0)/2 = 1/2`. -/
theorem one_le_selbergIntervalMajorant
    {a b δ x : ℝ} (hδ : 0 < δ) (hax : a < x) (hxb : x ≤ b) :
    1 ≤ selbergIntervalMajorant a b δ x := by
  rw [selbergIntervalMajorant_eq_signPair_add_phi hδ]
  rcases hxb.lt_or_eq with hxb' | rfl
  · rw [intervalSignPair_eq_one hax hxb']
    have h1 : 0 ≤ phi (δ * (b - x)) :=
      vaalerBeurlingMajorant_closed.nonneg (δ * (b - x))
    have h2 : 0 ≤ phi (δ * (x - a)) :=
      vaalerBeurlingMajorant_closed.nonneg (δ * (x - a))
    linarith
  · rw [intervalSignPair_right_endpoint hax]
    simp only [sub_self, mul_zero, phi_zero]
    have h2 : 0 ≤ phi (δ * (x - a)) :=
      vaalerBeurlingMajorant_closed.nonneg (δ * (x - a))
    linarith

/-! ## The half-step is the interval indicator almost everywhere -/

theorem intervalSignPair_eq_indicator_of_ne
    {a b x : ℝ} (hab : a ≤ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    intervalSignPair a b x = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ Set.Ioc a b
  · have hax : a < x := hx.1
    have hxb' : x ≤ b := hx.2
    have hxb'' : x < b := lt_of_le_of_ne hxb' hxb
    rw [intervalSignPair_eq_one hax hxb'', Set.indicator_of_mem hx]
  · have hout : x < a ∨ b < x := by
      rcases lt_trichotomy x a with h | h | h
      · exact Or.inl h
      · exact (hxa h).elim
      · right
        by_contra hn
        exact hx ⟨h, le_of_not_gt hn⟩
    rw [Set.indicator_of_notMem hx]
    unfold intervalSignPair
    rcases hout with h | h
    · have hxb' : x < b := lt_of_lt_of_le h hab
      rw [Real.sign_of_pos (sub_pos.mpr hxb'), Real.sign_of_neg (sub_neg.mpr h)]
      norm_num
    · have hax : a < x := lt_of_le_of_lt hab h
      rw [Real.sign_of_neg (sub_neg.mpr h), Real.sign_of_pos (sub_pos.mpr hax)]
      norm_num

theorem intervalSignPair_ae_eq_indicator {a b : ℝ} (hab : a ≤ b) :
    intervalSignPair a b =ᵐ[volume]
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) := by
  have ha : ∀ᵐ x ∂volume, x ≠ a := by
    rw [ae_iff]
    simp
  have hb : ∀ᵐ x ∂volume, x ≠ b := by
    rw [ae_iff]
    simp
  filter_upwards [ha, hb] with x hxa hxb
  exact intervalSignPair_eq_indicator_of_ne hab hxa hxb

theorem intervalSignPair_integrable {a b : ℝ} (hab : a ≤ b) :
    Integrable (intervalSignPair a b) := by
  have hi : Integrable ((Set.Ioc a b).indicator (fun _ => (1 : ℝ))) :=
    (MeasureTheory.integrableOn_const (s := Set.Ioc a b)
      (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
        measurableSet_Ioc
  exact hi.congr (intervalSignPair_ae_eq_indicator hab).symm

theorem integral_intervalSignPair {a b : ℝ} (hab : a ≤ b) :
    ∫ x, intervalSignPair a b x = b - a := by
  rw [MeasureTheory.integral_congr_ae (intervalSignPair_ae_eq_indicator hab)]
  rw [MeasureTheory.integral_indicator_const (1 : ℝ) measurableSet_Ioc]
  have hv : volume.real (Set.Ioc a b) = b - a := by
    rw [MeasureTheory.Measure.real, Real.volume_Ioc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr hab)
  simpa [hv]

theorem scaled_integrable {δ : ℝ} (hδ : 0 < δ) :
    Integrable (vaalerBeurlingMajorant_closed.scaled δ) := by
  unfold VaalerBeurlingMajorant.scaled
  exact ((integrable_comp_mul_left_iff vaalerBeurlingMajorant_closed.φ hδ.ne').mpr
    vaalerBeurlingMajorant_closed.integrable).const_mul δ

theorem selbergIntervalMajorant_integrable
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    Integrable (selbergIntervalMajorant a b δ) := by
  rw [show selbergIntervalMajorant a b δ = fun x =>
      intervalSignPair a b x + (1 / (2 * δ)) *
        (vaalerBeurlingMajorant_closed.scaled δ (b - x) +
          vaalerBeurlingMajorant_closed.scaled δ (x - a)) by
        funext x
        exact selbergIntervalMajorant_eq_signPair_add_scaled hδ x]
  exact (intervalSignPair_integrable hab).add
    ((((scaled_integrable hδ).comp_sub_left b).add
      ((scaled_integrable hδ).comp_sub_right a)).const_mul (1 / (2 * δ)))

/-- The exact Selberg mass `(b-a)+delta^{-1}`. -/
theorem integral_selbergIntervalMajorant
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    ∫ x, selbergIntervalMajorant a b δ x = (b - a) + δ⁻¹ := by
  rw [show selbergIntervalMajorant a b δ = fun x =>
      intervalSignPair a b x + (1 / (2 * δ)) *
        (vaalerBeurlingMajorant_closed.scaled δ (b - x) +
          vaalerBeurlingMajorant_closed.scaled δ (x - a)) by
        funext x
        exact selbergIntervalMajorant_eq_signPair_add_scaled hδ x]
  change (∫ x, intervalSignPair a b x + (1 / (2 * δ)) *
      (vaalerBeurlingMajorant_closed.scaled δ (b - x) +
        vaalerBeurlingMajorant_closed.scaled δ (x - a))) = (b - a) + δ⁻¹
  let f : ℝ → ℝ := fun x =>
    vaalerBeurlingMajorant_closed.scaled δ (b - x) +
      vaalerBeurlingMajorant_closed.scaled δ (x - a)
  have hf : Integrable f :=
    ((scaled_integrable hδ).comp_sub_left b).add
      ((scaled_integrable hδ).comp_sub_right a)
  have hfint : ∫ x, f x = 2 := by
    change (∫ x, vaalerBeurlingMajorant_closed.scaled δ (b - x) +
      vaalerBeurlingMajorant_closed.scaled δ (x - a)) = 2
    rw [MeasureTheory.integral_add ((scaled_integrable hδ).comp_sub_left b)
        ((scaled_integrable hδ).comp_sub_right a),
      MeasureTheory.integral_sub_left_eq_self
        (vaalerBeurlingMajorant_closed.scaled δ) volume b,
      MeasureTheory.integral_sub_right_eq_self
        (vaalerBeurlingMajorant_closed.scaled δ) a,
      vaalerBeurlingMajorant_closed.scaled_integral hδ]
    norm_num
  change (∫ x, intervalSignPair a b x + (1 / (2 * δ)) * f x) =
    (b - a) + δ⁻¹
  rw [MeasureTheory.integral_add (intervalSignPair_integrable hab)
      (hf.const_mul (1 / (2 * δ))),
    integral_intervalSignPair hab, MeasureTheory.integral_const_mul, hfint]
  field_simp [hδ.ne']
  <;> ring

end MathExtras.NumberTheory.Analysis.SelbergIntervalMajorantClosed

end
