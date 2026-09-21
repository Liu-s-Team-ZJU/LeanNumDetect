/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerMinorWallClosed
import MathExtras.NumberTheory.Analysis.VaalerTheorem6Unconditional
import MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof
import MathExtras.NumberTheory.Analysis.VaalerFejerFT
import MathExtras.NumberTheory.Analysis.VaalerPoUCancellation
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Vaaler Corollary 7, closed

The global identity `interpH' = 2 Re vaalerJ` proved in
`VaalerMinorWallClosed` permits an ordinary integration by parts on the two
half-lines.  The two one-sided values of `interpH - sign` at zero contribute
the jump term, while Vaaler Theorem 6 evaluates the transform of `vaalerJ`.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology Set
open scoped BigOperators FourierTransform

namespace MathExtras.NumberTheory.Analysis.VaalerCor7Closed

open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerThm16Mechanism
open MathExtras.NumberTheory.Analysis.VaalerBeurlingFT
open MathExtras.NumberTheory.Analysis.VaalerExcessFT
open MathExtras.NumberTheory.Analysis.VaalerCor7ExcessFT
open MathExtras.NumberTheory.Analysis.VaalerCor7IBPProof
open MathExtras.NumberTheory.Analysis.VaalerCor7RouteB
open MathExtras.NumberTheory.Analysis.VaalerMinorWallClosed
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerTheorem6Unconditional
open MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof
open MathExtras.NumberTheory.Analysis.VaalerFejerFT
open MathExtras.NumberTheory.Analysis.VaalerPoUCancellation
open MathExtras.NumberTheory.Analysis.VaalerInterpHContinuous
open MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ
open MathExtras.NumberTheory.Analysis.VaalerHNAssembly

/-- The inverse-transform presentation of `vaalerJ` is real-valued. -/
theorem vaalerJ_eq_ofReal_re (x : ℝ) : ((vaalerJ x).re : ℂ) = vaalerJ x := by
  have hx := congrFun gcEqVaalerJSpatial_closed x
  change ((vaalerJ x).re : ℂ) = vaalerJ x
  rw [← hx]
  rfl

/-- Complexification of the global identity `interpH' = 2 Re vaalerJ`. -/
theorem hasDerivAt_interpHC_two_mul_vaalerJ (x : ℝ) :
    HasDerivAt (fun y : ℝ => (interpH y : ℂ)) (2 * vaalerJ x) x := by
  have h := (hasDerivAt_interpH_two_mul_re_vaalerJ x).ofReal_comp
  convert h using 1
  rw [ofReal_mul, ofReal_ofNat, vaalerJ_eq_ofReal_re]

/-- On the positive half-line the sign term is locally constant. -/
theorem hasDerivAt_Ec_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt Ec (2 * vaalerJ x) x := by
  have h := (hasDerivAt_interpHC_two_mul_vaalerJ x).sub_const (1 : ℂ)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp only [Ec, excess, Real.sign_of_pos hy]
  push_cast
  ring

/-- On the negative half-line the sign term is locally constant. -/
theorem hasDerivAt_Ec_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt Ec (2 * vaalerJ x) x := by
  have h := (hasDerivAt_interpHC_two_mul_vaalerJ x).add_const (1 : ℂ)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hx] with y hy
  simp only [Ec, excess, Real.sign_of_neg hy]
  push_cast
  ring

/-! ## Decay and boundary values -/

theorem tendsto_inv_sq_atTop :
    Tendsto (fun x : ℝ => (x ^ 2)⁻¹) atTop (𝓝 0) :=
  (tendsto_pow_atTop (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0)).inv_tendsto_atTop

theorem tendsto_inv_sq_atBot :
    Tendsto (fun x : ℝ => (x ^ 2)⁻¹) atBot (𝓝 0) := by
  have h := tendsto_inv_sq_atTop.comp (tendsto_neg_atBot_atTop :
    Tendsto (fun x : ℝ => -x) atBot atTop)
  simpa only [Function.comp_def, neg_sq] using h

theorem tendsto_fejerK_atTop : Tendsto fejerK atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with x
    rw [MathExtras.NumberTheory.Analysis.VaalerInterpHContinuous.fejerK_eq_sinc_sq]
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact fejerK_le_inv_sq hx.ne'
  · exact tendsto_inv_sq_atTop

theorem tendsto_fejerK_atBot : Tendsto fejerK atBot (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with x
    rw [MathExtras.NumberTheory.Analysis.VaalerInterpHContinuous.fejerK_eq_sinc_sq]
    positivity
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
    exact fejerK_le_inv_sq hx.ne
  · exact tendsto_inv_sq_atBot

theorem tendsto_Ec_atTop : Tendsto Ec atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun x => norm_nonneg _)
  · exact Filter.Eventually.of_forall
      (fun x => norm_Ec_le_fejerK
        VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds x)
  · exact tendsto_fejerK_atTop

theorem tendsto_Ec_atBot : Tendsto Ec atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun x => norm_nonneg _)
  · exact Filter.Eventually.of_forall
      (fun x => norm_Ec_le_fejerK
        VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds x)
  · exact tendsto_fejerK_atBot

theorem tendsto_Ec_mul_antideriv_atTop {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun x => Ec x * echarAntideriv t x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun x => norm_nonneg _)
  · exact Filter.Eventually.of_forall
      (fun x => norm_Ec_mul_antideriv_le
        VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds ht x)
  · simpa using tendsto_fejerK_atTop.mul_const ((2 * π * |t|)⁻¹)

theorem tendsto_Ec_mul_antideriv_atBot {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun x => Ec x * echarAntideriv t x) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun x => norm_nonneg _)
  · exact Filter.Eventually.of_forall
      (fun x => norm_Ec_mul_antideriv_le
        VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds ht x)
  · simpa using tendsto_fejerK_atBot.mul_const ((2 * π * |t|)⁻¹)

theorem tendsto_Ec_nhdsGT_zero :
    Tendsto Ec (𝓝[>] (0 : ℝ)) (𝓝 (-1 : ℂ)) := by
  have hcont : Continuous (fun x : ℝ => (interpH x : ℂ) - 1) := by
    exact (Complex.continuous_ofReal.comp interpH_continuous).sub continuous_const
  have h : Tendsto (fun x : ℝ => (interpH x : ℂ) - 1)
      (𝓝[>] (0 : ℝ)) (𝓝 ((interpH 0 : ℂ) - 1)) :=
    hcont.continuousWithinAt.tendsto
  have heq : (fun x : ℝ => (interpH x : ℂ) - 1) =ᶠ[𝓝[>] (0 : ℝ)] Ec := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [mem_Ioi] at hx
    simp only [Ec, excess, Real.sign_of_pos hx]
    push_cast
    rfl
  have hzero : interpH 0 = 0 := by
    unfold interpH
    simp
  simpa [hzero] using h.congr' heq

theorem tendsto_Ec_nhdsLT_zero :
    Tendsto Ec (𝓝[<] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hcont : Continuous (fun x : ℝ => (interpH x : ℂ) + 1) := by
    exact (Complex.continuous_ofReal.comp interpH_continuous).add continuous_const
  have h : Tendsto (fun x : ℝ => (interpH x : ℂ) + 1)
      (𝓝[<] (0 : ℝ)) (𝓝 ((interpH 0 : ℂ) + 1)) :=
    hcont.continuousWithinAt.tendsto
  have heq : (fun x : ℝ => (interpH x : ℂ) + 1) =ᶠ[𝓝[<] (0 : ℝ)] Ec := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [mem_Iio] at hx
    simp only [Ec, excess, Real.sign_of_neg hx]
    push_cast
    ring
  have hzero : interpH 0 = 0 := by
    unfold interpH
    simp
  simpa [hzero] using h.congr' heq

theorem continuous_echarAntideriv (t : ℝ) : Continuous (echarAntideriv t) := by
  unfold echarAntideriv echar
  fun_prop

theorem tendsto_Ec_mul_antideriv_nhdsGT_zero (t : ℝ) :
    Tendsto (fun x => Ec x * echarAntideriv t x) (𝓝[>] (0 : ℝ))
      (𝓝 ((-1 : ℂ) * echarAntideriv t 0)) := by
  exact tendsto_Ec_nhdsGT_zero.mul
    (continuous_echarAntideriv t).continuousWithinAt.tendsto

theorem tendsto_Ec_mul_antideriv_nhdsLT_zero (t : ℝ) :
    Tendsto (fun x => Ec x * echarAntideriv t x) (𝓝[<] (0 : ℝ))
      (𝓝 ((1 : ℂ) * echarAntideriv t 0)) := by
  exact tendsto_Ec_nhdsLT_zero.mul
    (continuous_echarAntideriv t).continuousWithinAt.tendsto

/-! ## Integrability and the transform of the derivative term -/

theorem vaalerJ_integrable_closed : Integrable vaalerJ := by
  rw [← gcEqVaalerJSpatial_closed]
  exact gIntegrable_holds

theorem vaalerJ_mul_echar_integrable (t : ℝ) :
    Integrable (fun x => vaalerJ x * echar t x) := by
  refine vaalerJ_integrable_closed.mul_bdd (c := 1)
    (aestronglyMeasurable_echar t) ?_
  filter_upwards with x
  rw [norm_echar]

theorem two_vaalerJ_mul_antideriv_integrable (t : ℝ) :
    Integrable (fun x => (2 * vaalerJ x) * echarAntideriv t x) := by
  have h := (vaalerJ_mul_echar_integrable t).const_mul (2 : ℂ)
  have hdiv := h.div_const (-2 * π * Complex.I * t : ℂ)
  convert hdiv using 1
  funext x
  unfold echarAntideriv
  ring

theorem pi_I_t_ne_zero {t : ℝ} (ht : t ≠ 0) :
    ((π : ℂ) * Complex.I * (t : ℂ)) ≠ 0 := by
  have hpi : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have htC : (t : ℂ) ≠ 0 := by
    exact_mod_cast ht
  exact mul_ne_zero (mul_ne_zero hpi Complex.I_ne_zero) htC

theorem two_mul_antideriv_zero {t : ℝ} (ht : t ≠ 0) :
    2 * echarAntideriv t 0 = -((π : ℂ) * Complex.I * (t : ℂ))⁻¹ := by
  have hp := pi_I_t_ne_zero ht
  unfold echarAntideriv echar
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

theorem integral_two_vaalerJ_mul_antideriv {t : ℝ} (ht : t ≠ 0) :
    (∫ x : ℝ, (2 * vaalerJ x) * echarAntideriv t x)
      = -((π : ℂ) * Complex.I * (t : ℂ))⁻¹ * (vaalerJhatFT t : ℂ) := by
  have hp := pi_I_t_ne_zero ht
  calc
    (∫ x : ℝ, (2 * vaalerJ x) * echarAntideriv t x)
        = ∫ x : ℝ, (2 / (-2 * π * Complex.I * (t : ℂ))) *
            (vaalerJ x * echar t x) := by
          refine integral_congr_ae ?_
          filter_upwards with x
          unfold echarAntideriv
          ring
    _ = (2 / (-2 * π * Complex.I * (t : ℂ))) *
          (∫ x : ℝ, vaalerJ x * echar t x) := by
          rw [integral_const_mul]
    _ = (2 / (-2 * π * Complex.I * (t : ℂ))) * 𝓕 vaalerJ t := by
          rw [integral_mul_echar_eq_fourier]
    _ = (2 / (-2 * π * Complex.I * (t : ℂ))) * (vaalerJhatFT t : ℂ) := by
          rw [fourier_vaalerJ_eq_vaalerJhatFT ht]
    _ = -((π : ℂ) * Complex.I * (t : ℂ))⁻¹ * (vaalerJhatFT t : ℂ) := by
          field_simp

/-! ## The two half-line integrations by parts -/

/-- Vaaler's Corollary 7, with the jump at zero supplied by the two ordinary
half-line boundary terms. -/
theorem cor7IBP_closed : Cor7IBP := by
  intro t ht
  change (∫ x : ℝ, Ec x * echar t x) =
    ((π : ℂ) * Complex.I * (t : ℂ))⁻¹ * ((vaalerJhatFT t : ℂ) - 1)
  have hE : Integrable (fun x : ℝ => Ec x * echar t x) := by
    simpa only [Ec] using excessMod_integrable
      VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds fejerIntegrable_holds t
  have hJv : Integrable (fun x : ℝ => (2 * vaalerJ x) * echarAntideriv t x) :=
    two_vaalerJ_mul_antideriv_integrable t
  have hpos := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := Ec) (u' := fun x => 2 * vaalerJ x)
    (v := echarAntideriv t) (v' := echar t)
    (fun x hx => hasDerivAt_Ec_pos hx)
    (fun x _ => hasDerivAt_echar_antideriv ht x)
    hE.integrableOn hJv.integrableOn
    (tendsto_Ec_mul_antideriv_nhdsGT_zero t)
    (tendsto_Ec_mul_antideriv_atTop ht)
  have hneg := MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := Ec) (u' := fun x => 2 * vaalerJ x)
    (v := echarAntideriv t) (v' := echar t)
    (fun x hx => hasDerivAt_Ec_neg hx)
    (fun x _ => hasDerivAt_echar_antideriv ht x)
    hE.integrableOn hJv.integrableOn
    (tendsto_Ec_mul_antideriv_nhdsLT_zero t)
    (tendsto_Ec_mul_antideriv_atBot ht)
  have hsplitE :
      (∫ x in Iic (0 : ℝ), Ec x * echar t x) +
          (∫ x in Ioi (0 : ℝ), Ec x * echar t x)
        = ∫ x : ℝ, Ec x * echar t x := by
    simpa only [compl_Iic] using
      (MeasureTheory.integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hE)
  have hsplitJ :
      (∫ x in Iic (0 : ℝ), (2 * vaalerJ x) * echarAntideriv t x) +
          (∫ x in Ioi (0 : ℝ), (2 * vaalerJ x) * echarAntideriv t x)
        = ∫ x : ℝ, (2 * vaalerJ x) * echarAntideriv t x := by
    simpa only [compl_Iic] using
      (MeasureTheory.integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hJv)
  calc
    (∫ x : ℝ, Ec x * echar t x)
        = (∫ x in Iic (0 : ℝ), Ec x * echar t x) +
            (∫ x in Ioi (0 : ℝ), Ec x * echar t x) := hsplitE.symm
    _ = ((1 : ℂ) * echarAntideriv t 0 - 0 -
            ∫ x in Iic (0 : ℝ), (2 * vaalerJ x) * echarAntideriv t x) +
          (0 - (-1 : ℂ) * echarAntideriv t 0 -
            ∫ x in Ioi (0 : ℝ), (2 * vaalerJ x) * echarAntideriv t x) := by
          rw [hneg, hpos]
    _ = 2 * echarAntideriv t 0 -
          ((∫ x in Iic (0 : ℝ), (2 * vaalerJ x) * echarAntideriv t x) +
            ∫ x in Ioi (0 : ℝ), (2 * vaalerJ x) * echarAntideriv t x) := by
          ring
    _ = 2 * echarAntideriv t 0 -
          (∫ x : ℝ, (2 * vaalerJ x) * echarAntideriv t x) := by
          rw [hsplitJ]
    _ = ((π : ℂ) * Complex.I * (t : ℂ))⁻¹ * ((vaalerJhatFT t : ℂ) - 1) := by
          rw [two_mul_antideriv_zero ht, integral_two_vaalerJ_mul_antideriv ht]
          ring

/-- The formerly residual derivative/multiplication statement is now a theorem. -/
theorem cor7DerivMultiplication_closed : Cor7DerivMultiplication :=
  cor7IBP_iff_fourierIntegral.mp cor7IBP_closed

/-- The concrete excess has Vaaler's far Fourier transform. -/
theorem excessFarFourier_closed : ExcessFarFourier :=
  excessFarFourier_holds cor7IBP_closed

/-- The explicit Beurling majorant now has all Fourier fields unconditionally. -/
def vaalerBeurlingMajorant_closed : VaalerBeurlingMajorant :=
  vaalerBeurlingMajorant_of_cor7IBP
    VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds
    fejerIntegrable_holds fejerIntegralOne_holds fejerFarFourier_holds
    cor7IBP_closed

/-- Vaaler Theorem 16 (the sharp cosecant/Hilbert-form bound), unconditional. -/
theorem vaaler_thm16_closed
    {N : ℕ} (lam : Fin N → ℝ) (a : Fin N → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsp : ∀ m n, m ≠ n → δ ≤ |lam m - lam n|) :
    ‖hilbertForm lam a‖ ≤ (π / δ) * ∑ n, ‖a n‖ ^ 2 :=
  vaaler_thm16_of_beurlingMajorant
    vaalerBeurlingMajorant_closed lam a hδ hsp

#print axioms cor7IBP_closed
#print axioms cor7DerivMultiplication_closed
#print axioms excessFarFourier_closed
#print axioms vaalerBeurlingMajorant_closed
#print axioms vaaler_thm16_closed

end MathExtras.NumberTheory.Analysis.VaalerCor7Closed

end
