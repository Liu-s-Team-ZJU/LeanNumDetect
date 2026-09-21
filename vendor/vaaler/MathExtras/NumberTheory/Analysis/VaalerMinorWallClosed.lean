/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCesPointwiseAE
import MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ
import MathExtras.NumberTheory.Analysis.VaalerInterpHContinuous
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# The Vaaler minor wall, closed

This file records the consumer-facing consequences of the source-level Cesàro
argument in `VaalerGCesPointwiseAE`.  In particular, the explicit half
derivative `GC` is the inverse transform `vaalerJ`, and the formerly bundled
identity `DerivInterpHEqTwoJ` is now a theorem.
-/

noncomputable section

namespace MathExtras.NumberTheory.Analysis.VaalerMinorWallClosed

open MathExtras.NumberTheory.Analysis.VaalerGCesPointwiseAE
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
open MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ
open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerCor7RouteB
open MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail
open MathExtras.NumberTheory.Analysis.VaalerInterpHContinuous

/-- The two Fourier transforms agree, with the one-sided Cesàro transform
identity supplied by `minorWall_closed` and the now-proven corner/decay data
for `vaalerJ`. -/
theorem gcFTeqJ_closed :
    MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch.GCFTeqJ :=
  gcFTeqJ_of_hat minorWall_closed
    MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ.vaalerJhatContCornerOne_holds
    MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ.vaalerJTwoIBPDecay_holds

/-- Fourier uniqueness identifies the concrete half derivative with the
band-limited inverse transform pointwise. -/
theorem gcEqVaalerJSpatial_closed :
    MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatTransform.GCEqVaalerJSpatial :=
  gcEqVaalerJSpatial_of_GCFTeqJ gcFTeqJ_closed

/-- The explicit Vaaler identity `H' = 2J` (in the repository's bundled
positive-axis, off-lattice form) is unconditional. -/
theorem derivInterpHEqTwoJ_closed :
    MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail.DerivInterpHEqTwoJ :=
  derivInterpHEqTwoJ_of_GCFTeqJ gcFTeqJ_closed

/-- The same derivative identity in the global off-lattice form used by the
Fourier integration-by-parts route.  The negative half-line follows from the
oddness of `interpH` and the evenness of `vaalerJ`. -/
theorem derivInterpHIsTwoJ_closed : DerivInterpHIsTwoJ := by
  intro x hs
  have hxrange : x ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨n, rfl⟩
    apply hs
    rw [show Real.pi * (n : ℝ) = (n : ℝ) * Real.pi by ring,
      Real.sin_int_mul_pi]
  have hxne : x ≠ 0 := by
    intro hx
    apply hs
    rw [hx, mul_zero, Real.sin_zero]
  rcases lt_or_gt_of_ne hxne with hxneg | hxpos
  · have hnegRange : -x ∉ Set.range ((↑) : ℤ → ℝ) := by
      rintro ⟨n, hn⟩
      apply hxrange
      refine ⟨-n, ?_⟩
      push_cast
      linarith
    have hbase : HasDerivAt interpH (2 * (vaalerJ (-x)).re) (-x) :=
      derivInterpHIsTwoJ_pos_of_eq derivInterpHEqTwoJ_closed (by linarith) hnegRange
    have hreflection : HasDerivAt (fun y : ℝ => -interpH (-y))
        (2 * (vaalerJ x).re) x := by
      have hneg : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := by
        refine (hasDerivAt_id x).neg.congr_of_eventuallyEq ?_
        filter_upwards with y
        rfl
      refine (((hbase.comp x hneg).neg).congr_deriv ?_).congr_of_eventuallyEq ?_
      · rw [vaalerJ_even]
        ring
      · filter_upwards with y
        simp only [Function.comp_apply, Pi.neg_apply]
    refine hreflection.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [interpH_neg]
    ring
  · exact derivInterpHIsTwoJ_pos_of_eq derivInterpHEqTwoJ_closed hxpos hxrange

/-! ## Removing the removable lattice exception -/

/-- The real derivative value `2·Re J` is continuous. -/
theorem continuous_two_mul_re_vaalerJ :
    Continuous (fun x : ℝ => 2 * (vaalerJ x).re) := by
  have hJ : Continuous vaalerJ := by
    rw [← gcEqVaalerJSpatial_closed]
    exact MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ.gContinuous_holds
  fun_prop

/-- Fundamental theorem for `interpH`, allowing the integer lattice as the
countable exceptional set in the derivative computation. -/
theorem integral_two_mul_re_vaalerJ_eq_sub (a b : ℝ) :
    (∫ x in a..b, 2 * (vaalerJ x).re) = interpH b - interpH a := by
  apply MeasureTheory.integral_eq_of_hasDerivAt_off_countable
      interpH (fun x : ℝ => 2 * (vaalerJ x).re)
      (Set.countable_range ((↑) : ℤ → ℝ))
  · exact interpH_continuous.continuousOn
  · intro x hx
    exact derivInterpHIsTwoJ_closed x (sin_pi_mul_ne_zero_of_notMem hx.2)
  · exact continuous_two_mul_re_vaalerJ.intervalIntegrable _ _

/-- **Global Vaaler derivative identity.**  The countable-exception FTC first
identifies `interpH` with the primitive of the continuous function `2·Re J`;
FTC-1 then supplies the derivative at the removable integer points as well.
Thus `H' = 2J` now holds at every real point, not merely off the lattice. -/
theorem hasDerivAt_interpH_two_mul_re_vaalerJ (x : ℝ) :
    HasDerivAt interpH (2 * (vaalerJ x).re) x := by
  have hprim : HasDerivAt
      (fun u : ℝ => ∫ t in (0 : ℝ)..u, 2 * (vaalerJ t).re)
      (2 * (vaalerJ x).re) x :=
    intervalIntegral.integral_hasDerivAt_right
      (continuous_two_mul_re_vaalerJ.intervalIntegrable 0 x)
      continuous_two_mul_re_vaalerJ.aestronglyMeasurable.stronglyMeasurableAtFilter
      continuous_two_mul_re_vaalerJ.continuousAt
  have hzero : interpH 0 = 0 := by
    unfold interpH
    simp
  have hfun : (fun u : ℝ => ∫ t in (0 : ℝ)..u, 2 * (vaalerJ t).re) = interpH := by
    funext u
    rw [integral_two_mul_re_vaalerJ_eq_sub, hzero, sub_zero]
  rwa [hfun] at hprim

#print axioms gcFTeqJ_closed
#print axioms gcEqVaalerJSpatial_closed
#print axioms derivInterpHEqTwoJ_closed
#print axioms derivInterpHIsTwoJ_closed
#print axioms integral_two_mul_re_vaalerJ_eq_sub
#print axioms hasDerivAt_interpH_two_mul_re_vaalerJ

end MathExtras.NumberTheory.Analysis.VaalerMinorWallClosed

end
