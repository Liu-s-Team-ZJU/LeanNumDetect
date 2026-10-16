import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # The Cauchy formula on an axis-parallel rectangle

The pole integral is evaluated using logarithm primitives on its four sides;
the general formula follows by removing the pole and applying Goursat.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Complex Set MeasureTheory
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

def rectangleIntegral (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  (∫ x : ℝ in a.re..b.re, f (x + a.im * I)) -
  (∫ x : ℝ in a.re..b.re, f (x + b.im * I)) +
  I * (∫ y : ℝ in a.im..b.im, f (b.re + y * I)) -
  I * (∫ y : ℝ in a.im..b.im, f (a.re + y * I))

private theorem log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    log (-z) = log z - (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re]
  · simp [log_im, arg_neg_eq_arg_sub_pi_of_im_pos hz]

private theorem log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    log (-z) = log z + (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re]
  · simp [log_im, arg_neg_eq_arg_add_pi_of_im_neg hz]

private theorem integral_affine_inv_eq_log_sub (v c : ℂ) (r s : ℝ)
    (hslit : ∀ t ∈ uIcc r s, (t : ℂ) * v + c ∈ slitPlane) :
    (∫ t : ℝ in r..s, v * ((t : ℂ) * v + c)⁻¹) =
      log ((s : ℂ) * v + c) - log ((r : ℂ) * v + c) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    simpa only [ofRealCLM_apply, ofReal_one, one_mul, div_eq_mul_inv] using
      (((ofRealCLM.hasDerivAt (x := t)).mul_const v).add_const c).clog_real (hslit t ht)
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    exact ((((continuous_ofReal.continuousAt.mul_const v).add_const c).inv₀
      (slitPlane_ne_zero (hslit t ht))).const_mul v).continuousWithinAt

theorem rectangleIntegral_pole (a b w₀ : ℂ)
    (hleft : a.re < w₀.re) (hright : w₀.re < b.re)
    (hbottom : a.im < w₀.im) (htop : w₀.im < b.im) :
    rectangleIntegral (fun w => 1 / (w - w₀)) a b =
      (2 * Real.pi : ℂ) * I := by
  let bl : ℂ := a.re + a.im * I - w₀
  let br : ℂ := b.re + a.im * I - w₀
  let tr : ℂ := b.re + b.im * I - w₀
  let tl : ℂ := a.re + b.im * I - w₀
  have hb : (∫ x : ℝ in a.re..b.re, 1 / ((x : ℂ) + a.im * I - w₀)) =
      log br - log bl := by
    simpa only [mul_one, one_mul, one_div, add_sub_assoc, br, bl] using
      integral_affine_inv_eq_log_sub 1 (a.im * I - w₀) a.re b.re (by
        intro t _
        apply mem_slitPlane_iff.mpr
        right
        simpa using (sub_ne_zero.mpr hbottom.ne))
  have ht : (∫ x : ℝ in a.re..b.re, 1 / ((x : ℂ) + b.im * I - w₀)) =
      log tr - log tl := by
    simpa only [mul_one, one_mul, one_div, add_sub_assoc, tr, tl] using
      integral_affine_inv_eq_log_sub 1 (b.im * I - w₀) a.re b.re (by
        intro t _
        apply mem_slitPlane_iff.mpr
        right
        simpa using (sub_ne_zero.mpr htop.ne'))
  have hr : I * (∫ y : ℝ in a.im..b.im,
      1 / (b.re + (y : ℂ) * I - w₀)) = log tr - log br := by
    have h := integral_affine_inv_eq_log_sub I ((b.re : ℂ) - w₀) a.im b.im (by
      intro t _
      apply mem_slitPlane_iff.mpr
      left
      simpa using sub_pos.mpr hright)
    have heq (t : ℝ) : (t : ℂ) * I + ((b.re : ℂ) - w₀) =
        b.re + (t : ℂ) * I - w₀ := by ring
    simpa only [heq, intervalIntegral.integral_const_mul, one_div, tr, br] using h
  have hl : I * (∫ y : ℝ in a.im..b.im,
      1 / (a.re + (y : ℂ) * I - w₀)) = log (-tl) - log (-bl) := by
    have h := integral_affine_inv_eq_log_sub (-I) (w₀ - (a.re : ℂ)) a.im b.im (by
      intro t _
      apply mem_slitPlane_iff.mpr
      left
      simpa using sub_pos.mpr hleft)
    have heq (t : ℝ) : (t : ℂ) * -I + (w₀ - a.re) =
        -(a.re + (t : ℂ) * I - w₀) := by ring
    simpa only [heq, inv_neg, neg_mul_neg, intervalIntegral.integral_const_mul,
      one_div, tl, bl] using h
  have hbli : bl.im < 0 := by simpa [bl] using sub_neg.mpr hbottom
  have htli : 0 < tl.im := by simpa [tl] using sub_pos.mpr htop
  rw [log_neg_of_im_pos htli, log_neg_of_im_neg hbli] at hl
  dsimp only [rectangleIntegral]
  rw [hb, ht, hr, hl]
  ring

def RectangleBoundaryIntegrable (f : ℂ → ℂ) (a b : ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f (x + a.im * I)) volume a.re b.re ∧
  IntervalIntegrable (fun x : ℝ => f (x + b.im * I)) volume a.re b.re ∧
  IntervalIntegrable (fun y : ℝ => f (b.re + y * I)) volume a.im b.im ∧
  IntervalIntegrable (fun y : ℝ => f (a.re + y * I)) volume a.im b.im

theorem rectangleIntegral_add (f g : ℂ → ℂ) (a b : ℂ)
    (hf : RectangleBoundaryIntegrable f a b)
    (hg : RectangleBoundaryIntegrable g a b) :
    rectangleIntegral (fun w => f w + g w) a b =
      rectangleIntegral f a b + rectangleIntegral g a b := by
  simp only [rectangleIntegral,
    intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

theorem rectangleIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (a b : ℂ) :
    rectangleIntegral (fun w => c * f w) a b = c * rectangleIntegral f a b := by
  simp only [rectangleIntegral, intervalIntegral.integral_const_mul]
  ring

theorem rectangleIntegral_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℂ → ℂ) (a b : ℂ)
    (hf : ∀ i ∈ s, RectangleBoundaryIntegrable (f i) a b) :
    rectangleIntegral (fun w => ∑ i ∈ s, f i w) a b =
      ∑ i ∈ s, rectangleIntegral (f i) a b := by
  simp only [rectangleIntegral,
    intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).1),
    intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).2.1),
    intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).2.2.1),
    intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).2.2.2),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem norm_rectangleIntegral_le (f : ℂ → ℂ) (a b : ℂ)
    (Bbottom Btop Bright Bleft : ℝ)
    (habre : a.re ≤ b.re) (habim : a.im ≤ b.im)
    (hbottom : ∀ x ∈ Icc a.re b.re, ‖f ((x : ℂ) + a.im * I)‖ ≤ Bbottom)
    (htop : ∀ x ∈ Icc a.re b.re, ‖f ((x : ℂ) + b.im * I)‖ ≤ Btop)
    (hright : ∀ y ∈ Icc a.im b.im, ‖f (b.re + (y : ℂ) * I)‖ ≤ Bright)
    (hleft : ∀ y ∈ Icc a.im b.im, ‖f (a.re + (y : ℂ) * I)‖ ≤ Bleft) :
    ‖rectangleIntegral f a b‖ ≤
      (b.re - a.re) * (Bbottom + Btop) + (b.im - a.im) * (Bright + Bleft) := by
  have hb : ‖∫ x : ℝ in a.re..b.re, f (x + a.im * I)‖ ≤
      Bbottom * (b.re - a.re) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a.re) (b := b.re) (fun x hx => hbottom x
        (by simpa only [uIcc_of_le habre] using uIoc_subset_uIcc hx))
    simpa only [abs_of_nonneg (sub_nonneg.mpr habre)] using h
  have ht : ‖∫ x : ℝ in a.re..b.re, f (x + b.im * I)‖ ≤
      Btop * (b.re - a.re) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a.re) (b := b.re) (fun x hx => htop x
        (by simpa only [uIcc_of_le habre] using uIoc_subset_uIcc hx))
    simpa only [abs_of_nonneg (sub_nonneg.mpr habre)] using h
  have hr : ‖∫ y : ℝ in a.im..b.im, f (b.re + y * I)‖ ≤
      Bright * (b.im - a.im) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a.im) (b := b.im) (fun y hy => hright y
        (by simpa only [uIcc_of_le habim] using uIoc_subset_uIcc hy))
    simpa only [abs_of_nonneg (sub_nonneg.mpr habim)] using h
  have hl : ‖∫ y : ℝ in a.im..b.im, f (a.re + y * I)‖ ≤
      Bleft * (b.im - a.im) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a.im) (b := b.im) (fun y hy => hleft y
        (by simpa only [uIcc_of_le habim] using uIoc_subset_uIcc hy))
    simpa only [abs_of_nonneg (sub_nonneg.mpr habim)] using h
  calc
    ‖rectangleIntegral f a b‖ ≤
        ‖∫ x : ℝ in a.re..b.re, f (x + a.im * I)‖ +
        ‖∫ x : ℝ in a.re..b.re, f (x + b.im * I)‖ +
        ‖I * (∫ y : ℝ in a.im..b.im, f (b.re + y * I))‖ +
        ‖I * (∫ y : ℝ in a.im..b.im, f (a.re + y * I))‖ := by
      unfold rectangleIntegral
      exact (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ Bbottom * (b.re - a.re) + Btop * (b.re - a.re) +
        Bright * (b.im - a.im) + Bleft * (b.im - a.im) := by
      simp only [norm_mul, norm_I, one_mul]
      exact add_le_add (add_le_add (add_le_add hb ht) hr) hl
    _ = _ := by ring

theorem rectangleBoundaryIntegrable_of_continuousOn {f : ℂ → ℂ} {a b : ℂ}
    (habre : a.re ≤ b.re) (habim : a.im ≤ b.im)
    (hf : ContinuousOn f (Icc a.re b.re ×ℂ Icc a.im b.im)) :
    RectangleBoundaryIntegrable f a b := by
  have hh (t : ℝ) (ht : t ∈ Icc a.im b.im) :
      IntervalIntegrable (fun x : ℝ => f (x + t * I)) volume a.re b.re := by
    apply ContinuousOn.intervalIntegrable
    apply hf.comp (by fun_prop)
    intro x hx
    rw [uIcc_of_le habre] at hx
    simpa [mem_reProdIm] using And.intro hx ht
  have hv (t : ℝ) (ht : t ∈ Icc a.re b.re) :
      IntervalIntegrable (fun y : ℝ => f (t + y * I)) volume a.im b.im := by
    apply ContinuousOn.intervalIntegrable
    apply hf.comp (by fun_prop)
    intro y hy
    rw [uIcc_of_le habim] at hy
    simpa [mem_reProdIm] using And.intro ht hy
  exact ⟨hh _ ⟨le_rfl, habim⟩, hh _ ⟨habim, le_rfl⟩,
    hv _ ⟨habre, le_rfl⟩, hv _ ⟨le_rfl, habre⟩⟩

theorem rectangleIntegral_eq_zero_of_differentiableOn (f : ℂ → ℂ) (a b : ℂ)
    (hf : DifferentiableOn ℂ f (uIcc a.re b.re ×ℂ uIcc a.im b.im)) :
    rectangleIntegral f a b = 0 := by
  simpa only [rectangleIntegral, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f a b hf

private theorem rectangleBoundaryIntegrable_pole (a b w₀ : ℂ)
    (hleft : a.re < w₀.re) (hright : w₀.re < b.re)
    (hbottom : a.im < w₀.im) (htop : w₀.im < b.im) :
    RectangleBoundaryIntegrable (fun w => 1 / (w - w₀)) a b := by
  have hh (t : ℝ) (ht : t ≠ w₀.im) :
      IntervalIntegrable (fun x : ℝ => 1 / ((x : ℂ) + t * I - w₀)) volume a.re b.re := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const (by fun_prop)
    intro x h
    have hi := congrArg Complex.im h
    simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, add_zero, zero_add, zero_im] at hi
    exact ht (sub_eq_zero.mp hi)
  have hv (t : ℝ) (ht : t ≠ w₀.re) :
      IntervalIntegrable (fun y : ℝ => 1 / (t + (y : ℂ) * I - w₀)) volume a.im b.im := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const (by fun_prop)
    intro y h
    have hr := congrArg Complex.re h
    simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_im, I_re,
      mul_one, mul_zero, sub_zero, add_zero, zero_re] at hr
    exact ht (sub_eq_zero.mp hr)
  exact ⟨hh _ hbottom.ne, hh _ htop.ne', hv _ hright.ne', hv _ hleft.ne⟩

theorem rectangle_cauchy_of_analyticOnNhd (f : ℂ → ℂ) (a b w₀ : ℂ)
    (hleft : a.re < w₀.re) (hright : w₀.re < b.re)
    (hbottom : a.im < w₀.im) (htop : w₀.im < b.im)
    (hf : AnalyticOnNhd ℂ f (Icc a.re b.re ×ℂ Icc a.im b.im)) :
    rectangleIntegral (fun w => f w / (w - w₀)) a b =
      ((2 * Real.pi : ℂ) * I) * f w₀ := by
  let g : ℂ → ℂ := dslope f w₀
  have habre : a.re ≤ b.re := (hleft.trans hright).le
  have habim : a.im ≤ b.im := (hbottom.trans htop).le
  have hnhds : (Icc a.re b.re ×ℂ Icc a.im b.im) ∈ nhds w₀ := by
    apply Filter.mem_of_superset
      ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds (show
        w₀ ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im from ⟨⟨hleft, hright⟩, ⟨hbottom, htop⟩⟩))
    intro w hw
    exact ⟨⟨hw.1.1.le, hw.1.2.le⟩, ⟨hw.2.1.le, hw.2.2.le⟩⟩
  have hg : DifferentiableOn ℂ g (Icc a.re b.re ×ℂ Icc a.im b.im) :=
    (Complex.differentiableOn_dslope hnhds).mpr hf.differentiableOn
  have hgzero : rectangleIntegral g a b = 0 := by
    apply rectangleIntegral_eq_zero_of_differentiableOn
    simpa only [uIcc_of_le habre, uIcc_of_le habim] using hg
  have hgint := rectangleBoundaryIntegrable_of_continuousOn habre habim hg.continuousOn
  have hpint := rectangleBoundaryIntegrable_pole a b w₀ hleft hright hbottom htop
  have hcint : RectangleBoundaryIntegrable (fun w => f w₀ * (1 / (w - w₀))) a b :=
    ⟨hpint.1.const_mul _, hpint.2.1.const_mul _,
      hpint.2.2.1.const_mul _, hpint.2.2.2.const_mul _⟩
  have hpoint (w : ℂ) (hw : w ≠ w₀) :
      f w / (w - w₀) = g w + f w₀ * (1 / (w - w₀)) := by
    dsimp only [g]
    rw [dslope_of_ne f hw, slope_def_field]
    ring
  have hh (t : ℝ) (ht : t ≠ w₀.im) (x : ℝ) :
      f ((x : ℂ) + t * I) / ((x : ℂ) + t * I - w₀) =
        g ((x : ℂ) + t * I) + f w₀ * (1 / ((x : ℂ) + t * I - w₀)) := by
    apply hpoint
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hv (t : ℝ) (ht : t ≠ w₀.re) (y : ℝ) :
      f (t + (y : ℂ) * I) / (t + (y : ℂ) * I - w₀) =
        g (t + (y : ℂ) * I) + f w₀ * (1 / (t + (y : ℂ) * I - w₀)) := by
    apply hpoint
    intro h
    exact ht (by simpa using congrArg Complex.re h)
  calc
    rectangleIntegral (fun w => f w / (w - w₀)) a b =
        rectangleIntegral (fun w => g w + f w₀ * (1 / (w - w₀))) a b := by
      unfold rectangleIntegral
      simp only [hh a.im hbottom.ne, hh b.im htop.ne',
        hv b.re hright.ne', hv a.re hleft.ne]
    _ = rectangleIntegral g a b +
        rectangleIntegral (fun w => f w₀ * (1 / (w - w₀))) a b :=
      rectangleIntegral_add _ _ _ _ hgint hcint
    _ = ((2 * Real.pi : ℂ) * I) * f w₀ := by
      rw [hgzero, rectangleIntegral_const_mul, rectangleIntegral_pole a b w₀
        hleft hright hbottom htop]
      ring

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
