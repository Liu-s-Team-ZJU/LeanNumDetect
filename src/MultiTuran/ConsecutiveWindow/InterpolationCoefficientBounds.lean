import MultiTuran.ConsecutiveWindow.InterpolationContourData

/-! # The literal uniform Newton coefficient bound

The logarithmic rectangle integral retains the Jacobian `exp w`, so its
weighted boundary length is bounded by `6π`, exactly as in the sector proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
open Set Complex MeasureTheory

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

theorem windowNewtonCoefficient_norm_le {n : ℕ} (hn : 2 ≤ n)
    (frequency : Fin n → ℝ) (hfrequency : ∀ j, |frequency j| ≤ Real.pi-Real.pi/(n : ℝ))
    {t : ℝ} (ht0 : 0 ≤ t) (htn : t≤n) (k : Fin n) :
    ‖windowNewtonCoefficient frequency t k‖ ≤ 3*(1+1/(n : ℝ))^n*(n : ℝ)^(k.val+1) := by
  let B : ℝ := (1+1/(n : ℝ))^n*(n : ℝ)^(k.val+1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA := windowContourAngle_bounds hn
  have hr := windowContourRadii_bounds hn
  have hr0 : 0 < 1-1/(n : ℝ) := by linarith [hr.1]
  have hR0 : 0 < 1+1/(n : ℝ) := by linarith [hr.2.2.1]
  have hpoint (w : ℂ) (hw : WindowBoundary n w) :
      ‖windowNewtonKernel frequency t k.val w‖ ≤ Real.exp w.re*B := by
    convert windowNewtonKernel_norm_le hn frequency hfrequency ht0 htn k.isLt hw using 1
    dsimp [B]
    ring
  have hh (x : ℝ) (hx : x ∈ Icc (Real.log (1-1/(n : ℝ))) (Real.log (1+1/(n : ℝ))))
      (φ : ℝ) (hφ : φ= -windowContourAngle n ∨ φ=windowContourAngle n) :
      ‖windowNewtonKernel frequency t k.val (x+φ*I)‖ ≤ (1+1/(n : ℝ))*B := by
    have hw : WindowBoundary n (x+φ*I) := by
      rcases hφ with rfl | rfl
      · simpa only [Complex.ofReal_neg] using windowBoundary_bottom hn hx
      · exact windowBoundary_top hn hx
    have he : Real.exp (x+φ*I).re ≤ 1+1/(n : ℝ) := by
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero]
      exact (Real.exp_le_exp.mpr hx.2).trans_eq (Real.exp_log hR0)
    exact (hpoint _ hw).trans (mul_le_mul_of_nonneg_right he hB)
  have hvRight (y : ℝ) (hy : y ∈ Icc (-windowContourAngle n) (windowContourAngle n)) :
      ‖windowNewtonKernel frequency t k.val (Real.log (1+1/(n : ℝ))+y*I)‖ ≤ (1+1/(n : ℝ))*B := by
    have h := hpoint _ (windowBoundary_right hn hy)
    simpa only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
      sub_zero,add_zero,Real.exp_log hR0] using h
  have hvLeft (y : ℝ) (hy : y ∈ Icc (-windowContourAngle n) (windowContourAngle n)) :
      ‖windowNewtonKernel frequency t k.val (Real.log (1-1/(n : ℝ))+y*I)‖ ≤ (1-1/(n : ℝ))*B := by
    have h := hpoint _ (windowBoundary_left hn hy)
    simpa only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
      sub_zero,add_zero,Real.exp_log hr0] using h
  have hrect := norm_rectangleIntegral_le (windowNewtonKernel frequency t k.val)
    (windowContourLower n) (windowContourUpper n) ((1+1/(n : ℝ))*B) ((1+1/(n : ℝ))*B) ((1+1/(n : ℝ))*B) ((1-1/(n : ℝ))*B)
    (windowContour_real_order hn).le (by change -windowContourAngle n ≤ windowContourAngle n; linarith)
    (fun x hx => hh x hx _ (Or.inl rfl)) (fun x hx => hh x hx _ (Or.inr rfl)) hvRight hvLeft
  have hwidth : Real.log (1+1/(n : ℝ))-Real.log (1-1/(n : ℝ)) ≤ 2 := by
    have hupper := Real.log_le_log hR0 hr.2.2.2
    have hlower := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2) hr.1
    have hfixed : Real.log (3/2 : ℝ)-Real.log (1/2 : ℝ) ≤ 2 := by
      have he : (3/2 : ℝ)/(1/2)=3 := by norm_num
      rw [← Real.log_div (by norm_num) (by norm_num),he]
      simpa only [show (3 : ℝ)-1=2 by norm_num] using
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlength : 2*(1+1/(n : ℝ))*(Real.log (1+1/(n : ℝ))-Real.log (1-1/(n : ℝ)))+
      4*windowContourAngle n ≤ 6*Real.pi := by
    have hm := mul_le_mul (by linarith [hr.2.2.2] : 2*(1+1/(n : ℝ)) ≤ 3) hwidth
      (sub_nonneg.mpr (windowContour_real_order hn).le) (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith [hA.2,Real.pi_gt_three]
  have hrect' : ‖rectangleIntegral (windowNewtonKernel frequency t k.val)
      (windowContourLower n) (windowContourUpper n)‖ ≤ (6*Real.pi)*B := by
    apply hrect.trans
    convert mul_le_mul_of_nonneg_right hlength hB using 1 <;>
      dsimp [windowContourLower,windowContourUpper] <;> ring
  have hnorm : ‖(((2*Real.pi : ℝ) : ℂ)*I)⁻¹‖=1/(2*Real.pi) := by
    rw [norm_inv,norm_mul,Complex.norm_real,Complex.norm_I,mul_one,
      Real.norm_eq_abs,abs_of_pos (by positivity),one_div]
  unfold windowNewtonCoefficient
  rw [norm_mul,hnorm]
  calc
    _ ≤ (1/(2*Real.pi))*((6*Real.pi)*B) :=
      mul_le_mul_of_nonneg_left hrect' (by positivity)
    _ = _ := by dsimp [B]; field_simp; ring

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
