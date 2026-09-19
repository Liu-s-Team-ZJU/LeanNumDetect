import General.Fourier.CosineGammaIntegral
import General.Fourier.CosineWindowDerivative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace LeanNumDetect

theorem windowTransform_re_interval (s : ℕ) {eta : ℝ} (heta : 0 < eta) (t : ℝ) :
    (windowTransform s eta t).re =
      ∫ x in -eta/2..eta/2, Real.cos (Real.pi*x/eta)^(2*s)*Real.cos (t*x) := by
  have hf := clipped_fourier_integral (cosineProfile s eta) (by linarith : -eta/2 ≤ eta/2) t
  change windowTransform s eta t = _ at hf
  rw [hf]
  have hi : IntervalIntegrable (fun x : ℝ => (cosineProfile s eta x : ℂ)*
      Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))) volume (-eta/2) (eta/2) := by
    apply Continuous.intervalIntegrable
    dsimp [cosineProfile]
    fun_prop
  have hr := intervalIntegral.intervalIntegral_re hi
  change (∫ x in -eta/2..eta/2, ((cosineProfile s eta x : ℂ)*
    Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))).re) =
    (∫ x in -eta/2..eta/2, (cosineProfile s eta x : ℂ)*
      Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))).re at hr
  rw [← hr]
  apply intervalIntegral.integral_congr
  intro x _
  have he : (Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))).re = Real.cos (t*x) := by
    simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  dsimp only
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, he]
  rfl

theorem cosine_even_integral (s : ℕ) (v : ℝ) :
    (∫ x in -Real.pi/2..Real.pi/2, Real.cos x^(2*s)*Real.cos (2*v*x)) =
      2 * ∫ x in (0 : ℝ)..Real.pi/2, Real.cos x^(2*s)*Real.cos (2*v*x) := by
  let f (x : ℝ) := Real.cos x^(2*s)*Real.cos (2*v*x)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have he (x : ℝ) : f (-x) = f x := by simp [f]
  have hn := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := Real.pi/2) f
  simp only [he, neg_zero] at hn
  rw [← neg_div] at hn
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (-Real.pi/2) 0)
    (hf.intervalIntegrable 0 (Real.pi/2)), ← hn]
  ring

theorem windowTransform_re_scaled (s : ℕ) {eta : ℝ} (heta : 0 < eta) (t : ℝ) :
    (windowTransform s eta t).re =
      (2*eta/Real.pi) * ∫ x in (0 : ℝ)..Real.pi/2,
        Real.cos (2*(eta*t/(2*Real.pi))*x)*Real.cos x^(2*s) := by
  rw [windowTransform_re_interval s heta]
  let v := eta*t/(2*Real.pi)
  let f (x : ℝ) := Real.cos x^(2*s)*Real.cos (2*v*x)
  have harg (x : ℝ) : f ((Real.pi/eta)*x) =
      Real.cos (Real.pi*x/eta)^(2*s)*Real.cos (t*x) := by
    dsimp [f,v]
    congr 2 <;> field_simp
  have hi := intervalIntegral.integral_comp_mul_left (a := -eta/2) (b := eta/2) f
    (div_ne_zero Real.pi_ne_zero heta.ne')
  have hl : (Real.pi/eta)*(-eta/2) = -Real.pi/2 := by field_simp
  have hr : (Real.pi/eta)*(eta/2) = Real.pi/2 := by field_simp
  simp only [harg,hl,hr,smul_eq_mul] at hi
  rw [hi]
  change (Real.pi/eta)⁻¹ * (∫ x in -Real.pi/2..Real.pi/2,
    Real.cos x^(2*s)*Real.cos (2*v*x)) = _
  rw [cosine_even_integral]
  have he : (∫ x in (0 : ℝ)..Real.pi/2, Real.cos x^(2*s)*Real.cos (2*v*x)) =
      ∫ x in (0 : ℝ)..Real.pi/2, Real.cos (2*v*x)*Real.cos x^(2*s) := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [he]
  dsimp [v]
  field_simp
theorem windowTransform_re_normalized (s : ℕ) {eta : ℝ} (heta : 0 < eta) (t : ℝ) :
    (windowTransform s eta t).re =
      windowMass s eta * normalizedCosineIntegral s (eta*t/(2*Real.pi)) := by
  have hm := windowTransform_re_scaled s heta 0
  rw [windowTransform_zero, Complex.ofReal_re] at hm
  simp only [mul_zero, zero_div, zero_mul, Real.cos_zero, one_mul] at hm
  change windowMass s eta = (2*eta/Real.pi)*cosineHalfMass s at hm
  rw [windowTransform_re_scaled s heta, hm]
  unfold normalizedCosineIntegral
  have hp := (cosineHalfMass_pos s).ne'
  field_simp

/-- The Fourier transform of the even real window is real. -/
theorem windowTransform_im_zero (s : ℕ) {eta : ℝ} (heta : 0 < eta) (t : ℝ) :
    (windowTransform s eta t).im = 0 := by
  have hf := clipped_fourier_integral (cosineProfile s eta) (by linarith : -eta/2 ≤ eta/2) t
  change windowTransform s eta t = _ at hf
  rw [hf]
  have hi : IntervalIntegrable (fun x : ℝ => (cosineProfile s eta x : ℂ)*
      Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))) volume (-eta/2) (eta/2) := by
    apply Continuous.intervalIntegrable
    dsimp [cosineProfile]
    fun_prop
  have him := intervalIntegral.intervalIntegral_im hi
  change (∫ x in -eta/2..eta/2, ((cosineProfile s eta x : ℂ)*
    Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))).im) =
    (∫ x in -eta/2..eta/2, (cosineProfile s eta x : ℂ)*
      Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))).im at him
  rw [← him]
  have he (x : ℝ) : ((cosineProfile s eta x : ℂ)*
      Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))).im =
      Real.cos (Real.pi*x/eta)^(2*s)*Real.sin (t*x) := by
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    rw [show (Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))).im = Real.sin (t*x) by
      simp [Complex.exp_im,Complex.mul_re,Complex.mul_im]]
    rfl
  simp_rw [he]
  let g (x : ℝ) := Real.cos (Real.pi*x/eta)^(2*s)*Real.sin (t*x)
  have hg (x : ℝ) : g (-x) = -g x := by simp [g,neg_div]
  have hh := intervalIntegral.integral_comp_neg (a := -eta/2) (b := eta/2) g
  simp only [hg,intervalIntegral.integral_neg,neg_div,neg_neg] at hh
  change (∫ x in -eta/2..eta/2, g x) = 0
  simp only [neg_div]
  linarith

/-- The normalization constant used by the Gamma expression. -/
theorem windowMass_eq_factorial (s : ℕ) {eta : ℝ} (heta : 0 < eta) :
    windowMass s eta = eta * ((2*s).factorial : ℝ) /
      (4^s*(s.factorial : ℝ)^2) := by
  have hm := windowTransform_re_scaled s heta 0
  rw [windowTransform_zero,Complex.ofReal_re] at hm
  simp only [mul_zero,zero_div,zero_mul,Real.cos_zero,one_mul] at hm
  change windowMass s eta = (2*eta/Real.pi)*cosineHalfMass s at hm
  rw [hm,cosineHalfMass_eq_factorial]
  field_simp

/-- The manuscript's Gamma formula on a neighborhood of the entire core interval.
Integer parameters are included by the continuity argument in the integral theorem. -/
theorem windowTransform_eq_gamma (s : ℕ) {eta : ℝ} (heta : 0 < eta) (t : ℝ)
    (ht : |eta*t/(2*Real.pi)| < s+1) :
    windowTransform s eta t =
      ((eta * ((2*s).factorial : ℝ) /
        (4^s*Real.Gamma (s+1+eta*t/(2*Real.pi))*
          Real.Gamma (s+1-eta*t/(2*Real.pi))) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    rw [windowTransform_re_normalized s heta t,normalizedCosineIntegral_eq_gamma s ht,
      windowMass_eq_factorial s heta]
    field_simp
  · simpa only [Complex.ofReal_im] using windowTransform_im_zero s heta t

/-- The exact Gamma quotient for the normalized Fourier kernel. -/
theorem windowTransform_norm_div_mass_eq_gamma (s : ℕ) {eta t : ℝ} (heta : 0 < eta)
    (ht : |eta*t/(2*Real.pi)| < s+1) :
    ‖windowTransform s eta t‖/windowMass s eta = (s.factorial : ℝ)^2 /
      (Real.Gamma (s+1+eta*t/(2*Real.pi))*Real.Gamma (s+1-eta*t/(2*Real.pi))) := by
  have hp : 0 < (s+1 : ℝ)+eta*t/(2*Real.pi) := by have := (abs_lt.mp ht).1; linarith
  have hm : 0 < (s+1 : ℝ)-eta*t/(2*Real.pi) := by have := (abs_lt.mp ht).2; linarith
  have hGp := Real.Gamma_pos_of_pos hp
  have hGm := Real.Gamma_pos_of_pos hm
  rw [windowTransform_eq_gamma s heta t ht,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity),windowMass_eq_factorial s heta]
  field_simp

/-- Log-convexity gives the sharper factorial-ratio bound stated in the manuscript. -/
theorem windowTransform_core_factorial_lower (s : ℕ) {eta t : ℝ} (heta : 0 < eta)
    (ht : |eta*t/(2*Real.pi)| ≤ s) :
    (s.factorial : ℝ)^2/((2*s).factorial : ℝ) ≤
      ‖windowTransform s eta t‖/windowMass s eta := by
  rw [windowTransform_norm_div_mass_eq_gamma s heta (by linarith),
    ← normalizedCosineIntegral_eq_gamma s (by linarith)]
  exact normalizedCosineIntegral_factorial_lower s ht

theorem windowTransform_core_lower (s : ℕ) {eta t : ℝ} (heta : 0 < eta)
    (ht : |eta*t/(2*Real.pi)| ≤ s) :
    1/(4 : ℝ)^s ≤ ‖windowTransform s eta t‖ / windowMass s eta :=
  (reciprocal_central_factorial_lower s).trans (windowTransform_core_factorial_lower s heta ht)

/-- The original tail-product proof remains available independently of Gamma. -/
theorem windowTransform_core_lower_of_tail_product (s : ℕ) {eta t : ℝ} (heta : 0 < eta)
    (ht : |eta*t/(2*Real.pi)| ≤ s) :
    1/(4 : ℝ)^s ≤ ‖windowTransform s eta t‖ / windowMass s eta := by
  have hm := windowMass_pos s heta
  have hc := normalizedCosineIntegral_lower s ht
  have hr : (windowTransform s eta t).re ≤ ‖windowTransform s eta t‖ := Complex.re_le_norm _
  rw [windowTransform_re_normalized s heta t] at hr
  apply (le_div_iff₀ hm).2
  have hh := mul_le_mul_of_nonneg_left hc hm.le
  exact (by simpa only [mul_comm] using hh : (1/(4 : ℝ)^s)*windowMass s eta ≤
    windowMass s eta * normalizedCosineIntegral s (eta*t/(2*Real.pi))).trans hr

theorem windowTransform_core_sq_lower (s : ℕ) {eta t : ℝ} (heta : 0 < eta)
    (ht : |eta*t/(2*Real.pi)| ≤ s) :
    1/(16 : ℝ)^s ≤ ‖windowTransform s eta t‖^2 / windowMass s eta^2 := by
  have hm := (windowMass_pos s heta).le
  have hh := (sq_le_sq₀ (by positivity) (by positivity)).2 (windowTransform_core_lower s heta ht)
  have hp : ((4 : ℝ)^s)^2 = 16^s := by rw [← pow_mul, Nat.mul_comm s 2, pow_mul]; norm_num
  simpa only [div_pow, one_pow, hp] using hh
end LeanNumDetect
