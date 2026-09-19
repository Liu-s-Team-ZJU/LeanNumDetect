import Mathlib.Analysis.Fourier.AddCircle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace LeanNumDetect

/-- Unnormalized positive-sign Fourier integral on an interval of length 2π. -/
noncomputable def intervalAngularTransform (a : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x in a..a + 2 * Real.pi, f x * Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))

private theorem coefficient_normalization (a : ℝ) (f : ℝ → ℂ) (k : ℤ) :
    fourierCoeffOn (show a < a + 2 * Real.pi by linarith [Real.pi_pos]) f (-k) =
      ((2 * Real.pi)⁻¹ : ℝ) • intervalAngularTransform a f k := by
  rw [fourierCoeffOn_eq_integral]
  simp only [add_sub_cancel_left, one_div, neg_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [fourier_coe_apply, smul_eq_mul]
  have he : (2 : ℂ) * Real.pi * Complex.I * k * x / (2 * Real.pi) =
      Complex.I * (((k : ℝ) * x : ℝ) : ℂ) := by
    push_cast
    field_simp
  simp only [add_sub_cancel_left, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [he, mul_comm]
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast]

/-- Parseval with the angular-frequency and unnormalized-integral conventions used
in sampling estimates. Its proof is a normalization of mathlib's Fourier basis. -/
theorem hasSum_intervalAngularTransform (a : ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a (a + 2 * Real.pi)))) :
    HasSum (fun k : ℤ => ‖intervalAngularTransform a f k‖ ^ 2)
      ((2 * Real.pi) * ∫ x in a..a + 2 * Real.pi, ‖f x‖ ^ 2) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have h := hasSum_sq_fourierCoeffOn (show a < a + 2 * Real.pi by linarith) hf
  have hh := (Equiv.neg ℤ).hasSum_iff.mpr h
  simp only [Function.comp_def, Equiv.neg_apply, coefficient_normalization, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), mul_pow, add_sub_cancel_left,
    smul_eq_mul] at hh
  have he := hh.mul_left ((2 * Real.pi) ^ 2)
  have hfactor (v : ℝ) : (2 * Real.pi) ^ 2 * ((2 * Real.pi)⁻¹ ^ 2 * v) = v := by
    field_simp
  have hfactor' (v : ℝ) : (2 * Real.pi) ^ 2 * ((2 * Real.pi)⁻¹ * v) =
      2 * Real.pi * v := by
    field_simp
  simpa only [hfactor, hfactor'] using he

/-- Parseval on every shifted integer grid, covering both integer and half-integer
sampling without separate parity cases. -/
theorem hasSum_shifted_intervalAngularTransform (a shift : ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a (a + 2 * Real.pi)))) :
    HasSum (fun k : ℤ => ‖intervalAngularTransform a f ((k : ℝ) - shift)‖ ^ 2)
      ((2 * Real.pi) * ∫ x in a..a + 2 * Real.pi, ‖f x‖ ^ 2) := by
  let g : ℝ → ℂ := fun x => f x * Complex.exp (-(Complex.I * ((shift * x : ℝ) : ℂ)))
  have hg_norm (x : ℝ) : ‖g x‖ = ‖f x‖ := by
    simp [g, Complex.norm_exp, Complex.mul_re]
  have hg : MemLp g 2 (volume.restrict (Set.Ioc a (a + 2 * Real.pi))) := by
    apply hf.congr_norm
    · apply hf.aestronglyMeasurable.mul
      apply Continuous.aestronglyMeasurable
      fun_prop
    · exact Filter.Eventually.of_forall (fun x => (hg_norm x).symm)
  have he (k : ℤ) : intervalAngularTransform a g k =
      intervalAngularTransform a f ((k : ℝ) - shift) := by
    unfold intervalAngularTransform
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [g]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hh := hasSum_intervalAngularTransform a g hg
  simpa only [he, hg_norm] using hh
/-- Compactly supported functions can use the full real-line Fourier integral.
The support condition is stated pointwise so it also controls the squared norm. -/
theorem hasSum_angularTransform_of_support (a shift : ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a (a + 2 * Real.pi))))
    (hs : ∀ x, x ∉ Set.Ioc a (a + 2 * Real.pi) → f x = 0) :
    HasSum (fun k : ℤ => ‖∫ x : ℝ, f x *
        Complex.exp (Complex.I * ((((k : ℝ) - shift) * x : ℝ) : ℂ))‖ ^ 2)
      ((2 * Real.pi) * ∫ x : ℝ, ‖f x‖ ^ 2) := by
  have hi (t : ℝ) : intervalAngularTransform a f t =
      ∫ x : ℝ, f x * Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) := by
    rw [intervalAngularTransform, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hs x hx, zero_mul]
  have hn : (∫ x in a..a + 2 * Real.pi, ‖f x‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [hs x hx, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  simpa only [hi, hn] using hasSum_shifted_intervalAngularTransform a shift f hf

end LeanNumDetect
