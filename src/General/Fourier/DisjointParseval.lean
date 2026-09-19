import General.Fourier.ShiftedParseval
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace LeanNumDetect

/-- A real cross term vanishes when the two functions have disjoint supports. -/
theorem hasSum_realCross_interval_of_disjoint (a shift : ℝ) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a (a+2*Real.pi))))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc a (a+2*Real.pi))))
    (hdis : ∀ x, f x = 0 ∨ g x = 0) :
    HasSum (fun k : ℤ => 2 * (star (intervalAngularTransform a f ((k : ℝ)-shift)) *
      intervalAngularTransform a g ((k : ℝ)-shift)).re) 0 := by
  have hp : a ≤ a+2*Real.pi := by linarith [Real.pi_pos]
  have hi (u : ℝ → ℂ) (hu : MemLp u 2 (volume.restrict (Set.Ioc a (a+2*Real.pi)))) (t : ℝ) :
      IntervalIntegrable (fun x => u x * Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))) volume a (a+2*Real.pi) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hp).2
    apply (hu.integrable (by norm_num)).mul_bdd (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · exact Filter.Eventually.of_forall (fun x => by simp [Complex.norm_exp, Complex.mul_re])
  have hadd (t : ℝ) : intervalAngularTransform a (f+g) t =
      intervalAngularTransform a f t + intervalAngularTransform a g t := by
    unfold intervalAngularTransform
    simp only [Pi.add_apply, add_mul]
    exact intervalIntegral.integral_add (hi f hf t) (hi g hg t)
  have hnorm (x : ℝ) : ‖(f+g) x‖^2 = ‖f x‖^2 + ‖g x‖^2 := by
    rcases hdis x with hx | hx <;> simp [Pi.add_apply, hx]
  have hint : (∫ x in a..a+2*Real.pi, ‖(f+g) x‖^2) =
      (∫ x in a..a+2*Real.pi, ‖f x‖^2) + ∫ x in a..a+2*Real.pi, ‖g x‖^2 := by
    simp only [hnorm, intervalIntegral.integral_of_le hp]
    exact integral_add (hf.integrable_norm_pow (by norm_num)) (hg.integrable_norm_pow (by norm_num))
  have hh := ((hasSum_shifted_intervalAngularTransform a shift (f+g) (hf.add hg)).sub
    (hasSum_shifted_intervalAngularTransform a shift f hf)).sub
    (hasSum_shifted_intervalAngularTransform a shift g hg)
  rw [hint] at hh
  have he (z w : ℂ) : ‖z+w‖^2 - ‖z‖^2 - ‖w‖^2 = 2 * (star z * w).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hz (x y : ℝ) : 2*Real.pi*(x+y)-2*Real.pi*x-2*Real.pi*y = 0 := by ring
  simpa only [hadd, he, hz] using hh

/-- The same orthogonality for full real-line Fourier integrals. -/
theorem hasSum_realCross_of_disjoint_support (a shift : ℝ) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a (a+2*Real.pi))))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc a (a+2*Real.pi))))
    (hsf : ∀ x, x ∉ Set.Ioc a (a+2*Real.pi) → f x = 0)
    (hsg : ∀ x, x ∉ Set.Ioc a (a+2*Real.pi) → g x = 0)
    (hdis : ∀ x, f x = 0 ∨ g x = 0) :
    HasSum (fun k : ℤ => 2 * (star (∫ x : ℝ, f x *
      Complex.exp (Complex.I * ((((k : ℝ)-shift)*x : ℝ) : ℂ))) *
      (∫ x : ℝ, g x * Complex.exp (Complex.I * ((((k : ℝ)-shift)*x : ℝ) : ℂ)))).re) 0 := by
  have hi (u : ℝ → ℂ) (hu : ∀ x, x ∉ Set.Ioc a (a+2*Real.pi) → u x = 0) (t : ℝ) :
      intervalAngularTransform a u t = ∫ x : ℝ, u x * Complex.exp (Complex.I * ((t*x : ℝ) : ℂ)) := by
    rw [intervalAngularTransform, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hu x hx, zero_mul]
  simpa only [hi f hsf, hi g hsg] using hasSum_realCross_interval_of_disjoint a shift f g hf hg hdis
noncomputable def angularTransform (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))

theorem angularTransform_translate_mul (p : ℝ → ℂ) (c : ℂ) (d t : ℝ) :
    angularTransform (fun x => c * p (x-d)) t =
      c * angularTransform p t * Complex.exp (Complex.I * ((t*d : ℝ) : ℂ)) := by
  unfold angularTransform
  rw [← integral_add_right_eq_self (fun x : ℝ => c * p (x-d) *
    Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))) d]
  have he (x : ℝ) : Complex.I * ((t*(x+d) : ℝ) : ℂ) =
      Complex.I * ((t*x : ℝ) : ℂ) + Complex.I * ((t*d : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [add_sub_cancel_right, he, Complex.exp_add, ← mul_assoc]
  rw [integral_mul_const]
  congr 1
  simp only [mul_assoc]
  exact integral_const_mul _ _

/-- Orthogonality of separated translates of a compact kernel, on any shifted grid. -/
theorem compact_kernel_realCross {p : ℝ → ℂ} {eta gap : ℝ}
    (hp : Integrable p) (B : ℝ) (hbound : ∀ x, ‖p x‖ ≤ B)
    (hsupp : ∀ x, x ∉ Set.Icc (-eta/2) (eta/2) → p x = 0)
    (hgap : eta < gap) (hwidth : gap + eta < 2*Real.pi)
    (c₁ c₂ : ℂ) (shift : ℝ) :
    HasSum (fun k : ℤ => ‖angularTransform p ((k : ℝ)-shift)‖^2 *
      (2 * (star c₁ * c₂ * Complex.exp (Complex.I * ((((k : ℝ)-shift)*gap : ℝ) : ℂ))).re)) 0 := by
  let a := gap/2 - Real.pi
  let f : ℝ → ℂ := fun x => c₁ * p x
  let g : ℝ → ℂ := fun x => c₂ * p (x-gap)
  have hmem (c : ℂ) (d : ℝ) : MemLp (fun x => c * p (x-d)) 2
      (volume.restrict (Set.Ioc a (a+2*Real.pi))) := by
    apply MemLp.of_bound
      (((hp.comp_sub_right d).const_mul c).aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      (‖c‖ * B)
    exact Filter.Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _))
  have hsf : ∀ x, x ∉ Set.Ioc a (a+2*Real.pi) → f x = 0 := by
    intro x hx
    have hh : x ∉ Set.Icc (-eta/2) (eta/2) := by
      intro hh
      apply hx
      dsimp [a]
      constructor <;> linarith [hh.1,hh.2]
    simp [f, hsupp x hh]
  have hsg : ∀ x, x ∉ Set.Ioc a (a+2*Real.pi) → g x = 0 := by
    intro x hx
    have hh : x-gap ∉ Set.Icc (-eta/2) (eta/2) := by
      intro hh
      apply hx
      dsimp [a]
      constructor <;> linarith [hh.1,hh.2]
    simp [g, hsupp (x-gap) hh]
  have hdis (x : ℝ) : f x = 0 ∨ g x = 0 := by
    by_cases hx : x ∈ Set.Icc (-eta/2) (eta/2)
    · right
      have hh : x-gap ∉ Set.Icc (-eta/2) (eta/2) := by
        intro hh
        linarith [hx.2,hh.1]
      simp [g, hsupp (x-gap) hh]
    · left
      simp [f, hsupp x hx]
  have hf : MemLp f 2 (volume.restrict (Set.Ioc a (a+2*Real.pi))) := by
    simpa only [sub_zero] using hmem c₁ 0
  have hh := hasSum_realCross_of_disjoint_support a shift f g hf (hmem c₂ gap) hsf hsg hdis
  change HasSum (fun k : ℤ => 2 * (star (angularTransform f ((k : ℝ)-shift)) *
    angularTransform g ((k : ℝ)-shift)).re) 0 at hh
  have hft (t : ℝ) : angularTransform f t = c₁ * angularTransform p t := by
    have hh := angularTransform_translate_mul p c₁ 0 t
    simpa [f] using hh
  have hgt (t : ℝ) : angularTransform g t = c₂ * angularTransform p t *
      Complex.exp (Complex.I * ((t*gap : ℝ) : ℂ)) := angularTransform_translate_mul p c₂ gap t
  have he (z w : ℂ) : 2 * (star (c₁*z) * (c₂*z*w)).re =
      ‖z‖^2 * (2 * (star c₁*c₂*w).re) := by
    rw [star_mul]
    have hz : star z * z = ((‖z‖^2 : ℝ) : ℂ) := by
      rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
      rfl
    rw [show star z * star c₁ * (c₂*z*w) = (star z*z)*(star c₁*c₂*w) by ring, hz]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  simpa only [hft,hgt,he] using hh
end LeanNumDetect
