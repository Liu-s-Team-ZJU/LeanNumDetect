import General.Fourier.CosineWindowParseval
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace LeanNumDetect

noncomputable def cosineProfile (s : ℕ) (eta x : ℝ) : ℝ :=
  Real.cos (Real.pi * x / eta) ^ (2 * s)

noncomputable def cosineProfileSlope (s : ℕ) (eta x : ℝ) : ℝ :=
  -(2 * s : ℝ) * (Real.pi / eta) * Real.sin (Real.pi * x / eta) *
    Real.cos (Real.pi * x / eta) ^ (2 * s - 1)

noncomputable def cosineWindowSlope (s : ℕ) (eta : ℝ) : ℝ → ℝ :=
  (Set.Icc (-eta / 2) (eta / 2)).indicator (cosineProfileSlope s eta)

theorem cosineProfile_hasDerivAt (s : ℕ) (eta x : ℝ) :
    HasDerivAt (cosineProfile s eta) (cosineProfileSlope s eta x) x := by
  have hh := (((hasDerivAt_id x).const_mul Real.pi).div_const eta).cos.pow (2 * s)
  convert! hh using 1
  simp [cosineProfileSlope, Nat.cast_mul]
  ring

theorem cosineProfileSlope_continuous (s : ℕ) (eta : ℝ) :
    Continuous (cosineProfileSlope s eta) := by unfold cosineProfileSlope; fun_prop

theorem cosineWindowSlope_integrable (s : ℕ) (eta : ℝ) :
    Integrable (cosineWindowSlope s eta) := by
  exact (integrable_indicator_iff measurableSet_Icc).2
    (cosineProfileSlope_continuous s eta).integrableOn_Icc

theorem cosineProfile_boundary {s : ℕ} (hs : 1 ≤ s) {eta : ℝ} (heta : 0 < eta) :
    cosineProfile s eta (-eta / 2) = 0 ∧ cosineProfile s eta (eta / 2) = 0 := by
  have hn : 2 * s ≠ 0 := by omega
  have hp : Real.pi * (eta / 2) / eta = Real.pi / 2 := by field_simp
  have hm : Real.pi * (-eta / 2) / eta = -(Real.pi / 2) := by field_simp
  simp only [cosineProfile, hp, hm, Real.cos_neg, Real.cos_pi_div_two, zero_pow hn, and_self]

/-- Away from the two cutoff points, the slope is the actual derivative. -/
theorem cosineWindow_hasDerivAt_of_ne (s : ℕ) (eta x : ℝ)
    (hl : x ≠ -eta / 2) (hr : x ≠ eta / 2) :
    HasDerivAt (cosineWindow s eta) (cosineWindowSlope s eta x) x := by
  classical
  by_cases hx : x ∈ Set.Icc (-eta / 2) (eta / 2)
  · have hi : x ∈ Set.Ioo (-eta / 2) (eta / 2) :=
      ⟨lt_of_le_of_ne hx.1 hl.symm, lt_of_le_of_ne hx.2 hr⟩
    rw [cosineWindowSlope, Set.indicator_of_mem hx]
    apply (cosineProfile_hasDerivAt s eta x).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hi] with y hy
    simp only [cosineWindow, Set.indicator_of_mem (show y ∈ Set.Icc (-eta/2) (eta/2) from
      ⟨hy.1.le, hy.2.le⟩), cosineProfile]
  · rw [cosineWindowSlope, Set.indicator_of_notMem hx]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    exact Set.indicator_of_notMem hy _

theorem cosineWindow_deriv_ae (s : ℕ) (eta : ℝ) :
    deriv (cosineWindow s eta) =ᵐ[volume] cosineWindowSlope s eta := by
  have ha (a : ℝ) : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff]
  filter_upwards [ha (-eta / 2), ha (eta / 2)] with x hx hy
  exact (cosineWindow_hasDerivAt_of_ne s eta x hx hy).deriv

/-- Restricting a real profile to a closed interval has the expected Fourier integral. -/
theorem clipped_fourier_integral (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    (∫ x : ℝ, (((Set.Icc a b).indicator f x : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) =
    ∫ x in a..b, (f x : ℂ) * Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) := by
  classical
  have hh : (fun x : ℝ => (((Set.Icc a b).indicator f x : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) =
      (Set.Icc a b).indicator (fun x => (f x : ℂ) *
        Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b <;> simp [hx]
  rw [hh, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

theorem cosineWindowSlope_transform {s : ℕ} (hs : 1 ≤ s) {eta : ℝ} (heta : 0 < eta)
    (t : ℝ) :
    (∫ x : ℝ, (cosineWindowSlope s eta x : ℂ) *
      Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) =
      -(Complex.I * (t : ℂ)) * windowTransform s eta t := by
  let u : ℝ → ℂ := fun x => (cosineProfile s eta x : ℂ)
  let up : ℝ → ℂ := fun x => (cosineProfileSlope s eta x : ℂ)
  let v : ℝ → ℂ := fun x => Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))
  let vp : ℝ → ℂ := fun x => (Complex.I * (t : ℂ)) * v x
  have hu : Continuous u := by dsimp [u, cosineProfile]; fun_prop
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hup : Continuous up := Complex.continuous_ofReal.comp (cosineProfileSlope_continuous s eta)
  have hvp : Continuous vp := by dsimp [vp]; fun_prop
  have hdu (x : ℝ) : HasDerivAt u (up x) x := (cosineProfile_hasDerivAt s eta x).ofReal_comp
  have hdv (x : ℝ) : HasDerivAt v (vp x) x := by
    have hh := ((((hasDerivAt_id x).const_mul t).ofReal_comp).const_mul Complex.I).cexp
    convert! hh using 1
    dsimp [v, vp]
    push_cast
    ring
  have hh := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    hu.continuousOn hv.continuousOn (fun x _ => hdu x) (fun x _ => hdv x)
    (hup.intervalIntegrable (-eta/2) (eta/2)) (hvp.intervalIntegrable (-eta/2) (eta/2))
  have ha : u (-eta / 2) = 0 := by simp only [u, (cosineProfile_boundary hs heta).1, Complex.ofReal_zero]
  have hb : u (eta / 2) = 0 := by simp only [u, (cosineProfile_boundary hs heta).2, Complex.ofReal_zero]
  rw [ha, hb, zero_mul, zero_mul, sub_self] at hh
  have hsum := intervalIntegral.integral_add (μ := volume) ((hup.mul hv).intervalIntegrable (-eta/2) (eta/2))
    ((hu.mul hvp).intervalIntegrable (-eta/2) (eta/2))
  simp only [Pi.mul_apply] at hsum
  rw [hsum] at hh
  have hi : (∫ x in -eta/2..eta/2, u x * vp x) =
      (Complex.I * (t : ℂ)) * ∫ x in -eta/2..eta/2, u x * v x := by
    simp only [vp, mul_left_comm (u _) (Complex.I * (t : ℂ)),
      intervalIntegral.integral_const_mul]
  rw [hi] at hh
  change (∫ x : ℝ, (((Set.Icc (-eta/2) (eta/2)).indicator (cosineProfileSlope s eta) x : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) = _
  rw [clipped_fourier_integral _ (by linarith) t]
  have hf : windowTransform s eta t = ∫ x in -eta/2..eta/2, u x * v x :=
    clipped_fourier_integral (cosineProfile s eta) (by linarith) t
  rw [hf]
  exact (eq_neg_of_add_eq_zero_left hh).trans (neg_mul _ _).symm
end LeanNumDetect
