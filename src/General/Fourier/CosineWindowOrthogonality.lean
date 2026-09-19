import General.Fourier.DisjointParseval
import General.Fourier.CosineWindowDerivativeParseval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace LeanNumDetect

/-- Exact weighted orthogonality of two separated translates, including both tails. -/
theorem cosineWeight_realCross_hasSum {s : ℕ} (hs : 1 ≤ s) {eta T gap : ℝ}
    (heta : 0 < eta) (hT : 0 < T) (hgap : eta < gap)
    (hwidth : gap + eta < 2*Real.pi) (c₁ c₂ : ℂ) (shift : ℝ) :
    HasSum (fun k : ℤ => cosineWeight s eta T ((k : ℝ)-shift) *
      (2 * (star c₁*c₂*Complex.exp (Complex.I * ((((k : ℝ)-shift)*gap : ℝ) : ℂ))).re)) 0 := by
  have hb (x : ℝ) : ‖(cosineWindow s eta x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cosineWindow_nonneg s eta x)]
      using cosineWindow_le_one s eta x
  have hsb (x : ℝ) : ‖(cosineWindowSlope s eta x : ℂ)‖ ≤ |(2*s : ℝ)*(Real.pi/eta)| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using cosineWindowSlope_abs_le s eta x
  have hz := compact_kernel_realCross (p := fun x => (cosineWindow s eta x : ℂ)) (cosineWindow_integrable s eta).ofReal 1 hb
    (fun x hx => by simp [cosineWindow, Set.indicator_of_notMem hx]) hgap hwidth c₁ c₂ shift
  have ho := compact_kernel_realCross (p := fun x => (cosineWindowSlope s eta x : ℂ)) (cosineWindowSlope_integrable s eta).ofReal
    |(2*s : ℝ)*(Real.pi/eta)| hsb
    (fun x hx => by simp [cosineWindowSlope, Set.indicator_of_notMem hx]) hgap hwidth c₁ c₂ shift
  have hst (t : ℝ) : angularTransform (fun x => (cosineWindowSlope s eta x : ℂ)) t =
      -(Complex.I * (t : ℂ)) * windowTransform s eta t := cosineWindowSlope_transform hs heta t
  have hnormt (t : ℝ) : ‖angularTransform (fun x => (cosineWindowSlope s eta x : ℂ)) t‖^2 =
      t^2 * ‖windowTransform s eta t‖^2 := by
    rw [hst]
    simp [mul_pow, sq_abs]
  simp_rw [hnormt] at ho
  change HasSum (fun k : ℤ => ‖windowTransform s eta ((k : ℝ)-shift)‖^2 *
    (2 * (star c₁*c₂*Complex.exp (Complex.I * ((((k : ℝ)-shift)*gap : ℝ) : ℂ))).re)) 0 at hz
  have hh := (hz.div_const (windowMass s eta ^ 2)).sub
    (ho.div_const (T^2 * windowMass s eta^2))
  have hm := (windowMass_pos s heta).ne'
  have htn := hT.ne'
  convert! hh using 1
  · funext k
    unfold cosineWeight
    field_simp
  · simp
/-- Choose the representative of a torus separation inside one period. -/
theorem separated_torus_representative {eta gap : ℝ} (_heta : 0 < eta)
    (hsep : ∀ p : ℤ, eta < |gap - 2*Real.pi*p|) :
    ∃ p : ℤ, eta < gap-2*Real.pi*p ∧ gap-2*Real.pi*p+eta < 2*Real.pi := by
  let p : ℤ := ⌊gap / (2*Real.pi)⌋
  have hp : (p : ℝ) ≤ gap / (2*Real.pi) := Int.floor_le _
  have hp' : gap / (2*Real.pi) < (p : ℝ)+1 := Int.lt_floor_add_one _
  have hpp : 0 < 2*Real.pi := by positivity
  have hlo := (le_div_iff₀ hpp).mp hp
  have hhi := (div_lt_iff₀ hpp).mp hp'
  have hs := hsep p
  rw [abs_of_nonneg (by nlinarith : 0 ≤ gap-2*Real.pi*p)] at hs
  have ht := hsep (p+1)
  push_cast at ht
  rw [abs_of_neg (by nlinarith : gap-2*Real.pi*((p : ℝ)+1) < 0)] at ht
  exact ⟨p, hs, by linarith⟩

/-- Wrapped separations have the same vanishing real cross series. -/
theorem cosineWeight_realCross_torus_hasSum {s : ℕ} (hs : 1 ≤ s) {eta T gap : ℝ}
    (heta : 0 < eta) (hT : 0 < T)
    (hsep : ∀ p : ℤ, eta < |gap - 2*Real.pi*p|)
    (c₁ c₂ : ℂ) (shift : ℝ) :
    HasSum (fun k : ℤ => cosineWeight s eta T ((k : ℝ)-shift) *
      (2 * (star c₁*c₂*Complex.exp (Complex.I * ((((k : ℝ)-shift)*gap : ℝ) : ℂ))).re)) 0 := by
  obtain ⟨p,hlo,hhi⟩ := separated_torus_representative heta hsep
  let d := gap - 2*Real.pi*p
  let z := Complex.exp (-(Complex.I * ((shift * (2*Real.pi*p) : ℝ) : ℂ)))
  have hh := cosineWeight_realCross_hasSum hs heta hT hlo hhi c₁ (c₂*z) shift
  have he (k : ℤ) : Complex.exp (Complex.I * ((((k : ℝ)-shift)*gap : ℝ) : ℂ)) =
      z * Complex.exp (Complex.I * ((((k : ℝ)-shift)*d : ℝ) : ℂ)) := by
    have ha : Complex.I * ((((k : ℝ)-shift)*gap : ℝ) : ℂ) =
        -(Complex.I * ((shift*(2*Real.pi*p) : ℝ) : ℂ)) +
        Complex.I * ((((k : ℝ)-shift)*d : ℝ) : ℂ) +
        ((k*p : ℤ) : ℂ) * (2*Real.pi*Complex.I) := by
      dsimp [d]
      push_cast
      ring
    rw [ha, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  convert! hh using 1
  funext k
  rw [he]
  dsimp only [d]
  simp only [mul_assoc]
/-- The manuscript's complex cross-kernel identity on an arbitrary shifted grid. -/
theorem cosineWeight_cross_torus_hasSum {s : ℕ} (hs : 1 ≤ s) {eta T gap : ℝ}
    (heta : 0 < eta) (hT : 0 < T)
    (hsep : ∀ p : ℤ, eta < |gap - 2*Real.pi*p|) (shift : ℝ) :
    HasSum (fun k : ℤ => (cosineWeight s eta T ((k : ℝ)-shift) : ℂ) *
      Complex.exp (Complex.I * ((((k : ℝ)-shift)*gap : ℝ) : ℂ))) 0 := by
  have hr := (cosineWeight_realCross_torus_hasSum hs heta hT hsep 1 1 shift).div_const 2
  have hi := (cosineWeight_realCross_torus_hasSum hs heta hT hsep 1 Complex.I shift).div_const (-2)
  apply (Complex.hasSum_iff _ _).2
  constructor
  · convert! hr using 1
    · funext k
      simp only [star_one, one_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      ring
    · simp
  · convert! hi using 1
    · funext k
      simp only [star_one, one_mul, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, Complex.I_re, Complex.I_im,
        zero_sub]
      ring
    · simp
end LeanNumDetect
