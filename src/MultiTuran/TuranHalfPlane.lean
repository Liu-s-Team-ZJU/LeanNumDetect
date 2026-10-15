import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Tactic

/-! Flattening tangent circles in the upper half plane. These elementary
geometric and harmonic identities support real-line weak Cauchy estimates. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Topology ENNReal
open Set Filter MeasureTheory Complex Metric InnerProductSpace Real

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- A radius-`R` circle tangent to the horizontal line of height `ε`,
parametrized by arc length from its bottom point. -/
def flatteningCircle (ε R t : ℝ) : ℂ :=
  ⟨R*Real.sin (t/R), ε+R*(1-Real.cos (t/R))⟩

theorem flatteningCircle_im_pos {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) (t : ℝ) :
    0 < (flatteningCircle ε R t).im := by
  dsimp [flatteningCircle]
  have hcos := Real.cos_le_one (t/R)
  have hp := mul_nonneg hR (sub_nonneg.mpr hcos)
  linarith

theorem flatteningCircle_eq_circleMap (ε R t : ℝ) :
    flatteningCircle ε R t =
      circleMap (Complex.I*((R+ε : ℝ) : ℂ)) R (t/R-Real.pi/2) := by
  unfold circleMap
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext <;>
    simp only [flatteningCircle,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      Real.sin_sub_pi_div_two,Real.cos_sub_pi_div_two] <;> ring

theorem continuous_flatteningCircle (ε R : ℝ) : Continuous (flatteningCircle ε R) := by
  have he : flatteningCircle ε R = fun t : ℝ =>
      ((R*Real.sin (t/R) : ℝ) : ℂ)+Complex.I*((ε+R*(1-Real.cos (t/R)) : ℝ) : ℂ) := by
    funext t
    apply Complex.ext <;> simp only [flatteningCircle,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
      Complex.I_im,zero_mul,mul_zero,zero_add,add_zero,one_mul,mul_one,sub_self,sub_zero]
  rw [he]
  fun_prop

/-- Tangent circles converge pointwise to their tangent horizontal line. -/
theorem tendsto_flatteningCircle (ε t : ℝ) :
    Tendsto (fun n : ℕ => flatteningCircle ε ((n : ℝ)+1) t) atTop
      (𝓝 ((t : ℂ)+Complex.I*(ε : ℂ))) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv := (tendsto_inv_atTop_nhdsGT_zero (𝕜 := ℝ)).comp hnat
  have hs : HasDerivAt (fun v : ℝ => Real.sin (t*v)) t 0 := by
    convert (Real.hasDerivAt_sin (t*0)).comp 0 ((hasDerivAt_id 0).const_mul t) using 1 <;>
      first | rfl | simp
  have hc : HasDerivAt (fun v : ℝ => Real.cos (t*v)) 0 0 := by
    convert (Real.hasDerivAt_cos (t*0)).comp 0 ((hasDerivAt_id 0).const_mul t) using 1 <;>
      first | rfl | simp
  have hsin := hs.tendsto_slope_zero_right.comp hinv
  have hcos := hc.tendsto_slope_zero_right.comp hinv
  have hs' : Tendsto (fun n : ℕ => ((n : ℝ)+1)*Real.sin (t/((n : ℝ)+1))) atTop (𝓝 t) := by
    simpa only [Function.comp_def,zero_add,inv_inv,smul_eq_mul,mul_zero,
      Real.sin_zero,sub_zero,div_eq_mul_inv] using hsin
  have hc' : Tendsto (fun n : ℕ => ε+((n : ℝ)+1)*(1-Real.cos (t/((n : ℝ)+1))))
      atTop (𝓝 ε) := by
    have h := (tendsto_const_nhds (x := ε)).sub hcos
    convert h using 1 <;>
      simp only [Function.comp_def,zero_add,inv_inv,smul_eq_mul,mul_zero,
        Real.cos_zero,sub_zero,div_eq_mul_inv] <;> ring
  have h := hs'.ofReal.add (hc'.ofReal.const_mul Complex.I)
  convert h using 1
  funext n
  apply Complex.ext <;> simp only [flatteningCircle,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,zero_mul,mul_zero,zero_add,add_zero,one_mul,mul_one,sub_self,sub_zero]

/-- A closed circle above height `ε>0` remains inside the upper half plane. -/
theorem upperHalfPlane_closedBall_subset {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    closedBall (Complex.I*((R+ε : ℝ) : ℂ)) R ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  have hn : ‖z-Complex.I*((R+ε : ℝ) : ℂ)‖ ≤ R := by
    simpa only [dist_eq_norm] using mem_closedBall.mp hz
  have hi := Complex.abs_im_le_norm (z-Complex.I*((R+ε : ℝ) : ℂ))
  have hlo := neg_le_abs ((z-Complex.I*((R+ε : ℝ) : ℂ)).im)
  simp only [Complex.sub_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add] at hi hlo
  dsimp only [Set.mem_setOf_eq]
  linarith

/-- The arc-length integral over one full tangent circle is its harmonic
centre value times its circumference. -/
theorem harmonic_integral_flatteningCircle {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u {z : ℂ | 0 < z.im})
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    (∫ t in (-Real.pi*R)..(Real.pi*R), u (flatteningCircle ε R t)) =
      2*Real.pi*R*u (Complex.I*((R+ε : ℝ) : ℂ)) := by
  let c : ℂ := Complex.I*((R+ε : ℝ) : ℂ)
  have hclosed : HarmonicOnNhd u (closedBall c |R|) := by
    rw [abs_of_pos hR]
    exact hu.mono (upperHalfPlane_closedBall_subset hε hR.le)
  have hmean := _root_.HarmonicOnNhd.circleAverage_eq hclosed
  have havg := circleAverage_eq_integral_add (f := u) (c := c) (R := R) (-3*Real.pi/2)
  rw [intervalIntegral.integral_comp_add_right (fun θ => u (circleMap c R θ)) (-3*Real.pi/2)] at havg
  have ha : (0 : ℝ)+(-3*Real.pi/2)= -3*Real.pi/2 := by ring
  have hb : 2*Real.pi+(-3*Real.pi/2)=Real.pi/2 := by ring
  rw [ha,hb,hmean] at havg
  change u c=(2*Real.pi)⁻¹*(∫ θ in (-3*Real.pi/2)..(Real.pi/2), u (circleMap c R θ)) at havg
  have hi : (∫ θ in (-3*Real.pi/2)..(Real.pi/2), u (circleMap c R θ)) =
      (2*Real.pi)*u c := by
    rw [havg]
    field_simp
  have hdiv := intervalIntegral.integral_comp_div_add
    (f := fun θ => u (circleMap c R θ)) (a := -Real.pi*R) (b := Real.pi*R) hR.ne' (-Real.pi/2)
  have hleft : (-Real.pi*R)/R+(-Real.pi/2)= -3*Real.pi/2 := by field_simp <;> ring
  have hright : (Real.pi*R)/R+(-Real.pi/2)=Real.pi/2 := by field_simp <;> ring
  rw [hleft,hright,hi] at hdiv
  calc
    _ = ∫ t in (-Real.pi*R)..(Real.pi*R), u (circleMap c R (t/R+(-Real.pi/2))) := by
      apply intervalIntegral.integral_congr
      intro t _
      change u (flatteningCircle ε R t)=u (circleMap c R (t/R+(-Real.pi/2)))
      rw [flatteningCircle_eq_circleMap]
      rw [show t/R-Real.pi/2=t/R+(-Real.pi/2) by ring]
    _ = R*((2*Real.pi)*u c) := hdiv
    _ = _ := by dsimp [c]; ring

end
end LeanNumDetect.MultiTuran
