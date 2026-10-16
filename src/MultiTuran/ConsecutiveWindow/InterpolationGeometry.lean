import MultiTuran.Preliminaries.Geometry
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Uniform distance of the interpolation contour from every coordinate node

The sector's radial sides are controlled by the separated unit-circle chord,
avoiding a trigonometric case split. Its logarithmic rectangle retains the
literal coefficient estimate in the note.
No distinctness assumption on coordinate values is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
open Set

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

def windowContourAngle (n : ℕ) : ℝ := Real.pi-Real.pi/(4*(n : ℝ))

def angularPhase (x : ℝ) : ℂ := Complex.exp (Complex.I*(x : ℂ))

@[simp] theorem angularPhase_norm (x : ℝ) : ‖angularPhase x‖=1 := by
  exact Complex.norm_exp_I_mul_ofReal x

theorem windowContourAngle_bounds {n : ℕ} (hn : 2 ≤ n) :
    0 < windowContourAngle n ∧ windowContourAngle n < Real.pi := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < 4*(n : ℝ) := by positivity
  have hdiv : 0 < Real.pi/(4*(n : ℝ)) := div_pos Real.pi_pos hd
  have hsmall : Real.pi/(4*(n : ℝ)) < Real.pi := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith [Real.pi_pos]
  unfold windowContourAngle
  constructor <;> linarith

private theorem torusCoordinateDistance_lower_of_between (x y δ : ℝ)
    (hlo : δ ≤ x-y) (hhi : x-y ≤ 2*Real.pi-δ) :
    δ ≤ torusCoordinateDistance x y := by
  obtain ⟨p,hp⟩ := exists_winding_eq_torusCoordinateDistance x y
  rw [hp]
  by_cases h : p ≤ 0
  · have hpR : (p : ℝ) ≤ 0 := by exact_mod_cast h
    have hm : 2*Real.pi*p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hpR
    exact (by linarith : δ ≤ x-y-2*Real.pi*p).trans (le_abs_self _)
  · have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (show (1 : ℤ) ≤ p by omega)
    have hm : 2*Real.pi ≤ 2*Real.pi*p := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpR (by positivity : 0 ≤ 2*Real.pi)
    exact (by linarith : δ ≤ -(x-y-2*Real.pi*p)).trans (neg_le_abs _)

theorem window_radial_chord_lower {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : |y| ≤ Real.pi-Real.pi/(n : ℝ)) {φ : ℝ}
    (hφ : φ=windowContourAngle n ∨ φ= -windowContourAngle n) :
    3/(2*(n : ℝ)) ≤ ‖angularPhase φ-angularPhase y‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hylo := (abs_le.mp hy).1
  have hyhi := (abs_le.mp hy).2
  have he : Real.pi/(n : ℝ)-Real.pi/(4*(n : ℝ)) = 3*Real.pi/(4*(n : ℝ)) := by
    field_simp
    <;> ring
  have hquarter : 0 ≤ Real.pi/(4*(n : ℝ)) := by positivity
  have hgap : 3*Real.pi/(4*(n : ℝ)) ≤ torusCoordinateDistance φ y := by
    rcases hφ with rfl | rfl
    · apply torusCoordinateDistance_lower_of_between
      · unfold windowContourAngle
        linarith
      · unfold windowContourAngle
        have hp : 0 ≤ Real.pi/(n : ℝ) := by positivity
        linarith
    · have h := torusCoordinateDistance_lower_of_between y (-windowContourAngle n)
        (3*Real.pi/(4*(n : ℝ))) (by unfold windowContourAngle; linarith)
        (by
          unfold windowContourAngle
          linarith)
      have hs : torusCoordinateDistance y (-windowContourAngle n) =
          torusCoordinateDistance (-windowContourAngle n) y := by
        unfold torusCoordinateDistance
        have hneg : (y+windowContourAngle n : ℝ) = -(-windowContourAngle n-y) := by ring
        rw [sub_neg_eq_add,hneg,AddCircle.coe_neg,norm_neg]
      rwa [hs] at h
  calc
    3/(2*(n : ℝ)) = (2/Real.pi)*(3*Real.pi/(4*(n : ℝ))) := by field_simp; ring
    _ ≤ (2/Real.pi)*torusCoordinateDistance φ y :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    _ ≤ _ := coordinate_chord_lower φ y

private theorem radial_distance_sq (r : ℝ) (a b : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) :
    ‖(r : ℂ)*a-b‖^2 = (r-1)^2+r*‖a-b‖^2 := by
  have ha' : a.re^2+a.im^2=1 := by
    have h := Complex.normSq_eq_norm_sq a
    rw [ha] at h
    simpa [Complex.normSq_apply,pow_two] using h
  have hb' : b.re^2+b.im^2=1 := by
    have h := Complex.normSq_eq_norm_sq b
    rw [hb] at h
    simpa [Complex.normSq_apply,pow_two] using h
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  linear_combination (r^2-r)*ha'+(1-r)*hb'

theorem window_radial_distance_lower {n : ℕ} (hn : 2 ≤ n) {y r φ : ℝ}
    (hy : |y| ≤ Real.pi-Real.pi/(n : ℝ)) (hr : 1/2 ≤ r)
    (hφ : φ=windowContourAngle n ∨ φ= -windowContourAngle n) :
    1/(n : ℝ) ≤ ‖(r : ℂ)*angularPhase φ-angularPhase y‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc := window_radial_chord_lower hn hy hφ
  have hs := radial_distance_sq r (angularPhase φ) (angularPhase y) (by simp) (by simp)
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 3/(2*(n : ℝ))) hc 2
  have hrmul := mul_le_mul_of_nonneg_right hr (sq_nonneg ‖angularPhase φ-angularPhase y‖)
  have hscale : (3/(2*(n : ℝ)))^2 = (9/4 : ℝ)*(1/(n : ℝ))^2 := by
    field_simp
    <;> ring
  rw [hscale] at hsq
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  nlinarith [sq_nonneg (r-1)]

theorem exp_eq_radial_phase (w : ℂ) :
    Complex.exp w = (Real.exp w.re : ℂ)*angularPhase w.im := by
  have hw : w=(w.re : ℂ)+Complex.I*(w.im : ℂ) := by apply Complex.ext <;> simp
  rw [hw,Complex.exp_add]
  simp [angularPhase,Complex.ofReal_exp]

/-- Every point on either radial side is at least `1/n` from every node. -/
theorem window_log_radial_distance_lower {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : |y| ≤ Real.pi-Real.pi/(n : ℝ)) {w : ℂ}
    (hre : Real.log (1/2 : ℝ) ≤ w.re)
    (him : w.im=windowContourAngle n ∨ w.im= -windowContourAngle n) :
    1/(n : ℝ) ≤ ‖Complex.exp w-angularPhase y‖ := by
  rw [exp_eq_radial_phase]
  apply window_radial_distance_lower hn hy _ him
  exact (Real.exp_log (by norm_num : (0 : ℝ) < 1/2)).symm.trans_le (Real.exp_le_exp.mpr hre)

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
