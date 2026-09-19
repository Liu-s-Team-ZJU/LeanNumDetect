import General.Fourier.CosineWindowFourierLower
import General.Fourier.CosineWindowWeightedEnergy

/-! Exact mass, squared energy, derivative energy, and shifted discrete weight sum
for the compact cosine-squared window, with angular-frequency normalization. -/

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace LeanNumDetect

/-- The mass of the compact cosine-squared window. -/
theorem windowMass_one {eta : ℝ} (heta : 0 < eta) :
    windowMass 1 eta = eta / 2 := by
  rw [windowMass_eq_factorial 1 heta]
  norm_num [Nat.factorial]
  ring

/-- The mass of the compact fourth-power cosine window. -/
theorem windowMass_two {eta : ℝ} (heta : 0 < eta) :
    windowMass 2 eta = 3 * eta / 8 := by
  rw [windowMass_eq_factorial 2 heta]
  norm_num [Nat.factorial]
  ring

/-- Squaring the cosine-squared window gives the fourth-power window. -/
theorem cosineWindow_one_norm_sq (eta x : ℝ) :
    ‖(cosineWindow 1 eta x : ℂ)‖ ^ 2 = cosineWindow 2 eta x := by
  classical
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  by_cases hx : x ∈ Set.Icc (-eta / 2) (eta / 2)
  · simp only [cosineWindow, Set.indicator_of_mem hx]
    norm_num
    ring
  · simp [cosineWindow, Set.indicator_of_notMem hx]

/-- The squared slope is a difference of two compact cosine windows. -/
theorem cosineWindowSlope_one_norm_sq (eta x : ℝ) :
    ‖(cosineWindowSlope 1 eta x : ℂ)‖ ^ 2 =
      (4 * Real.pi ^ 2 / eta ^ 2) * (cosineWindow 1 eta x - cosineWindow 2 eta x) := by
  classical
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  by_cases hx : x ∈ Set.Icc (-eta / 2) (eta / 2)
  · simp only [cosineWindowSlope, cosineWindow, Set.indicator_of_mem hx,
      cosineProfileSlope]
    norm_num
    have hs := Real.sin_sq_add_cos_sq (Real.pi * x / eta)
    calc
      _ = (4 * Real.pi ^ 2 / eta ^ 2) *
          (Real.sin (Real.pi * x / eta) ^ 2 * Real.cos (Real.pi * x / eta) ^ 2) := by ring
      _ = _ := by rw [show Real.sin (Real.pi * x / eta) ^ 2 =
          1 - Real.cos (Real.pi * x / eta) ^ 2 by linarith]; ring
  · simp [cosineWindowSlope, cosineWindow, Set.indicator_of_notMem hx]

/-- The squared window is integrable. -/
theorem cosineWindow_one_norm_sq_integrable (eta : ℝ) :
    Integrable (fun x : ℝ => ‖(cosineWindow 1 eta x : ℂ)‖ ^ 2) := by
  simpa only [cosineWindow_one_norm_sq] using cosineWindow_integrable 2 eta

/-- The squared slope is integrable. -/
theorem cosineWindowSlope_one_norm_sq_integrable (eta : ℝ) :
    Integrable (fun x : ℝ => ‖(cosineWindowSlope 1 eta x : ℂ)‖ ^ 2) := by
  simpa only [cosineWindowSlope_one_norm_sq, Pi.sub_apply] using
    ((cosineWindow_integrable 1 eta).sub (cosineWindow_integrable 2 eta)).const_mul
      (4 * Real.pi ^ 2 / eta ^ 2)

/-- Exact squared energy of the compact cosine-squared window. -/
theorem cosineWindow_one_energy {eta : ℝ} (heta : 0 < eta) :
    (∫ x : ℝ, ‖(cosineWindow 1 eta x : ℂ)‖ ^ 2) = 3 * eta / 8 := by
  simp only [cosineWindow_one_norm_sq]
  exact windowMass_two heta

/-- Exact squared energy of the slope of the compact cosine-squared window. -/
theorem cosineWindowSlope_one_energy {eta : ℝ} (heta : 0 < eta) :
    (∫ x : ℝ, ‖(cosineWindowSlope 1 eta x : ℂ)‖ ^ 2) =
      Real.pi ^ 2 / (2 * eta) := by
  simp only [cosineWindowSlope_one_norm_sq]
  rw [integral_const_mul, integral_sub (cosineWindow_integrable 1 eta)
    (cosineWindow_integrable 2 eta)]
  change (4 * Real.pi ^ 2 / eta ^ 2) * (windowMass 1 eta - windowMass 2 eta) = _
  rw [windowMass_one heta, windowMass_two heta]
  field_simp
  ring

/-- Exact sum of the normalized signed cosine-squared weight on any shifted
integer grid. The strict width condition prevents overlap of periodic copies. -/
theorem cosineWeight_one_hasSum {eta T : ℝ} (heta : 0 < eta)
    (hwidth : eta < 2 * Real.pi) (hT : 0 < T) (shift : ℝ) :
    HasSum (fun k : ℤ => cosineWeight 1 eta T ((k : ℝ) - shift))
      (3 * Real.pi / eta - 4 * Real.pi ^ 3 / (T ^ 2 * eta ^ 3)) := by
  let xi : Fin 1 → ℝ := fun _ => 0
  let d : Fin 1 → ℂ := fun _ => 1
  have hxi : ∀ h, (0 : ℝ) ≤ xi h ∧ xi h ≤ 0 := by simp [xi]
  have hw : (0 : ℝ) - 0 + eta < 2 * Real.pi := by simpa using hwidth
  have hsum := cosineWeight_hasSum (q := 1) (s := 1) (by omega) heta hT
    0 0 shift xi d hxi hw
  have hexp (t : ℝ) : exponentialSum xi d t = 1 := by
    simp [exponentialSum, xi, d]
  have hfun (x : ℝ) : translatedWindowSum 1 eta xi d x =
      (cosineWindow 1 eta x : ℂ) := by
    simp [translatedWindowSum, xi, d]
  have hderiv : (∫ x : ℝ, ‖deriv (translatedWindowSum 1 eta xi d) x‖ ^ 2) =
      Real.pi ^ 2 / (2 * eta) := by
    calc
      _ = ∫ x : ℝ, ‖(cosineWindowSlope 1 eta x : ℂ)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [translatedWindow_deriv_ae 1 eta xi d] with x hx
        simp [hx, translatedWindowSlope, xi, d]
      _ = _ := cosineWindowSlope_one_energy heta
  simp only [hexp, norm_one, one_pow, mul_one, hfun,
    cosineWindow_one_energy heta, hderiv, windowMass_one heta] at hsum
  convert hsum using 1
  field_simp
  ring

end LeanNumDetect
