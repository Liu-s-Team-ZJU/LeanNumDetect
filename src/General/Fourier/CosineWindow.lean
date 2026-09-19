import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
namespace LeanNumDetect

/-- The actual compact cosine window in the manuscript; frequencies are angular. -/
noncomputable def cosineWindow (s : ℕ) (eta : ℝ) : ℝ → ℝ :=
  (Set.Icc (-eta / 2) (eta / 2)).indicator
    (fun x => Real.cos (Real.pi * x / eta) ^ (2 * s))

noncomputable def windowTransform (s : ℕ) (eta t : ℝ) : ℂ :=
  ∫ x : ℝ, (cosineWindow s eta x : ℂ) * Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))

noncomputable def windowMass (s : ℕ) (eta : ℝ) : ℝ :=
  ∫ x : ℝ, cosineWindow s eta x

theorem cosineWindow_nonneg (s : ℕ) (eta x : ℝ) : 0 ≤ cosineWindow s eta x := by
  unfold cosineWindow
  apply Set.indicator_nonneg
  intro y _
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) s

theorem cosineWindow_integrable (s : ℕ) (eta : ℝ) : Integrable (cosineWindow s eta) := by
  apply (integrable_indicator_iff measurableSet_Icc).2
  apply Continuous.integrableOn_Icc
  fun_prop

theorem cosineWindow_pos_inside (s : ℕ) {eta x : ℝ} (heta : 0 < eta)
    (hx : x ∈ Set.Ioo (-eta / 2) (eta / 2)) : 0 < cosineWindow s eta x := by
  unfold cosineWindow
  rw [Set.indicator_of_mem (show x ∈ Set.Icc (-eta / 2) (eta / 2) from ⟨hx.1.le, hx.2.le⟩)]
  apply pow_pos
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · apply (lt_div_iff₀ heta).2
    nlinarith [mul_lt_mul_of_pos_left hx.1 Real.pi_pos,
      mul_lt_mul_of_pos_left hx.2 Real.pi_pos]
  · apply (div_lt_iff₀ heta).2
    nlinarith [mul_lt_mul_of_pos_left hx.1 Real.pi_pos,
      mul_lt_mul_of_pos_left hx.2 Real.pi_pos]

theorem windowMass_pos (s : ℕ) {eta : ℝ} (heta : 0 < eta) : 0 < windowMass s eta := by
  rw [windowMass, integral_pos_iff_support_of_nonneg (cosineWindow_nonneg s eta)
    (cosineWindow_integrable s eta)]
  have hsub : Set.Ioo (-eta / 2) (eta / 2) ⊆ Function.support (cosineWindow s eta) :=
    fun x hx => (cosineWindow_pos_inside s heta hx).ne'
  apply lt_of_lt_of_le _ (measure_mono hsub)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (by linarith)

theorem windowTransform_zero (s : ℕ) (eta : ℝ) :
    windowTransform s eta 0 = (windowMass s eta : ℂ) := by
  simp only [windowTransform, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one, integral_complex_ofReal, windowMass]

theorem windowTransform_norm_le (s : ℕ) (eta t : ℝ) :
    ‖windowTransform s eta t‖ ≤ windowMass s eta := by
  have hn (x : ℝ) :
      ‖(cosineWindow s eta x : ℂ) * Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))‖ =
        cosineWindow s eta x := by
    rw [norm_mul]
    simp [Complex.norm_exp, Complex.mul_re, Real.norm_eq_abs,
      abs_of_nonneg (cosineWindow_nonneg s eta x)]
  exact (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae
    (Filter.Eventually.of_forall hn))

/-- The sign-changing weight, with the manuscript's exact normalization. -/
noncomputable def cosineWeight (s : ℕ) (eta T t : ℝ) : ℝ :=
  (1 - t ^ 2 / T ^ 2) * ‖windowTransform s eta t‖ ^ 2 / (windowMass s eta) ^ 2

theorem cosineWeight_inside (s : ℕ) {eta T t : ℝ} (heta : 0 < eta) (hT : 0 < T)
    (ht : |t| ≤ T) : 0 ≤ cosineWeight s eta T t ∧ cosineWeight s eta T t ≤ 1 := by
  have hm := windowMass_pos s heta
  have hsq : t ^ 2 ≤ T ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg t) hT.le).2 ht
    simpa only [sq_abs] using hh
  have hdiv : t ^ 2 / T ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hT)).2 hsq
  have hr : 0 ≤ 1 - t ^ 2 / T ^ 2 := by linarith
  have hr1 : 1 - t ^ 2 / T ^ 2 ≤ 1 := by
    linarith [div_nonneg (sq_nonneg t) (sq_nonneg T)]
  have hf := windowTransform_norm_le s eta t
  have hf2 : ‖windowTransform s eta t‖ ^ 2 ≤ windowMass s eta ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hm.le).2 hf
  unfold cosineWeight
  constructor
  · positivity
  · apply (div_le_one (sq_pos_of_pos hm)).2
    exact (mul_le_of_le_one_left (sq_nonneg _) hr1).trans hf2

theorem cosineWeight_outside (s : ℕ) {eta T t : ℝ} (hT : 0 < T) (ht : T < |t|) :
    cosineWeight s eta T t ≤ 0 := by
  have hsq : T ^ 2 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hdiv : 1 ≤ t ^ 2 / T ^ 2 := (one_le_div (sq_pos_of_pos hT)).2 hsq
  unfold cosineWeight
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)) (sq_nonneg _)

end LeanNumDetect
