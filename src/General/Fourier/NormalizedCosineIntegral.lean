import General.Fourier.SineTailProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped Topology BigOperators
namespace LeanNumDetect
noncomputable def cosineHalfMass (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi/2, Real.cos x^(2*n)
noncomputable def normalizedCosineIntegral (n : ℕ) (v : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..Real.pi/2, Real.cos (2*v*x)*Real.cos x^(2*n)) / cosineHalfMass n

theorem cosineHalfMass_pos (n : ℕ) : 0 < cosineHalfMass n := EulerSine.integral_cos_pow_pos _

theorem cosineHalfMass_succ (n : ℕ) :
    cosineHalfMass (n+1) = ((2*n+1 : ℝ)/(2*n+2))*cosineHalfMass n := by
  unfold cosineHalfMass
  rw [EulerSine.integral_cos_pow_eq, EulerSine.integral_cos_pow_eq]
  rw [show 2*(n+1) = 2*n+2 by omega, integral_sin_pow]
  simp only [Real.sin_zero, Real.sin_pi, zero_pow (by omega : 2*n+1 ≠ 0), zero_mul,
    sub_self, zero_div, zero_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem normalizedCosineIntegral_zero (n : ℕ) : normalizedCosineIntegral n 0 = 1 := by
  simp only [normalizedCosineIntegral, mul_zero, zero_mul, Real.cos_zero, one_mul]
  exact div_self (cosineHalfMass_pos n).ne'

theorem normalizedCosineIntegral_recurrence (n : ℕ) (v : ℝ) :
    normalizedCosineIntegral n v =
      (1-v^2/(n+1 : ℝ)^2)*normalizedCosineIntegral (n+1) v := by
  by_cases hv : v = 0
  · simp [hv, normalizedCosineIntegral_zero]
  have hh := EulerSine.integral_cos_mul_cos_pow_even n (Complex.ofReal_ne_zero.mpr hv)
  have hi (m : ℕ) :
      (∫ x in (0 : ℝ)..Real.pi/2, Complex.cos (2*(v : ℂ)*x)*(Real.cos x : ℂ)^(2*m)) =
      ((∫ x in (0 : ℝ)..Real.pi/2, Real.cos (2*v*x)*Real.cos x^(2*m) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _
    push_cast
    rfl
  rw [show 2*n+2 = 2*(n+1) by omega, hi (n+1), hi n] at hh
  have hr : (1-v^2/(n+1 : ℝ)^2) *
      (∫ x in (0 : ℝ)..Real.pi/2, Real.cos (2*v*x)*Real.cos x^(2*(n+1))) =
      ((2*n+1 : ℝ)/(2*n+2)) * ∫ x in (0 : ℝ)..Real.pi/2, Real.cos (2*v*x)*Real.cos x^(2*n) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_ofNat, Complex.ofReal_one] using hh
  unfold normalizedCosineIntegral
  rw [cosineHalfMass_succ]
  have hM := (cosineHalfMass_pos n).ne'
  have hn : (2*n+1 : ℝ) ≠ 0 := by positivity
  have hn' : (2*n+2 : ℝ) ≠ 0 := by positivity
  field_simp at hr ⊢
  nlinarith [hr]
theorem normalizedCosineIntegral_tail (s m : ℕ) (v : ℝ) :
    normalizedCosineIntegral s v = sineTailProduct s m v * normalizedCosineIntegral (s+m) v := by
  induction m with
  | zero => simp [sineTailProduct]
  | succ m ih =>
    rw [ih, normalizedCosineIntegral_recurrence (s+m)]
    simp only [sineTailProduct, Finset.prod_range_succ, Nat.cast_add, Nat.add_succ]
    ring

theorem normalizedCosineIntegral_tendsto (v : ℝ) :
    Tendsto (fun n : ℕ => normalizedCosineIntegral n v) atTop (𝓝 1) := by
  have hh := EulerSine.tendsto_integral_cos_pow_mul_div
    (show ContinuousOn (fun x : ℝ => (Real.cos (2*v*x) : ℂ)) (Set.Icc 0 (Real.pi/2)) by fun_prop)
  have hh' := hh.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < (2 : ℕ)))
  have he (n : ℕ) :
      ((∫ x in (0 : ℝ)..Real.pi/2, (Real.cos x : ℂ)^(2*n)*(Real.cos (2*v*x) : ℂ)) /
        ((∫ x in (0 : ℝ)..Real.pi/2, Real.cos x^(2*n) : ℝ) : ℂ)) =
      (normalizedCosineIntegral n v : ℂ) := by
    unfold normalizedCosineIntegral cosineHalfMass
    push_cast
    congr 1
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _
    push_cast
    ring
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hh'
  simpa only [Function.comp_def, id_eq, he, Complex.ofReal_re, mul_zero, Real.cos_zero] using hr

theorem normalizedCosineIntegral_lower (s : ℕ) {v : ℝ} (hv : |v| ≤ s) :
    1/(4 : ℝ)^s ≤ normalizedCosineIntegral s v := by
  have ht := (normalizedCosineIntegral_tendsto v).comp ((by simpa only [Nat.add_comm] using tendsto_add_atTop_nat s))
  have hpos : ∀ᶠ m : ℕ in atTop, 0 < normalizedCosineIntegral (s+m) v :=
    ht.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have he : ∀ᶠ m : ℕ in atTop, (s.factorial : ℝ)^2/((2*s).factorial : ℝ) *
      normalizedCosineIntegral (s+m) v ≤ normalizedCosineIntegral s v := by
    filter_upwards [hpos] with m hm
    rw [normalizedCosineIntegral_tail s m v]
    exact mul_le_mul_of_nonneg_right (sineTailProduct_lower s m hv) hm.le
  have hh := le_of_tendsto (tendsto_const_nhds.mul ht) he
  rw [mul_one] at hh
  exact (reciprocal_central_factorial_lower s).trans hh
end LeanNumDetect
