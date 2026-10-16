import MultiTuran.Turan.BlaschkeDerivative

/-! # An actual weak logarithmic derivative estimate from disk growth -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

def logarithmicDerivativeWeakConstant : ℝ := 1666+14*cauchyWeakConstant

theorem logarithmicDerivativeWeakConstant_pos : 0 < logarithmicDerivativeWeakConstant := by
  unfold logarithmicDerivativeWeakConstant
  have h := cauchyWeakConstant_pos
  positivity

/-- Genuine weak distribution control for `f'/f` on the unit real interval.
All analytic and growth hypotheses concern the actual function `f`.
At its zeros the quotient is Lean's ordinary field quotient, hence zero. -/
theorem analytic_logDerivative_weak_bound_of_growth {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 4)) {M S : ℝ} (hM : 0 < M) (hS : 0 < S)
    (hbound : ∀ z ∈ Metric.sphere (0 : ℂ) 4, ‖f z‖ ≤ M) {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hgrowth : M ≤ Real.exp S*‖f w‖) {y : ℝ} (hy : 0 < y) :
    volume {x : ℝ | x ∈ Icc (-1/2 : ℝ) (1/2) ∧ y < ‖deriv f (x : ℂ)/f (x : ℂ)‖} ≤
      ENNReal.ofReal (logarithmicDerivativeWeakConstant*S/y) := by
  have hC : 0 < cauchyWeakConstant := cauchyWeakConstant_pos
  by_cases hlarge : 1666*S ≤ y
  · obtain ⟨N,roots,hN,hmajorant⟩ := exists_logDerivative_cauchy_majorant hf hM hS hbound hw hgrowth
    have hsub : {x : ℝ | x ∈ Icc (-1/2 : ℝ) (1/2) ∧ y < ‖deriv f (x : ℂ)/f (x : ℂ)‖} ⊆
        {x : ℝ | y/2 < ‖∑ i, ((x : ℂ)-roots i)⁻¹‖} := by
      intro x hx
      have hfne : f (x : ℂ) ≠ 0 := by
        intro he
        have hbad : y < 0 := by simpa [he] using hx.2
        exact (not_lt_of_ge hy.le) hbad
      have hxnorm : ‖(x : ℂ)‖ ≤ 1/2 := by
        rw [Complex.norm_real,Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [hx.1.1],hx.1.2⟩
      have h := hmajorant (x : ℂ) hxnorm hfne
      change y/2 < ‖∑ i, ((x : ℂ)-roots i)⁻¹‖
      linarith [hx.2]
    have hweak := finiteCauchySum_weak_bound roots (div_pos hy (by norm_num : (0 : ℝ) < 2))
    simp only [Fintype.card_fin] at hweak
    have hcoef : (8*Real.pi/Real.log 2)*(N : ℝ)/(y/2) ≤
        logarithmicDerivativeWeakConstant*S/y := by
      calc
        _ = 2*cauchyWeakConstant*N/y := by unfold cauchyWeakConstant; ring
        _ ≤ 14*cauchyWeakConstant*S/y := by
          apply div_le_div_of_nonneg_right _ hy.le
          have h := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ 2*cauchyWeakConstant)
          nlinarith only [h]
        _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ hy.le
          unfold logarithmicDerivativeWeakConstant
          nlinarith only [hS.le]
    exact (measure_mono hsub).trans (hweak.trans (ENNReal.ofReal_le_ofReal hcoef))
  · have hsub : {x : ℝ | x ∈ Icc (-1/2 : ℝ) (1/2) ∧ y < ‖deriv f (x : ℂ)/f (x : ℂ)‖} ⊆
        Icc (-1/2 : ℝ) (1/2) := fun _ hx => hx.1
    have hcoef : (1 : ℝ) ≤ logarithmicDerivativeWeakConstant*S/y := by
      apply (one_le_div hy).mpr
      have hmul := mul_nonneg (show 0 ≤ 14*cauchyWeakConstant by positivity) hS.le
      unfold logarithmicDerivativeWeakConstant
      nlinarith [lt_of_not_ge hlarge]
    calc
      _ ≤ volume (Icc (-1/2 : ℝ) (1/2)) := measure_mono hsub
      _ = ENNReal.ofReal (1 : ℝ) := by rw [Real.volume_Icc]; norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal hcoef

theorem analytic_logDerivative_weak_bound_of_growth_toReal {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 4)) {M S : ℝ} (hM : 0 < M) (hS : 0 < S)
    (hbound : ∀ z ∈ Metric.sphere (0 : ℂ) 4, ‖f z‖ ≤ M) {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hgrowth : M ≤ Real.exp S*‖f w‖) {y : ℝ} (hy : 0 < y) :
    (volume {x : ℝ | x ∈ Icc (-1/2 : ℝ) (1/2) ∧
      y < ‖deriv f (x : ℂ)/f (x : ℂ)‖}).toReal ≤ logarithmicDerivativeWeakConstant*S/y := by
  have hC := logarithmicDerivativeWeakConstant_pos
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (analytic_logDerivative_weak_bound_of_growth hf hM hS hbound hw hgrowth hy)
  rwa [ENNReal.toReal_ofReal (by positivity)] at h

end
end LeanNumDetect.MultiTuran
