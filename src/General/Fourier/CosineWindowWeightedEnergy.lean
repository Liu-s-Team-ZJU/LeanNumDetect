import General.Fourier.CosineWindowDerivativeParseval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace LeanNumDetect

/-- The derivative estimate 3T/4 leaves at least 7/16 of the weighted energy. -/
private theorem weighted_energy_positive_of_derivative {T H H' Q : ℝ}
    (hT : 0 < T) (hQ : 0 ≤ Q) (hderiv : H' ≤ (3 * T / 4)^2 * H) :
    (7 / 16 : ℝ) * Q * H ≤ Q / T^2 * (T^2 * H - H') := by
  have ht : 0 < T^2 := sq_pos_of_pos hT
  have h : (7 / 16 : ℝ) * (T^2 * H) ≤ T^2 * H - H' := by nlinarith
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ Q / T^2 by positivity)
  have he : Q / T^2 * ((7 / 16 : ℝ) * (T^2 * H)) = (7 / 16 : ℝ) * Q * H := by
    field_simp
  rwa [he] at hm


/-- The full signed weighted series, including the negative terms outside the sampling block. -/
theorem cosineWeight_hasSum {q s : ℕ} (hs : 1 ≤ s) {eta T : ℝ}
    (heta : 0 < eta) (hT : 0 < T) (lo hi shift : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ)
    (hxi : ∀ h, lo ≤ xi h ∧ xi h ≤ hi) (hwidth : hi - lo + eta < 2 * Real.pi) :
    HasSum (fun k : ℤ => cosineWeight s eta T ((k : ℝ) - shift) *
      ‖exponentialSum xi d ((k : ℝ) - shift)‖ ^ 2)
      ((2 * Real.pi) / (T ^ 2 * windowMass s eta ^ 2) *
        (T ^ 2 * (∫ x : ℝ, ‖translatedWindowSum s eta xi d x‖ ^ 2) -
          ∫ x : ℝ, ‖deriv (translatedWindowSum s eta xi d) x‖ ^ 2)) := by
  have hzero := translatedWindowSum_parseval s eta lo hi shift xi d hxi hwidth
  have hone := translatedWindow_derivative_parseval hs heta lo hi shift xi d hxi hwidth
  have hh := (hzero.div_const (windowMass s eta ^ 2)).sub
    (hone.div_const (T ^ 2 * windowMass s eta ^ 2))
  have hm := (windowMass_pos s heta).ne'
  have ht := hT.ne'
  convert! hh using 1
  · funext k
    unfold cosineWeight
    field_simp
  · field_simp

/-- The derivative inequality yields the exact positive local weighted-energy margin.
The derivative inequality itself is kept explicit here and proved separately. -/
theorem cosineWeight_energy_lower {q s : ℕ} (hs : 1 ≤ s) {eta T : ℝ}
    (heta : 0 < eta) (hT : 0 < T) (lo hi shift : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ)
    (hxi : ∀ h, lo ≤ xi h ∧ xi h ≤ hi) (hwidth : hi - lo + eta < 2 * Real.pi)
    (hderiv : (∫ x : ℝ, ‖deriv (translatedWindowSum s eta xi d) x‖ ^ 2) ≤
      (3 * T / 4) ^ 2 * ∫ x : ℝ, ‖translatedWindowSum s eta xi d x‖ ^ 2) :
    (7 / 16 : ℝ) * ∑' k : ℤ, (‖windowTransform s eta ((k : ℝ) - shift)‖ ^ 2 /
      windowMass s eta ^ 2) * ‖exponentialSum xi d ((k : ℝ) - shift)‖ ^ 2 ≤
      ∑' k : ℤ, cosineWeight s eta T ((k : ℝ) - shift) *
        ‖exponentialSum xi d ((k : ℝ) - shift)‖ ^ 2 := by
  have hz := (translatedWindowSum_parseval s eta lo hi shift xi d hxi hwidth).div_const
    (windowMass s eta ^ 2)
  have he : (∑' k : ℤ, (‖windowTransform s eta ((k : ℝ) - shift)‖ ^ 2 /
      windowMass s eta ^ 2) * ‖exponentialSum xi d ((k : ℝ) - shift)‖ ^ 2) =
      (2 * Real.pi) / windowMass s eta ^ 2 *
        ∫ x : ℝ, ‖translatedWindowSum s eta xi d x‖ ^ 2 := by
    convert! hz.tsum_eq using 1
    · apply tsum_congr
      intro k
      ring
    · ring
  rw [he, (cosineWeight_hasSum hs heta hT lo hi shift xi d hxi hwidth).tsum_eq]
  have hp : 0 ≤ (2 * Real.pi) / windowMass s eta ^ 2 := by positivity
  have hh := weighted_energy_positive_of_derivative hT hp hderiv
  simpa only [div_div, mul_assoc, mul_comm (windowMass s eta ^ 2) (T ^ 2)] using hh
end LeanNumDetect
