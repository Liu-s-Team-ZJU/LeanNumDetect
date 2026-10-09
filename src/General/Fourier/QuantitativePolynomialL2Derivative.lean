import General.Fourier.QuantitativePolynomialBounds

/-! Explicit integral derivative bounds, without a pointwise Markov loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Polynomial BigOperators
open Set MeasureTheory
namespace LeanNumDetect.PolynomialEvaluationBounds
noncomputable section

theorem realShiftedLegendre_derivative_eval_zero (r : ℕ) :
    (realShiftedLegendre r).derivative.eval 0 = -(r : ℝ)*((r : ℝ)+1) := by
  have h := realShiftedLegendre_equation r 0
  simp only [zero_mul, sub_zero, realShiftedLegendre_eval_zero,
    mul_one, zero_add] at h
  linarith

theorem realShiftedLegendre_derivative_eval_one (r : ℕ) :
    (realShiftedLegendre r).derivative.eval 1 =
      (r : ℝ)*((r : ℝ)+1)*(-1 : ℝ)^r := by
  have h := realShiftedLegendre_equation r 1
  rw [realShiftedLegendre_eval_one] at h
  norm_num at h
  linarith

/-- The unit-interval derivative norm of the shifted Legendre polynomial. -/
theorem realShiftedLegendre_derivative_sq_integral (r : ℕ) :
    (∫ t in (0 : ℝ)..1, ((realShiftedLegendre r).derivative.eval t)^2) =
      2*(r : ℝ)*((r : ℝ)+1) := by
  let P := realShiftedLegendre r
  have hPne : P ≠ 0 := by
    intro h
    have hz := realShiftedLegendre_eval_zero r
    simp [P, h] at hz
  have hlow := realShiftedLegendre_orthogonal_of_degree_lt r P.derivative.derivative
    ((Polynomial.degree_derivative_le (p := P.derivative)).trans_lt
      (by simpa only [P, Polynomial.degree_eq_natDegree hPne,
        realShiftedLegendre_natDegree] using Polynomial.degree_derivative_lt hPne))
  change (∫ t in (0 : ℝ)..1, P.eval t*P.derivative.derivative.eval t)=0 at hlow
  have h := polynomial_unit_integral_derivative (P*P.derivative)
  simp only [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul] at h
  have hI₁ : IntervalIntegrable (fun t : ℝ => P.derivative.eval t*P.derivative.eval t)
      volume 0 1 := (P.derivative.continuous.mul P.derivative.continuous).intervalIntegrable _ _
  have hI₂ : IntervalIntegrable (fun t : ℝ => P.eval t*P.derivative.derivative.eval t)
      volume 0 1 := (P.continuous.mul P.derivative.derivative.continuous).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hI₁ hI₂,
    hlow, add_zero] at h
  have hsign : ((-1 : ℝ)^r)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm r 2, pow_mul]
    simp
  calc
    _ = P.eval 1*P.derivative.eval 1-P.eval 0*P.derivative.eval 0 := by
      simpa only [P, pow_two] using h
    _ = _ := by
      simp only [P, realShiftedLegendre_eval_one,
        realShiftedLegendre_eval_zero, realShiftedLegendre_derivative_eval_zero,
        realShiftedLegendre_derivative_eval_one]
      calc
        _ = ((-1 : ℝ)^r)^2*((r : ℝ)*((r : ℝ)+1)) +
            (r : ℝ)*((r : ℝ)+1) := by ring
        _ = _ := by rw [hsign]; ring

theorem sum_legendre_derivative_energy (s : ℕ) :
    (∑ r : Fin s, (2*(r.val : ℝ)+1)*(2*(r.val : ℝ)*((r.val : ℝ)+1))) =
      (s : ℝ)^2*((s : ℝ)^2-1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem complexLegendreSignal_deriv {s : ℕ} (a : Fin s → ℂ) (t : ℝ) :
    deriv (complexLegendreSignal a) t =
      ∑ r : Fin s, a r*Complex.ofReal ((realShiftedLegendre r.val).derivative.eval t) := by
  have h := (HasDerivAt.sum (u := Finset.univ) (fun r _ =>
    ((realShiftedLegendre r.val).hasDerivAt t).ofReal_comp.const_mul (a r))).deriv
  have he : (∑ r : Fin s, fun x : ℝ => a r*Complex.ofReal ((realShiftedLegendre r.val).eval x)) =
      complexLegendreSignal a := by
    funext x
    simp [complexLegendreSignal]
  rw [he] at h
  exact h

theorem complexLegendreSignal_derivative_energy_le (s : ℕ) (a : Fin s → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖deriv (complexLegendreSignal a) t‖^2) ≤
      (s : ℝ)^2*((s : ℝ)^2-1)*
        (∫ t in (0 : ℝ)..1, ‖complexLegendreSignal a t‖^2) := by
  let E := ∫ t in (0 : ℝ)..1, ‖complexLegendreSignal a t‖^2
  have hE : E=∑ r : Fin s, ‖a r‖^2/(2*(r.val : ℝ)+1) :=
    complexLegendreSignal_energy a
  have hpoint (t : ℝ) : ‖deriv (complexLegendreSignal a) t‖^2 ≤
      E*(∑ r : Fin s, (2*(r.val : ℝ)+1)*
        ((realShiftedLegendre r.val).derivative.eval t)^2) := by
    rw [complexLegendreSignal_deriv]
    simpa only [← hE] using complex_weighted_sum_norm_sq_le a
      (fun r => (realShiftedLegendre r.val).derivative.eval t)
      (fun r => 2*(r.val : ℝ)+1) (fun r => by positivity)
  have hcont : Continuous (fun t => deriv (complexLegendreSignal a) t) := by
    simp_rw [complexLegendreSignal_deriv]
    fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ)≤1)
    ((hcont.norm.pow 2).intervalIntegrable _ _)
    (show IntervalIntegrable (fun t : ℝ => E*(∑ r : Fin s,
      (2*(r.val : ℝ)+1)*((realShiftedLegendre r.val).derivative.eval t)^2)) volume 0 1 from
      (by fun_prop : Continuous (fun t : ℝ => E*(∑ r : Fin s,
        (2*(r.val : ℝ)+1)*((realShiftedLegendre r.val).derivative.eval t)^2))).intervalIntegrable _ _)
    (fun t _ => hpoint t)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    (fun r _ => (show Continuous (fun t : ℝ =>
      (2*(r.val : ℝ)+1)*((realShiftedLegendre r.val).derivative.eval t)^2) from
      continuous_const.mul ((realShiftedLegendre r.val).derivative.continuous.pow 2)).intervalIntegrable _ _)] at h
  simp_rw [intervalIntegral.integral_const_mul, realShiftedLegendre_derivative_sq_integral] at h
  rw [sum_legendre_derivative_energy] at h
  simpa only [E, mul_comm, Pi.pow_apply] using h

theorem coefficientPolynomial_derivative_energy_le_explicit {s : ℕ} (hs : 0<s)
    (a : Fin s → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖deriv (coefficientPolynomialSignal a) t‖^2) ≤
      (s : ℝ)^2*((s : ℝ)^2-1)*
        (∫ t in (0 : ℝ)..1, ‖coefficientPolynomialSignal a t‖^2) := by
  obtain ⟨c, hc, _⟩ := coefficientPolynomial_legendre_expansion hs a
  have he : coefficientPolynomialSignal a=complexLegendreSignal c := funext hc
  rw [he]
  exact complexLegendreSignal_derivative_energy_le s c

theorem jetPolynomial_derivative_energy_le_explicit {s : ℕ} (hs : 0<s)
    (a : Fin s → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖deriv (jetPolynomialSignal a) t‖^2) ≤
      (s : ℝ)^2*((s : ℝ)^2-1)*
        (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2) := by
  have he := jetPolynomialSignal_eq_coefficientPolynomialSignal a
  rw [he]
  exact coefficientPolynomial_derivative_energy_le_explicit hs _

theorem coefficientPolynomial_derivative_energy_sqrt_le_explicit {s : ℕ}
    (hs : 0<s) (a : Fin s → ℂ) :
    Real.sqrt (∫ t in (0 : ℝ)..1, ‖deriv (coefficientPolynomialSignal a) t‖^2) ≤
      (s : ℝ)*Real.sqrt ((s : ℝ)^2-1)*
        Real.sqrt (∫ t in (0 : ℝ)..1, ‖coefficientPolynomialSignal a t‖^2) := by
  have hsR : (1 : ℝ)≤s := by exact_mod_cast hs
  have hdegree : 0≤(s : ℝ)^2-1 := by nlinarith
  have h := Real.sqrt_le_sqrt (coefficientPolynomial_derivative_energy_le_explicit hs a)
  rw [Real.sqrt_mul (mul_nonneg (sq_nonneg _) hdegree),
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg s)] at h
  exact h

theorem jetPolynomial_derivative_energy_sqrt_le_explicit {s : ℕ}
    (hs : 0<s) (a : Fin s → ℂ) :
    Real.sqrt (∫ t in (0 : ℝ)..1, ‖deriv (jetPolynomialSignal a) t‖^2) ≤
      (s : ℝ)*Real.sqrt ((s : ℝ)^2-1)*
        Real.sqrt (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2) := by
  rw [jetPolynomialSignal_eq_coefficientPolynomialSignal]
  exact coefficientPolynomial_derivative_energy_sqrt_le_explicit hs _

end
end LeanNumDetect.PolynomialEvaluationBounds
