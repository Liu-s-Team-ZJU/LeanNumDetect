import General.Fourier.PolynomialEvaluationBounds

/-! Sharper elementary polynomial evaluation estimates. A scalar projection
in the derivative direction avoids separate estimates of the real and
imaginary parts. Integrating the full triangular lower profile avoids the
constant loss of the short flat subinterval argument. -/
set_option autoImplicit false
open scoped Polynomial
open Set MeasureTheory
namespace LeanNumDetect.PolynomialEvaluationBounds
noncomputable section

 theorem complexPolynomial_unit_derivative_le_sharper {P Q : ℝ[X]} {n : ℕ}
    (hPdeg : P.natDegree ≤ n) (hQdeg : Q.natDegree ≤ n)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖complexPolynomialSignal P Q t‖ ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖deriv (complexPolynomialSignal P Q) x‖ ≤ 4 * (n : ℝ)^2 * B := by
  let w := complexPolynomialSignal P.derivative Q.derivative x
  let R := w.re • P + w.im • Q
  have hdegree : R.natDegree ≤ n :=
    Polynomial.natDegree_add_le_of_degree_le
      ((Polynomial.natDegree_smul_le _ _).trans hPdeg)
      ((Polynomial.natDegree_smul_le _ _).trans hQdeg)
  have hRbound : ∀ t ∈ Icc (0 : ℝ) 1, |R.eval t| ≤ ‖w‖ * B := by
    intro t ht
    have hnorm : ‖complexPolynomialSignal P Q t‖^2 = (P.eval t)^2 + (Q.eval t)^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply,
        complexPolynomialSignal_re, complexPolynomialSignal_im]
      ring
    have hw : ‖w‖^2 = w.re^2 + w.im^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hs : ‖complexPolynomialSignal P Q t‖^2 ≤ B^2 :=
      (sq_le_sq₀ (norm_nonneg _) hB).2 (hbound t ht)
    have he : R.eval t = w.re * P.eval t + w.im * Q.eval t := by simp [R]
    rw [he]
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ ‖w‖ * B)).1
    rw [sq_abs, mul_pow]
    nlinarith [sq_nonneg (w.re * Q.eval t - w.im * P.eval t),
      mul_nonneg (sq_nonneg ‖w‖) (sub_nonneg.mpr hs)]
  have h := realPolynomial_unit_derivative_le hdegree (by positivity) hRbound hx
  have heval : R.derivative.eval x = ‖w‖^2 := by
    simp only [R, Polynomial.derivative_add, Polynomial.derivative_smul,
      Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
    have hw : ‖w‖^2 = w.re^2 + w.im^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hw]
    simp only [w, complexPolynomialSignal_re, complexPolynomialSignal_im]
    ring
  rw [heval, abs_of_nonneg (sq_nonneg _)] at h
  rw [complexPolynomialSignal_deriv]
  change ‖w‖ ≤ _
  by_cases hw : ‖w‖ = 0
  · rw [hw]; positivity
  · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
    nlinarith

 theorem integral_triangle_square (a B D : ℝ) (hD : D ≠ 0) :
    (∫ t in a..(a + 1 / D), (B - D * B * (t - a))^2) = B^2 / (3 * D) := by
  have he : (fun t : ℝ => (B - D * B * (t - a))^2) =
      (fun t : ℝ => (B + D * B * a)^2 +
        (-2 * (B + D * B * a) * D * B) * t + (D * B)^2 * t^2) := by
    funext t; ring
  rw [he]
  have h₁ : IntervalIntegrable (fun _ : ℝ => (B + D * B * a)^2) volume a (a + 1 / D) :=
    continuous_const.intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun t : ℝ => (-2 * (B + D * B * a) * D * B) * t)
      volume a (a + 1 / D) := by
    exact (show Continuous (fun t : ℝ => (-2 * (B + D * B * a) * D * B) * t) by fun_prop).intervalIntegrable _ _
  have h₃ : IntervalIntegrable (fun t : ℝ => (D * B)^2 * t^2) volume a (a + 1 / D) := by
    exact (show Continuous (fun t : ℝ => (D * B)^2 * t^2) by fun_prop).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h₁.add h₂) h₃,
    intervalIntegral.integral_add h₁ h₂]
  rw [intervalIntegral.integral_const_mul (-2 * (B + D * B * a) * D * B) (fun t : ℝ => t),
    intervalIntegral.integral_const_mul ((D * B)^2) (fun t : ℝ => t^2)]
  simp only [intervalIntegral.integral_const, smul_eq_mul, integral_id, integral_pow]
  ring_nf
  field_simp [hD]
  <;> ring

 theorem unitInterval_peak_sq_le_energy_triangle_right {f : ℝ → ℂ}
    (hf : Continuous f) {B D x₀ : ℝ} (hB : 0 ≤ B) (hD : 2 ≤ D)
    (hx₀ : x₀ ∈ Icc (0 : ℝ) (1 / 2)) (hpeak : ‖f x₀‖ = B)
    (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖f y - f x‖ ≤ D * B * |y - x|) :
    B^2 ≤ 3 * D * (∫ t in (0 : ℝ)..1, ‖f t‖^2) := by
  have hDpos : 0 < D := by linarith
  let b := x₀ + 1 / D
  have hlen : 0 < 1 / D := by positivity
  have hhalf : 1 / D ≤ (1 / 2 : ℝ) :=
    (div_le_div_iff₀ hDpos (by norm_num)).2 (by linarith)
  have hxb : x₀ ≤ b := by dsimp [b]; linarith
  have hb : b ≤ 1 := by dsimp [b]; linarith [hx₀.2]
  have henergy : B^2 / (3 * D) ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 := by
    calc
      B^2 / (3 * D) = ∫ t in x₀..b, (B - D * B * (t - x₀))^2 :=
        (integral_triangle_square x₀ B D (ne_of_gt hDpos)).symm
      _ ≤ ∫ t in x₀..b, ‖f t‖^2 := by
        apply intervalIntegral.integral_mono_on (μ := volume) hxb
          ((show Continuous (fun u : ℝ => (B - D * B * (u - x₀))^2) by fun_prop).intervalIntegrable _ _) ((hf.norm.pow 2).intervalIntegrable _ _)
        intro t ht
        have htunit : t ∈ Icc (0 : ℝ) 1 := ⟨hx₀.1.trans ht.1, ht.2.trans hb⟩
        have hxunit : x₀ ∈ Icc (0 : ℝ) 1 := ⟨hx₀.1, by linarith [hx₀.2]⟩
        have hd := hLip x₀ hxunit t htunit
        rw [abs_of_nonneg (sub_nonneg.mpr ht.1)] at hd
        have hnorm := norm_sub_norm_le (f x₀) (f t)
        rw [hpeak, norm_sub_rev] at hnorm
        have hnonneg : 0 ≤ B - D * B * (t - x₀) := by
          have hdist : t - x₀ ≤ 1 / D := by dsimp [b] at ht; linarith [ht.2]
          have hmul := mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ D * B)
          have he : D * B * (1 / D) = B := by field_simp
          rw [he] at hmul
          linarith
        exact (sq_le_sq₀ hnonneg (norm_nonneg _)).2 (by linarith)
      _ ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 := by
        exact intervalIntegral.integral_mono_interval hx₀.1 hxb hb
          (Filter.Eventually.of_forall (fun t => by positivity))
          ((hf.norm.pow 2).intervalIntegrable _ _)
  exact (div_le_iff₀ (by positivity : 0 < 3 * D)).1 henergy |>.trans_eq (by ring)

 theorem unitInterval_peak_sq_le_energy_triangle {f : ℝ → ℂ}
    (hf : Continuous f) {B D x₀ : ℝ} (hB : 0 ≤ B) (hD : 2 ≤ D)
    (hx₀ : x₀ ∈ Icc (0 : ℝ) 1) (hpeak : ‖f x₀‖ = B)
    (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖f y - f x‖ ≤ D * B * |y - x|) :
    B^2 ≤ 3 * D * (∫ t in (0 : ℝ)..1, ‖f t‖^2) := by
  by_cases hxhalf : x₀ ≤ 1 / 2
  · exact unitInterval_peak_sq_le_energy_triangle_right hf hB hD ⟨hx₀.1, hxhalf⟩ hpeak hLip
  let g : ℝ → ℂ := fun t => f (1 - t)
  have hg : Continuous g := hf.comp (continuous_const.sub continuous_id)
  have h := unitInterval_peak_sq_le_energy_triangle_right hg hB hD
    (x₀ := 1 - x₀) ⟨by linarith [hx₀.2], by linarith⟩ (by simp [g, hpeak])
    (fun x hx y hy => by
      have hh := hLip (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
        (1 - y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
      have he : 1 - y - (1 - x) = x - y := by ring
      simpa only [g, he, abs_sub_comm] using hh)
  have he : (∫ t in (0 : ℝ)..1, ‖g t‖^2) = ∫ t in (0 : ℝ)..1, ‖f t‖^2 := by
    exact (intervalIntegral.integral_comp_sub_left
      (fun t : ℝ => ‖f t‖^2) (a := 0) (b := 1) 1).trans (by norm_num)
  rwa [he] at h

 theorem complexPolynomial_unit_row_bound_sharper {P Q : ℝ[X]} {n : ℕ}
    (hPdeg : P.natDegree ≤ n) (hQdeg : Q.natDegree ≤ n)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖complexPolynomialSignal P Q x‖^2 ≤
      12 * ((n : ℝ) + 1)^2 *
        (∫ t in (0 : ℝ)..1, ‖complexPolynomialSignal P Q t‖^2) := by
  let f := complexPolynomialSignal P Q
  have hf : Continuous f := continuous_complexPolynomialSignal P Q
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩) hf.norm.continuousOn
  let B := ‖f x₀‖
  have hB : 0 ≤ B := norm_nonneg _
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ B := hmax
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖deriv f t‖ ≤ 4 * ((n : ℝ) + 1)^2 * B := by
    have h := complexPolynomial_unit_derivative_le_sharper hPdeg hQdeg hB hbound ht
    dsimp [f]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hLip (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
      (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      ‖f v - f u‖ ≤ (4 * ((n : ℝ) + 1)^2) * B * |v - u| := by
    exact (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (hasDerivAt_complexPolynomialSignal P Q t).differentiableAt)
      hder hu hv |>.trans_eq (by rw [Real.norm_eq_abs])
  have hpeak := unitInterval_peak_sq_le_energy_triangle hf hB
    (show 2 ≤ 4 * ((n : ℝ) + 1)^2 by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    hx₀ (by rfl) hLip
  have hxbound := (sq_le_sq₀ (norm_nonneg _) hB).2 (hbound x hx)
  calc
    ‖f x‖^2 ≤ B^2 := hxbound
    _ ≤ 12 * ((n : ℝ) + 1)^2 * (∫ t in (0 : ℝ)..1, ‖f t‖^2) := by
      convert hpeak using 1
      ring

 theorem jetPolynomial_unit_row_bound_sharper {s : ℕ} (hs : 0 < s)
    (a : Fin s → ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖jetPolynomialSignal a x‖^2 ≤
      12 * (s : ℝ)^2 * (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2) := by
  rw [jetPolynomialSignal_eq_coefficientPolynomialSignal]
  have h := complexPolynomial_unit_row_bound_sharper
    (coefficientPolynomial_natDegree_le hs (fun j => (a j / (j.val.factorial : ℂ)).re))
    (coefficientPolynomial_natDegree_le hs (fun j => (a j / (j.val.factorial : ℂ)).im)) hx
  have hsR : ((s - 1 : ℕ) : ℝ) + 1 = s := by exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ s from hs))
  change ‖complexPolynomialSignal
      (realCoefficientPolynomial (fun j => a j / (j.val.factorial : ℂ)))
      (imaginaryCoefficientPolynomial (fun j => a j / (j.val.factorial : ℂ))) x‖^2 ≤
    12 * ((↑(s - 1) : ℝ) + 1)^2 * (∫ t in (0 : ℝ)..1,
      ‖complexPolynomialSignal
        (realCoefficientPolynomial (fun j => a j / (j.val.factorial : ℂ)))
        (imaginaryCoefficientPolynomial (fun j => a j / (j.val.factorial : ℂ))) t‖^2) at h
  simpa only [← coefficientPolynomialSignal_eq, hsR] using h

end
end LeanNumDetect.PolynomialEvaluationBounds
