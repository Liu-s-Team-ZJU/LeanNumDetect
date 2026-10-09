import General.Fourier.PolynomialEvaluationBounds
import Mathlib.Tactic

/-!
# Uniform perturbations of Taylor-jet polynomial spaces

A sufficiently small uniform perturbation, measured relative to the coefficient
norm, preserves the dimension-squared point-evaluation estimate. Its required
smallness may depend on the dimension through the polynomial Gram lower bound.
-/

set_option autoImplicit false
open Set MeasureTheory

namespace LeanNumDetect.PolynomialEvaluationBounds

noncomputable section

theorem norm_sq_le_perturbation (u v : ℂ) :
    ‖u‖^2 ≤ (5 / 4 : ℝ) * ‖v‖^2 + 5 * ‖u - v‖^2 := by
  have htriangle : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by
    simpa [add_comm] using norm_add_le v (u - v)
  have hsq := (sq_le_sq₀ (norm_nonneg u) (by positivity :
    0 ≤ ‖v‖ + ‖u - v‖)).2 htriangle
  nlinarith [sq_nonneg (‖v‖ / 2 - 2 * ‖u - v‖)]

theorem jetPolynomial_stable_energy_and_row_bound {s : ℕ} (hs : 0 < s)
    {c : ℝ} (_hc : 0 < c)
    (hcoeff : ∀ a : Fin s → ℂ,
      c * ‖a‖^2 ≤ ∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2)
    {ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε^2 ≤ c / 25)
    (a : Fin s → ℂ) {f : ℝ → ℂ} (hf : Continuous f)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖f t - jetPolynomialSignal a t‖ ≤ ε * ‖a‖) :
    (c / 2) * ‖a‖^2 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 ∧
      ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖^2 ≤
        128 * (s : ℝ)^2 * (∫ t in (0 : ℝ)..1, ‖f t‖^2) := by
  let Ep := ∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2
  let Ef := ∫ t in (0 : ℝ)..1, ‖f t‖^2
  have hEp : 0 ≤ Ep := by
    apply intervalIntegral.integral_nonneg_of_forall
    · norm_num
    · intro t
      positivity
  have hEf : 0 ≤ Ef := by
    apply intervalIntegral.integral_nonneg_of_forall
    · norm_num
    · intro t
      positivity
  have herror : 5 * ε^2 * ‖a‖^2 ≤ Ep / 5 := by
    have h := mul_le_mul_of_nonneg_right hεsmall (sq_nonneg ‖a‖)
    have hp := hcoeff a
    change c * ‖a‖^2 ≤ Ep at hp
    nlinarith
  have hfenergy : IntervalIntegrable (fun t => (5 / 4 : ℝ) * ‖f t‖^2)
      volume 0 1 := ((hf.norm.pow 2).const_mul (5 / 4)).intervalIntegrable 0 1
  have hconstant : IntervalIntegrable (fun _ : ℝ => 5 * ε^2 * ‖a‖^2)
      volume 0 1 := continuous_const.intervalIntegrable 0 1
  have hbase : Ep ≤ (5 / 4 : ℝ) * Ef + 5 * ε^2 * ‖a‖^2 := by
    calc
      Ep ≤ ∫ t in (0 : ℝ)..1,
          (5 / 4 : ℝ) * ‖f t‖^2 + 5 * ε^2 * ‖a‖^2 := by
        apply intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
          (((continuous_jetPolynomialSignal a).norm.pow 2).intervalIntegrable 0 1)
          (hfenergy.add hconstant)
        intro t ht
        change ‖jetPolynomialSignal a t‖^2 ≤
          (5 / 4 : ℝ) * ‖f t‖^2 + 5 * ε^2 * ‖a‖^2
        have h := norm_sq_le_perturbation (jetPolynomialSignal a t) (f t)
        have hclose' := hclose t ht
        have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity :
          0 ≤ ε * ‖a‖)).2 hclose'
        rw [norm_sub_rev] at h
        rw [mul_pow] at hsq
        nlinarith
      _ = (5 / 4 : ℝ) * Ef + 5 * ε^2 * ‖a‖^2 := by
        rw [intervalIntegral.integral_add hfenergy hconstant]
        simp [Ef, intervalIntegral.integral_const_mul]
  have htransfer : Ep ≤ (25 / 16 : ℝ) * Ef := by nlinarith
  constructor
  · have h := hcoeff a
    change c * ‖a‖^2 ≤ Ep at h
    change (c / 2) * ‖a‖^2 ≤ Ef
    nlinarith
  · intro x hx
    have hpoint := jetPolynomial_unit_row_bound hs a hx
    change ‖jetPolynomialSignal a x‖^2 ≤ 64 * (s : ℝ)^2 * Ep at hpoint
    have hperturb := norm_sq_le_perturbation (f x) (jetPolynomialSignal a x)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity :
      0 ≤ ε * ‖a‖)).2 (hclose x hx)
    rw [mul_pow] at hsq
    have hbound : ‖f x‖^2 ≤ (80 * (s : ℝ)^2 + 1 / 5) * Ep := by
      nlinarith
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hmul := mul_le_mul_of_nonneg_left htransfer
      (by positivity : 0 ≤ 80 * (s : ℝ)^2 + 1 / 5)
    change ‖f x‖^2 ≤ 128 * (s : ℝ)^2 * Ef
    nlinarith [sq_nonneg ((s : ℝ) - 1),
      mul_nonneg (show 0 ≤ (s : ℝ)^2 - 1 by nlinarith) hEf]

theorem jetPolynomial_stability_constants (s : ℕ) (hs : 0 < s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ (a : Fin s → ℂ) (f : ℝ → ℂ),
      Continuous f →
      (∀ t ∈ Icc (0 : ℝ) 1,
        ‖f t - jetPolynomialSignal a t‖ ≤ ε * ‖a‖) →
      c * ‖a‖^2 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 ∧
        ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖^2 ≤
          128 * (s : ℝ)^2 * (∫ t in (0 : ℝ)..1, ‖f t‖^2) := by
  obtain ⟨c, hc, hcoeff⟩ := jetPolynomial_energy_lower s hs
  refine ⟨Real.sqrt (c / 25), c / 2, Real.sqrt_pos.2 (by positivity),
    by positivity, fun a f hf hclose => ?_⟩
  apply jetPolynomial_stable_energy_and_row_bound hs hc hcoeff
    (Real.sqrt_nonneg _) (by rw [Real.sq_sqrt (by positivity)]) a hf hclose

theorem jetPolynomial_stable_energy_and_row_bound_of_row_bound {s : ℕ} (hs : 0 < s) {K : ℝ} (hK : 1 ≤ K)
    (hrow : ∀ (a : Fin s → ℂ) (x : ℝ), x ∈ Icc (0 : ℝ) 1 →
      ‖jetPolynomialSignal a x‖^2 ≤ K * (s : ℝ)^2 *
        (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2))
    {c : ℝ} (_hc : 0 < c)
    (hcoeff : ∀ a : Fin s → ℂ,
      c * ‖a‖^2 ≤ ∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2)
    {ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε^2 ≤ c / 100)
    (a : Fin s → ℂ) {f : ℝ → ℂ} (hf : Continuous f)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖f t - jetPolynomialSignal a t‖ ≤ ε * ‖a‖) :
    (c / 2) * ‖a‖^2 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 ∧
      ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖^2 ≤
        (7 / 4 : ℝ) * K * (s : ℝ)^2 * (∫ t in (0 : ℝ)..1, ‖f t‖^2) := by
  let Ep := ∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2
  let Ef := ∫ t in (0 : ℝ)..1, ‖f t‖^2
  have hEp : 0 ≤ Ep := by
    apply intervalIntegral.integral_nonneg_of_forall
    · norm_num
    · intro t
      positivity
  have hEf : 0 ≤ Ef := by
    apply intervalIntegral.integral_nonneg_of_forall
    · norm_num
    · intro t
      positivity
  have herror : 5 * ε^2 * ‖a‖^2 ≤ Ep / 20 := by
    have h := mul_le_mul_of_nonneg_right hεsmall (sq_nonneg ‖a‖)
    have hp := hcoeff a
    change c * ‖a‖^2 ≤ Ep at hp
    nlinarith
  have hfenergy : IntervalIntegrable (fun t => (5 / 4 : ℝ) * ‖f t‖^2)
      volume 0 1 := ((hf.norm.pow 2).const_mul (5 / 4)).intervalIntegrable 0 1
  have hconstant : IntervalIntegrable (fun _ : ℝ => 5 * ε^2 * ‖a‖^2)
      volume 0 1 := continuous_const.intervalIntegrable 0 1
  have hbase : Ep ≤ (5 / 4 : ℝ) * Ef + 5 * ε^2 * ‖a‖^2 := by
    calc
      Ep ≤ ∫ t in (0 : ℝ)..1,
          (5 / 4 : ℝ) * ‖f t‖^2 + 5 * ε^2 * ‖a‖^2 := by
        apply intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
          (((continuous_jetPolynomialSignal a).norm.pow 2).intervalIntegrable 0 1)
          (hfenergy.add hconstant)
        intro t ht
        change ‖jetPolynomialSignal a t‖^2 ≤
          (5 / 4 : ℝ) * ‖f t‖^2 + 5 * ε^2 * ‖a‖^2
        have h := norm_sq_le_perturbation (jetPolynomialSignal a t) (f t)
        have hclose' := hclose t ht
        have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity :
          0 ≤ ε * ‖a‖)).2 hclose'
        rw [norm_sub_rev] at h
        rw [mul_pow] at hsq
        nlinarith
      _ = (5 / 4 : ℝ) * Ef + 5 * ε^2 * ‖a‖^2 := by
        rw [intervalIntegral.integral_add hfenergy hconstant]
        simp [Ef, intervalIntegral.integral_const_mul]
  have htransfer : Ep ≤ (25 / 19 : ℝ) * Ef := by nlinarith
  constructor
  · have h := hcoeff a
    change c * ‖a‖^2 ≤ Ep at h
    change (c / 2) * ‖a‖^2 ≤ Ef
    nlinarith
  · intro x hx
    have hpoint := hrow a x hx
    change ‖jetPolynomialSignal a x‖^2 ≤ K * (s : ℝ)^2 * Ep at hpoint
    have hperturb := norm_sq_le_perturbation (f x) (jetPolynomialSignal a x)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity :
      0 ≤ ε * ‖a‖)).2 (hclose x hx)
    rw [mul_pow] at hsq
    have hbound : ‖f x‖^2 ≤ ((5 / 4 : ℝ) * K * (s : ℝ)^2 + 1 / 20) * Ep := by
      nlinarith
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hmul := mul_le_mul_of_nonneg_left htransfer
      (by positivity : 0 ≤ (5 / 4 : ℝ) * K * (s : ℝ)^2 + 1 / 20)
    change ‖f x‖^2 ≤ (7 / 4 : ℝ) * K * (s : ℝ)^2 * Ef
    have hKs : 1 ≤ K * (s : ℝ)^2 := by
      nlinarith [sq_nonneg ((s : ℝ) - 1), mul_nonneg (show 0 ≤ K - 1 by linarith) (sq_nonneg (s : ℝ))]
    nlinarith [mul_nonneg (show 0 ≤ K * (s : ℝ)^2 - 1 by linarith) hEf]

theorem jetPolynomial_stability_constants_of_row_bound (s : ℕ) (hs : 0 < s)
    {K : ℝ} (hK : 1 ≤ K)
    (hrow : ∀ (a : Fin s → ℂ) (x : ℝ), x ∈ Icc (0 : ℝ) 1 →
      ‖jetPolynomialSignal a x‖^2 ≤ K * (s : ℝ)^2 *
        (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2)) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ (a : Fin s → ℂ) (f : ℝ → ℂ),
      Continuous f →
      (∀ t ∈ Icc (0 : ℝ) 1,
        ‖f t - jetPolynomialSignal a t‖ ≤ ε * ‖a‖) →
      c * ‖a‖^2 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 ∧
        ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖^2 ≤
          (7 / 4 : ℝ) * K * (s : ℝ)^2 * (∫ t in (0 : ℝ)..1, ‖f t‖^2) := by
  obtain ⟨c, hc, hcoeff⟩ := jetPolynomial_energy_lower s hs
  refine ⟨Real.sqrt (c / 100), c / 2, Real.sqrt_pos.2 (by positivity),
    by positivity, fun a f hf hclose => ?_⟩
  apply jetPolynomial_stable_energy_and_row_bound_of_row_bound hs hK hrow hc hcoeff
    (Real.sqrt_nonneg _) (by rw [Real.sq_sqrt (by positivity)]) a hf hclose



theorem norm_sq_le_perturbation_with_parameter (u v : ℂ) {α : ℝ} (hα : 0 < α) :
    ‖u‖^2 ≤ (1 + α) * ‖v‖^2 + (1 + 1 / α) * ‖u - v‖^2 := by
  have ht : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by
    simpa [add_comm] using norm_add_le v (u - v)
  have hs := (sq_le_sq₀ (norm_nonneg u) (by positivity :
    0 ≤ ‖v‖ + ‖u - v‖)).2 ht
  have he : α * (1 + 1 / α) = α + 1 := by field_simp
  apply (mul_le_mul_iff_right₀ hα).1
  simp only [mul_add, ← mul_assoc, he]
  nlinarith only [mul_le_mul_of_nonneg_left hs hα.le,
    sq_nonneg (α * ‖v‖ - ‖u - v‖)]

/-- A freely chosen positive perturbation tolerance removes any fixed loss
in transferring polynomial point-evaluation estimates. -/
theorem jetPolynomial_stable_energy_and_row_bound_with_parameter
    {s : ℕ} (hs : 0 < s) {K : ℝ} (hK : 1 ≤ K)
    (hrow : ∀ (a : Fin s → ℂ) (x : ℝ), x ∈ Icc (0 : ℝ) 1 →
      ‖jetPolynomialSignal a x‖^2 ≤ K * (s : ℝ)^2 *
        (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2))
    {c : ℝ} (hc : 0 < c)
    (hcoeff : ∀ a : Fin s → ℂ,
      c * ‖a‖^2 ≤ ∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2)
    {α ε : ℝ} (hα : 0 < α) (hαsmall : α ≤ 1 / 8)
    (hε : 0 ≤ ε) (hεsmall : (1 + 1 / α) * ε^2 ≤ α * c)
    (a : Fin s → ℂ) {f : ℝ → ℂ} (hf : Continuous f)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖f t - jetPolynomialSignal a t‖ ≤ ε * ‖a‖) :
    (c / 2) * ‖a‖^2 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 ∧
      ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖^2 ≤
        (1 + 5 * α) * K * (s : ℝ)^2 * (∫ t in (0 : ℝ)..1, ‖f t‖^2) := by
  let Ep := ∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2
  let Ef := ∫ t in (0 : ℝ)..1, ‖f t‖^2
  let T := K * (s : ℝ)^2
  have hEp : 0 ≤ Ep := intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun _ => sq_nonneg _)
  have hEf : 0 ≤ Ef := intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun _ => sq_nonneg _)
  have hT : 1 ≤ T := by
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    dsimp [T]
    nlinarith [mul_nonneg (show 0 ≤ K - 1 by linarith) (sq_nonneg (s : ℝ)),
      sq_nonneg ((s : ℝ) - 1)]
  have herror : (1 + 1 / α) * ε^2 * ‖a‖^2 ≤ α * Ep := by
    have he := mul_le_mul_of_nonneg_right hεsmall (sq_nonneg ‖a‖)
    have hp := mul_le_mul_of_nonneg_left (hcoeff a) hα.le
    change α * (c * ‖a‖^2) ≤ α * Ep at hp
    nlinarith
  have hbase : Ep ≤ (1 + α) * Ef + (1 + 1 / α) * ε^2 * ‖a‖^2 := by
    calc
      Ep ≤ ∫ t in (0 : ℝ)..1,
          (1 + α) * ‖f t‖^2 + (1 + 1 / α) * ε^2 * ‖a‖^2 := by
        apply intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
          (((continuous_jetPolynomialSignal a).norm.pow 2).intervalIntegrable 0 1)
          ((show Continuous (fun t : ℝ =>
            (1 + α) * ‖f t‖^2 + (1 + 1 / α) * ε^2 * ‖a‖^2) by fun_prop).intervalIntegrable 0 1)
        intro t ht
        have hh := norm_sq_le_perturbation_with_parameter (jetPolynomialSignal a t) (f t) hα
        rw [norm_sub_rev] at hh
        have he := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ε * ‖a‖)).2
          (hclose t ht)
        rw [mul_pow] at he
        have he' := mul_le_mul_of_nonneg_left he
          (show 0 ≤ 1 + 1 / α by positivity)
        exact hh.trans (by nlinarith only [he'])
      _ = (1 + α) * Ef + (1 + 1 / α) * ε^2 * ‖a‖^2 := by
        rw [intervalIntegral.integral_add
          ((show Continuous (fun t : ℝ => (1 + α) * ‖f t‖^2) by fun_prop).intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1)]
        simp [Ef, intervalIntegral.integral_const_mul]
  have htransfer : (1 - α) * Ep ≤ (1 + α) * Ef := by linarith
  constructor
  · have hp := hcoeff a
    change c * ‖a‖^2 ≤ Ep at hp
    have hmul := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1 - α by linarith)
    have hsmall := mul_le_mul_of_nonneg_right (show α ≤ 1 / 8 from hαsmall)
      (show 0 ≤ c * ‖a‖^2 by positivity)
    have hsmall' := mul_le_mul_of_nonneg_right hαsmall hEf
    change (c / 2) * ‖a‖^2 ≤ Ef
    nlinarith
  · intro x hx
    have hp := hrow a x hx
    change ‖jetPolynomialSignal a x‖^2 ≤ T * Ep at hp
    have hh := norm_sq_le_perturbation_with_parameter (f x) (jetPolynomialSignal a x) hα
    have he := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ε * ‖a‖)).2
      (hclose x hx)
    rw [mul_pow] at he
    have hpoint : ‖f x‖^2 ≤ (1 + 2 * α) * T * Ep := by
      have hh' : ‖f x‖^2 ≤ (1 + α) * (T * Ep) +
          (1 + 1 / α) * ε^2 * ‖a‖^2 := by
        have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1 + α by positivity)
        have he' := mul_le_mul_of_nonneg_left he
          (show 0 ≤ 1 + 1 / α by positivity)
        exact hh.trans (by nlinarith only [hp', he'])
      nlinarith only [hh', herror,
        mul_nonneg hα.le (mul_nonneg (show 0 ≤ T - 1 by linarith) hEp)]
    have hfactor : (1 + 2 * α) * (1 + α) ≤ (1 + 5 * α) * (1 - α) := by
      nlinarith [mul_nonneg hα.le (show 0 ≤ 1 - 7 * α by linarith)]
    have h₁ := mul_le_mul_of_nonneg_left hpoint (show 0 ≤ 1 - α by linarith)
    have h₂ := mul_le_mul_of_nonneg_left htransfer (show 0 ≤ (1 + 2 * α) * T by positivity)
    have h₃ := mul_le_mul_of_nonneg_right hfactor (mul_nonneg (show 0 ≤ T by linarith) hEf)
    change ‖f x‖^2 ≤ (1 + 5 * α) * K * (s : ℝ)^2 * Ef
    rw [mul_assoc (1 + 5 * α) K ((s : ℝ)^2)]
    change ‖f x‖^2 ≤ (1 + 5 * α) * T * Ef
    apply (mul_le_mul_iff_right₀ (show 0 < 1 - α by linarith)).1
    nlinarith only [h₁, h₂, h₃]

theorem jetPolynomial_stability_constants_with_row_loss (s : ℕ) (hs : 0 < s)
    {K q : ℝ} (hK : 1 ≤ K) (hq : K < q)
    (hrow : ∀ (a : Fin s → ℂ) (x : ℝ), x ∈ Icc (0 : ℝ) 1 →
      ‖jetPolynomialSignal a x‖^2 ≤ K * (s : ℝ)^2 *
        (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2)) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ (a : Fin s → ℂ) (f : ℝ → ℂ),
      Continuous f →
      (∀ t ∈ Icc (0 : ℝ) 1, ‖f t - jetPolynomialSignal a t‖ ≤ ε * ‖a‖) →
      c * ‖a‖^2 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 ∧
      ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖^2 ≤
        q * (s : ℝ)^2 * (∫ t in (0 : ℝ)..1, ‖f t‖^2) := by
  obtain ⟨c, hc, hcoeff⟩ := jetPolynomial_energy_lower s hs
  let α : ℝ := min (1 / 8) ((q - K) / (5 * K))
  have hK0 : 0 < K := by linarith
  have hα : 0 < α := lt_min (by norm_num)
    (div_pos (sub_pos.mpr hq) (by positivity))
  have hαsmall : α ≤ 1 / 8 := min_le_left _ _
  have hαq : (1 + 5 * α) * K ≤ q := by
    have h := min_le_right (1 / 8 : ℝ) ((q - K) / (5 * K))
    have hK0 : 0 < K := by linarith
    have h' := (le_div_iff₀ (by positivity : 0 < 5 * K)).1 h
    change α * (5 * K) ≤ q - K at h'
    nlinarith
  let ε : ℝ := Real.sqrt (α * c / (1 + 1 / α))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : (1 + 1 / α) * ε^2 ≤ α * c := by
    dsimp [ε]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
    exact le_refl _
  refine ⟨ε, c / 2, hε, by positivity, ?_⟩
  intro a f hf hclose
  obtain ⟨he, hr⟩ := jetPolynomial_stable_energy_and_row_bound_with_parameter
    hs hK hrow hc hcoeff hα hαsmall hε.le hsmall a hf hclose
  refine ⟨he, fun x hx => (hr x hx).trans ?_⟩
  have hE : 0 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => sq_nonneg _)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hαq (sq_nonneg (s : ℝ))) hE

theorem unitInterval_energy_le_bound_sq {f : ℝ → ℂ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ B) :
    (∫ t in (0 : ℝ)..1, ‖f t‖^2) ≤ B^2 := by
  calc
    (∫ t in (0 : ℝ)..1, ‖f t‖^2) ≤ ∫ t in (0 : ℝ)..1, B^2 := by
      apply intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
        ((hf.norm.pow 2).intervalIntegrable 0 1)
        (continuous_const.intervalIntegrable 0 1)
      intro t ht
      exact (sq_le_sq₀ (norm_nonneg _) hB).2 (hbound t ht)
    _ = B^2 := by simp

/-- An energy lower bound for coefficients converts any derivative bound in
the coefficient norm into a derivative bound relative to the signal supremum. -/
theorem derivative_bound_of_coefficient_energy_lower {s : ℕ} (a : Fin s → ℂ)
    {f : ℝ → ℂ} (hf : Continuous f) {c L B : ℝ}
    (hc : 0 < c) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (henergy : c * ‖a‖^2 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ B)
    (hderivative : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv f t‖ ≤ L * ‖a‖) :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv f t‖ ≤ (L / Real.sqrt c) * B := by
  have hE := henergy.trans (unitInterval_energy_le_bound_sq hf hB hbound)
  have hcroot : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hscaled : Real.sqrt c * ‖a‖ ≤ B := by
    have heq : (Real.sqrt c * ‖a‖)^2 = c * ‖a‖^2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]
    rw [← heq] at hE
    exact (sq_le_sq₀ (by positivity) hB).1 hE
  have hcoeff : ‖a‖ ≤ B / Real.sqrt c :=
    (le_div_iff₀ hcroot).2 (by simpa [mul_comm] using hscaled)
  intro t ht
  calc
    ‖deriv f t‖ ≤ L * ‖a‖ := hderivative t ht
    _ ≤ L * (B / Real.sqrt c) := mul_le_mul_of_nonneg_left hcoeff hL
    _ = (L / Real.sqrt c) * B := by ring

end
end LeanNumDetect.PolynomialEvaluationBounds
