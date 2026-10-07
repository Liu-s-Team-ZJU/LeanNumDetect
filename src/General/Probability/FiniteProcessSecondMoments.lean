import General.Probability.FiniteBernoulliProcess
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Second moments of finite process maxima

A two-sided subgaussian exponential moment gives a logarithmic-cardinality
second-moment bound for the absolute maximum. The proof uses an elementary
shifted exponential majorant, so no tail integration or concentration result
is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

/-- A shifted exponential controls the square of a nonnegative variable. -/
theorem nonneg_square_le_shifted_exponential {x a θ : ℝ}
    (hx : 0 ≤ x) (hθ : 0 < θ) :
    x ^ 2 ≤ 2 * a ^ 2 + 8 / θ ^ 2 * Real.exp (θ * (x - a)) := by
  have he : 0 ≤ 8 / θ ^ 2 * Real.exp (θ * (x - a)) := by positivity
  by_cases hxa : x ≤ a
  · have h := pow_le_pow_left₀ hx hxa 2
    nlinarith [sq_nonneg a]
  · have hd : 0 ≤ x - a := sub_nonneg.mpr (lt_of_not_ge hxa).le
    have hl : θ * (x - a) / 2 ≤ Real.exp (θ * (x - a) / 2) := by
      linarith [Real.add_one_le_exp (θ * (x - a) / 2)]
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ θ * (x - a) / 2) hl 2
    have hexp : Real.exp (θ * (x - a) / 2) ^ 2 = Real.exp (θ * (x - a)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hexp] at hsq
    have hdiv : (x - a) ^ 2 ≤ 4 / θ ^ 2 * Real.exp (θ * (x - a)) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hθ)).2
      nlinarith
    rw [show 8 / θ ^ 2 = 2 * (4 / θ ^ 2) by ring]
    nlinarith [sq_nonneg (x - 2 * a)]

/-- A free Laplace parameter and threshold give a second-moment maximal
bound whenever their exponential-moment budget is at most one. -/
theorem finiteProcess_absoluteMaximum_square_expectation_parameter_bound
    {α J : Type*} [Fintype α] [Nonempty α] [Fintype J] [Nonempty J]
    (Z : J → α → ℝ) {θ a V : ℝ} (hθ : 0 < θ)
    (hbudget : Real.log (2 * (Fintype.card J : ℝ)) + V ≤ θ * a)
    (hplus : ∀ j, finiteAverage (fun ω => Real.exp (θ * Z j ω)) ≤ Real.exp V)
    (hminus : ∀ j, finiteAverage (fun ω => Real.exp (-(θ * Z j ω))) ≤ Real.exp V) :
    finiteAverage (fun ω => finiteProcessAbsoluteMaximum Z ω ^ 2) ≤
      2 * a ^ 2 + 8 / θ ^ 2 := by
  have hmax := finiteProcess_absoluteMaximum_exp_bound Z θ V hplus hminus
  have hnormalized : finiteAverage (fun ω =>
      Real.exp (θ * (finiteProcessAbsoluteMaximum Z ω - a))) ≤ 1 := by
    have heq : (fun ω => Real.exp (θ * (finiteProcessAbsoluteMaximum Z ω - a))) =
        (fun ω => Real.exp (-(θ * a)) • Real.exp (θ * finiteProcessAbsoluteMaximum Z ω)) := by
      funext ω
      simp only [smul_eq_mul, ← Real.exp_add]
      congr 1
      ring
    rw [heq, finiteAverage_smul]
    change Real.exp (-(θ * a)) * _ ≤ 1
    apply (mul_le_mul_of_nonneg_left hmax (Real.exp_nonneg _)).trans
    have hc : (0 : ℝ) < 2 * (Fintype.card J : ℝ) := by positivity
    have he : Real.exp (Real.log (2 * (Fintype.card J : ℝ)) + V - θ * a) ≤ 1 := by
      exact (Real.exp_le_exp.mpr (sub_nonpos.mpr hbudget)).trans_eq Real.exp_zero
    calc
      _ = Real.exp (Real.log (2 * (Fintype.card J : ℝ)) + V - θ * a) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log hc, Real.exp_neg]
        ring
      _ ≤ 1 := he
  calc
    _ ≤ finiteAverage (fun ω => 2 * a ^ 2 + 8 / θ ^ 2 *
        Real.exp (θ * (finiteProcessAbsoluteMaximum Z ω - a))) :=
      finiteAverage_mono (fun ω => nonneg_square_le_shifted_exponential
        (finiteProcessAbsoluteMaximum_nonneg Z ω) hθ)
    _ = 2 * a ^ 2 + 8 / θ ^ 2 * finiteAverage (fun ω =>
        Real.exp (θ * (finiteProcessAbsoluteMaximum Z ω - a))) := by
      rw [finiteAverage_add, finiteAverage_const]
      change (2 * a ^ 2 + finiteAverage (fun ω => (8 / θ ^ 2) •
        Real.exp (θ * (finiteProcessAbsoluteMaximum Z ω - a)))) =
          2 * a ^ 2 + (8 / θ ^ 2) • finiteAverage _
      rw [finiteAverage_smul]
    _ ≤ _ := add_le_add le_rfl (by
      simpa using mul_le_mul_of_nonneg_left hnormalized (by positivity : 0 ≤ 8 / θ ^ 2))

/-- Optimizing the shifted majorant gives a second-moment bound with a
single logarithm of the finite process cardinality. -/
theorem finiteProcess_absoluteMaximum_square_expectation_le
    {α J : Type*} [Fintype α] [Nonempty α] [Fintype J] [Nonempty J]
    (Z : J → α → ℝ) {V : ℝ} (hV : 0 < V)
    (hplus : ∀ θ j, finiteAverage (fun ω => Real.exp (θ * Z j ω)) ≤ Real.exp (θ ^ 2 * V / 2))
    (hminus : ∀ θ j, finiteAverage (fun ω => Real.exp (-(θ * Z j ω))) ≤ Real.exp (θ ^ 2 * V / 2)) :
    finiteAverage (fun ω => finiteProcessAbsoluteMaximum Z ω ^ 2) ≤
      20 * V * Real.log (2 * (Fintype.card J : ℝ)) := by
  let L := Real.log (2 * (Fintype.card J : ℝ))
  have hc : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast Fintype.card_pos
  have hLhalf : (1 / 2 : ℝ) ≤ L := by
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ 2 * (Fintype.card J : ℝ) by nlinarith)
    dsimp [L]
    linarith [Real.log_two_gt_d9]
  have hL : 0 < L := by linarith
  let θ := Real.sqrt (2 * L) / Real.sqrt V
  let a := Real.sqrt V * Real.sqrt (2 * L)
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hsL : 0 < Real.sqrt (2 * L) := Real.sqrt_pos.mpr (by positivity)
  have hθ : 0 < θ := div_pos hsL hsV
  have hVsq := Real.sq_sqrt hV.le
  have hLsq := Real.sq_sqrt (show 0 ≤ 2 * L by positivity)
  have hparam : θ ^ 2 * V / 2 = L := by
    dsimp [θ]
    rw [div_pow, hLsq, hVsq]
    field_simp
  have hbudget : L + θ ^ 2 * V / 2 ≤ θ * a := by
    rw [hparam]
    dsimp [θ, a]
    have hsV0 := hsV.ne'
    field_simp
    nlinarith [Real.sq_sqrt (show 0 ≤ L * 2 by positivity)]
  have hbound := finiteProcess_absoluteMaximum_square_expectation_parameter_bound Z
    hθ hbudget (hplus θ) (hminus θ)
  apply hbound.trans
  have hae : a ^ 2 = 2 * V * L := by
    dsimp [a]
    rw [mul_pow, hVsq, hLsq]
    ring
  have hθsq : θ ^ 2 = 2 * L / V := by
    dsimp [θ]
    rw [div_pow, hLsq, hVsq]
  rw [hae, hθsq]
  dsimp only [L]
  change 2 * (2 * V * L) + 8 / (2 * L / V) ≤ 20 * V * L
  have hsmall : 1 ≤ 4 * L ^ 2 := by nlinarith [sq_nonneg (L - 1 / 2)]
  have hdiv : V / L ≤ 4 * V * L := by
    apply (div_le_iff₀ hL).2
    nlinarith [mul_le_mul_of_nonneg_left hsmall hV.le]
  have hid : 8 / (2 * L / V) = 4 * (V / L) := by field_simp; ring
  rw [hid]
  nlinarith

end LeanNumDetect.FiniteMatrixSampling
