import General.Probability.MatrixLaplace
import General.Probability.FiniteLaplace
import General.Probability.FinitePopulationReindex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Hoeffding bounds for bounded scalar populations sampled without replacement.
The proofs use the proved convex sampling comparison, elementary exponential
moments, and finite counting probabilities. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

/-- The elementary zero-mean bounded-variable exponential-moment estimate. -/
theorem finiteAverage_exp_mul_le {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : κ → ℝ) (hbound : ∀ k, |f k| ≤ 1) (hzero : ∑ k, f k = 0) (θ : ℝ) :
    finiteAverage (fun k => Real.exp (θ * f k)) ≤ Real.exp (θ ^ 2 / 2) := by
  have hc : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ finiteAverage (fun k => Real.cosh θ + f k * Real.sinh θ) :=
      finiteAverage_mono fun k => by
        simpa only [mul_comm θ] using Real.exp_mul_le_cosh_add_mul_sinh (hbound k) θ
    _ = Real.cosh θ := by
      simp [finiteAverage, Finset.sum_add_distrib, ← Finset.sum_mul, hzero, hc]
    _ ≤ _ := Real.cosh_le_exp_half_sq θ

/-- Exponential moment of a zero-mean bounded population sum without replacement. -/
theorem finiteSample_exp_sum_le {N m : ℕ} (hN : 0 < N) (hmN : m ≤ N)
    (f : Fin N → ℝ) (hbound : ∀ k, |f k| ≤ 1) (hzero : ∑ k, f k = 0)
    (θ : ℝ) :
    finiteAverage (fun Ω : Sample N m => Real.exp (θ * ∑ k ∈ Ω.val, f k)) ≤
      Real.exp ((m : ℝ) * θ ^ 2 / 2) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => Real.exp (θ * x)) := by
    simpa [Function.comp_def, smul_eq_mul] using
      convexOn_exp.comp_linearMap (θ • LinearMap.id (R := ℝ) (M := ℝ))
  have hstep (H : ℝ) :
      finiteAverage (fun k => Real.exp (θ * (H + f k))) ≤
        Real.exp (θ ^ 2 / 2) * Real.exp (θ * H) := by
    simp_rw [mul_add, Real.exp_add]
    rw [show finiteAverage (fun k => Real.exp (θ * H) * Real.exp (θ * f k)) =
      Real.exp (θ * H) * finiteAverage (fun k => Real.exp (θ * f k)) from
      finiteAverage_smul _ _]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (finiteAverage_exp_mul_le f hbound hzero θ) (Real.exp_nonneg (θ * H))
  have h := finiteAverage_subset_sum_le hN hmN f hconv
    (Real.exp_nonneg (θ ^ 2 / 2)) hstep
  simpa only [mul_zero, Real.exp_zero, mul_one, ← Real.exp_nat_mul,
    mul_div_assoc] using h

/-- The one-sided Hoeffding bound for an empirical mean sampled without replacement. -/
theorem sample_real_mean_upper_probability_le {N m : ℕ} (hm : 1 ≤ m)
    (hmN : m ≤ N) (f : Fin N → ℝ) (hbound : ∀ k, |f k| ≤ 1)
    (hzero : ∑ k, f k = 0) {u : ℝ} (hu : 0 < u) :
    probability (fun Ω : Sample N m => u < (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k) ≤
      Real.exp (-(m : ℝ) * u ^ 2 / 2) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hmoment := finiteSample_exp_sum_le (by omega : 0 < N) hmN f hbound hzero u
  have h := probability_le_exponential_moment
    (fun Ω : Sample N m => u < (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k)
    (fun Ω => Real.exp (u * ∑ k ∈ Ω.val, f k))
    (q := (m : ℝ) * u ^ 2) (b := (m : ℝ) * u ^ 2 / 2) (D := 1)
    (fun _ => Real.exp_nonneg _) (fun Ω hΩ => by
      apply Real.exp_le_exp.mpr
      have ht : (m : ℝ) * u < ∑ k ∈ Ω.val, f k := by
        rwa [← div_eq_inv_mul, lt_div_iff₀ hmr, mul_comm] at hΩ
      nlinarith [mul_pos hu (sub_pos.mpr ht)]) (by simpa using hmoment)
  simpa only [one_mul, show (m : ℝ) * u ^ 2 / 2 - (m : ℝ) * u ^ 2 =
    -(m : ℝ) * u ^ 2 / 2 by ring] using h

/-- A one-sided empirical-mean bound on subsets of an arbitrary finite type. -/
theorem finiteSample_real_mean_upper_probability_le {κ : Type*} [Fintype κ]
    [DecidableEq κ] {m : ℕ} (hm : 1 ≤ m) (hmκ : m ≤ Fintype.card κ)
    (f : κ → ℝ) (hbound : ∀ k, |f k| ≤ 1) (hzero : ∑ k, f k = 0)
    {u : ℝ} (hu : 0 < u) :
    probability (fun Ω : FiniteSample κ m => u < (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k) ≤
      Real.exp (-(m : ℝ) * u ^ 2 / 2) := by
  classical
  let e := (Fintype.equivFin κ).symm
  have h := sample_real_mean_upper_probability_le hm hmκ (fun k => f (e k))
    (fun k => hbound (e k)) (by simpa only [e.sum_comp] using hzero) hu
  rw [← probability_comp_equiv (finiteSampleEquiv e m)
    (fun Ω : FiniteSample κ m => u < (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k)]
  simpa using h

/-- A two-sided empirical-mean bound on subsets of an arbitrary finite type. -/
theorem finiteSample_real_mean_abs_probability_le {κ : Type*} [Fintype κ]
    [DecidableEq κ] {m : ℕ} (hm : 1 ≤ m) (hmκ : m ≤ Fintype.card κ)
    (f : κ → ℝ) (hbound : ∀ k, |f k| ≤ 1) (hzero : ∑ k, f k = 0)
    {u : ℝ} (hu : 0 < u) :
    probability (fun Ω : FiniteSample κ m => u < |(m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k|) ≤
      2 * Real.exp (-(m : ℝ) * u ^ 2 / 2) := by
  classical
  have hp := finiteSample_real_mean_upper_probability_le hm hmκ f hbound hzero hu
  have hn := finiteSample_real_mean_upper_probability_le hm hmκ (fun k => -f k)
    (by simpa using hbound) (by simp [hzero]) hu
  have h := probability_or_le
    (fun Ω : FiniteSample κ m => u < (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k)
    (fun Ω : FiniteSample κ m => u < (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, -f k)
  have heq : (fun Ω : FiniteSample κ m =>
      u < |(m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k|) =
      (fun Ω : FiniteSample κ m =>
        u < (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k ∨
        u < (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, -f k) := by
    funext Ω
    simp only [Finset.sum_neg_distrib, mul_neg, lt_abs]
  rw [heq]
  linarith

/-- A complex number exceeding a radius has a large real or imaginary coordinate. -/
theorem complex_norm_gt_imp_coordinate {z : ℂ} {u : ℝ} (hu : 0 < u)
    (hz : u < ‖z‖) : u / Real.sqrt 2 < |z.re| ∨ u / Real.sqrt 2 < |z.im| := by
  by_contra h
  push Not at h
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : (u / Real.sqrt 2) ^ 2 = u ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hr := sq_le_sq₀ (abs_nonneg z.re) (by positivity : 0 ≤ u / Real.sqrt 2)
  have hi := sq_le_sq₀ (abs_nonneg z.im) (by positivity : 0 ≤ u / Real.sqrt 2)
  have hrr := hr.2 h.1
  have hir := hi.2 h.2
  rw [sq_abs, hsq] at hrr hir
  have hn := Complex.sq_norm z
  rw [Complex.normSq_apply] at hn
  nlinarith [sq_lt_sq₀ hu.le (norm_nonneg z) |>.2 hz]

/-- Complex Hoeffding inequality for a uniform subset of a finite population.
The factor four comes from the two tails of each real coordinate. -/
theorem finiteSample_complex_norm_probability_le {κ : Type*} [Fintype κ]
    [DecidableEq κ] {m : ℕ} (hm : 1 ≤ m) (hmκ : m ≤ Fintype.card κ)
    (f : κ → ℂ) (hbound : ∀ k, ‖f k‖ ≤ 1) (hzero : ∑ k, f k = 0)
    {u : ℝ} (hu : 0 < u) :
    probability (fun Ω : FiniteSample κ m =>
      u < ‖(m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f k‖) ≤
      4 * Real.exp (-(m : ℝ) * u ^ 2 / 4) := by
  classical
  have hv : 0 < u / Real.sqrt 2 := div_pos hu (Real.sqrt_pos.2 (by norm_num))
  have hr := finiteSample_real_mean_abs_probability_le hm hmκ (fun k => (f k).re)
    (fun k => (Complex.abs_re_le_norm (f k)).trans (hbound k))
    (by simpa using congrArg Complex.re hzero) hv
  have hi := finiteSample_real_mean_abs_probability_le hm hmκ (fun k => (f k).im)
    (fun k => (Complex.abs_im_le_norm (f k)).trans (hbound k))
    (by simpa using congrArg Complex.im hzero) hv
  have hprob := probability_mono (fun Ω : FiniteSample κ m => fun hΩ =>
    complex_norm_gt_imp_coordinate (z := (m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f k) hu hΩ)
  have hunion := probability_or_le
    (fun Ω : FiniteSample κ m => u / Real.sqrt 2 <
      |((m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f k).re|)
    (fun Ω : FiniteSample κ m => u / Real.sqrt 2 <
      |((m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f k).im|)
  have hre (Ω : FiniteSample κ m) :
      ((m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f k).re =
        (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, (f k).re := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    simp [Complex.mul_re]
  have him (Ω : FiniteSample κ m) :
      ((m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f k).im =
        (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, (f k).im := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    simp [Complex.mul_im]
  simp_rw [hre, him] at hprob hunion
  have hsq : (u / Real.sqrt 2) ^ 2 = u ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsq] at hr hi
  have he : -(m : ℝ) * (u ^ 2 / 2) / 2 = -(m : ℝ) * u ^ 2 / 4 := by ring
  rw [he] at hr hi
  exact (hprob.trans hunion).trans (by linarith)

end LeanNumDetect.FiniteMatrixSampling
