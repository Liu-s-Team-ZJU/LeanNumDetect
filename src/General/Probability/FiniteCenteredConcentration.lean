import General.Probability.FiniteScalarConcentration
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Centered Hoeffding bounds for finite populations with values in the unit
disk. Centering preserves the coordinate interval widths, and hence preserves
the exponent in the zero-mean bounds. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ENNReal
open MeasureTheory

namespace LeanNumDetect.FiniteMatrixSampling

/-- Hoeffding's lemma for the finite uniform law, with the original width-two
interval retained after centering. -/
theorem finiteAverage_exp_mul_sub_mean_le {κ : Type*} [Fintype κ] [Nonempty κ]
    (f : κ → ℝ) (hbound : ∀ k, |f k| ≤ 1) (θ : ℝ) :
    finiteAverage (fun k => Real.exp (θ * (f k - finiteAverage f))) ≤
      Real.exp (θ ^ 2 / 2) := by
  classical
  letI : MeasurableSpace κ := ⊤
  let μ : Measure κ := (Fintype.card κ : ℝ≥0∞)⁻¹ • Measure.count
  have hc : (Fintype.card κ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  letI : IsProbabilityMeasure μ := ⟨by
    simpa [μ] using ENNReal.inv_mul_cancel hc (by finiteness)⟩
  have hint (g : κ → ℝ) : ∫ k, g k ∂μ = finiteAverage g := by
    simp [μ, integral_smul_measure, finiteAverage]
  have hb : ∀ᵐ k ∂μ, f k ∈ Set.Icc (-1 : ℝ) 1 :=
    Filter.Eventually.of_forall (fun k => abs_le.mp (hbound k))
  have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    (μ := μ) (measurable_of_countable f).aemeasurable hb
  have hm := h.mgf_le θ
  norm_num [ProbabilityTheory.mgf, hint] at hm
  exact hm

/-- Exponential moment of a centered bounded population sum without replacement. -/
theorem sample_exp_centered_sum_le {N m : ℕ} (hN : 0 < N) (hmN : m ≤ N)
    (f : Fin N → ℝ) (hbound : ∀ k, |f k| ≤ 1) (θ : ℝ) :
    finiteAverage (fun Ω : Sample N m =>
      Real.exp (θ * ∑ k ∈ Ω.val, (f k - finiteAverage f))) ≤
      Real.exp ((m : ℝ) * θ ^ 2 / 2) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => Real.exp (θ * x)) := by
    simpa [Function.comp_def, smul_eq_mul] using
      convexOn_exp.comp_linearMap (θ • LinearMap.id (R := ℝ) (M := ℝ))
  have hstep (H : ℝ) :
      finiteAverage (fun k => Real.exp (θ * (H + (f k - finiteAverage f)))) ≤
        Real.exp (θ ^ 2 / 2) * Real.exp (θ * H) := by
    simp_rw [mul_add, Real.exp_add]
    rw [show finiteAverage (fun k =>
        Real.exp (θ * H) * Real.exp (θ * (f k - finiteAverage f))) =
      Real.exp (θ * H) * finiteAverage (fun k =>
        Real.exp (θ * (f k - finiteAverage f))) from finiteAverage_smul _ _]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (finiteAverage_exp_mul_sub_mean_le f hbound θ) (Real.exp_nonneg (θ * H))
  have h := finiteAverage_subset_sum_le hN hmN
    (fun k => f k - finiteAverage f) hconv (Real.exp_nonneg (θ ^ 2 / 2)) hstep
  simpa only [mul_zero, Real.exp_zero, mul_one, ← Real.exp_nat_mul,
    mul_div_assoc] using h

/-- Centering before sampling agrees with subtracting the same center afterwards. -/
theorem sample_mean_centered {κ K : Type*} [Field K] [CharZero K]
    {m : ℕ} (hm : 1 ≤ m) (f : κ → K) (c : K) (Ω : FiniteSample κ m) :
    (m : K)⁻¹ * ∑ k ∈ Ω.val, (f k - c) =
      ((m : K)⁻¹ * ∑ k ∈ Ω.val, f k) - c := by
  have hm0 : (m : K) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp [Finset.sum_sub_distrib, Ω.property, nsmul_eq_mul, mul_sub, hm0]

/-- One-sided centered Hoeffding inequality on a finite indexed population. -/
theorem sample_real_centered_mean_upper_probability_le {N m : ℕ} (hm : 1 ≤ m)
    (hmN : m ≤ N) (f : Fin N → ℝ) (hbound : ∀ k, |f k| ≤ 1)
    {u : ℝ} (hu : 0 < u) :
    probability (fun Ω : Sample N m =>
      u < ((m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k) - finiteAverage f) ≤
      Real.exp (-(m : ℝ) * u ^ 2 / 2) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hmoment := sample_exp_centered_sum_le (by omega : 0 < N) hmN f hbound u
  have h := probability_le_exponential_moment
    (fun Ω : Sample N m => u < (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, (f k - finiteAverage f))
    (fun Ω => Real.exp (u * ∑ k ∈ Ω.val, (f k - finiteAverage f)))
    (q := (m : ℝ) * u ^ 2) (b := (m : ℝ) * u ^ 2 / 2) (D := 1)
    (fun _ => Real.exp_nonneg _) (fun Ω hΩ => by
      apply Real.exp_le_exp.mpr
      have ht : (m : ℝ) * u < ∑ k ∈ Ω.val, (f k - finiteAverage f) := by
        rwa [← div_eq_inv_mul, lt_div_iff₀ hmr, mul_comm] at hΩ
      nlinarith [mul_pos hu (sub_pos.mpr ht)]) (by simpa using hmoment)
  simpa only [sample_mean_centered hm, one_mul,
    show (m : ℝ) * u ^ 2 / 2 - (m : ℝ) * u ^ 2 =
      -(m : ℝ) * u ^ 2 / 2 by ring] using h

/-- The centered one-sided bound on actual subsets of an arbitrary finite type. -/
theorem finiteSample_real_centered_mean_upper_probability_le {κ : Type*} [Fintype κ]
    [DecidableEq κ] {m : ℕ} (hm : 1 ≤ m) (hmκ : m ≤ Fintype.card κ)
    (f : κ → ℝ) (hbound : ∀ k, |f k| ≤ 1) {u : ℝ} (hu : 0 < u) :
    probability (fun Ω : FiniteSample κ m =>
      u < ((m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k) - finiteAverage f) ≤
      Real.exp (-(m : ℝ) * u ^ 2 / 2) := by
  classical
  let e := (Fintype.equivFin κ).symm
  have h := sample_real_centered_mean_upper_probability_le hm hmκ (fun k => f (e k))
    (fun k => hbound (e k)) hu
  rw [← probability_comp_equiv (finiteSampleEquiv e m)
    (fun Ω : FiniteSample κ m =>
      u < ((m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k) - finiteAverage f)]
  simpa only [finiteAverage_comp_equiv e f, finiteSampleEquiv_val,
    Finset.sum_map, Equiv.coe_toEmbedding] using h

/-- The centered two-sided bound keeps the same width-two exponent. -/
theorem finiteSample_real_centered_mean_abs_probability_le {κ : Type*} [Fintype κ]
    [DecidableEq κ] {m : ℕ} (hm : 1 ≤ m) (hmκ : m ≤ Fintype.card κ)
    (f : κ → ℝ) (hbound : ∀ k, |f k| ≤ 1) {u : ℝ} (hu : 0 < u) :
    probability (fun Ω : FiniteSample κ m =>
      u < |((m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k) - finiteAverage f|) ≤
      2 * Real.exp (-(m : ℝ) * u ^ 2 / 2) := by
  classical
  have hp := finiteSample_real_centered_mean_upper_probability_le hm hmκ f hbound hu
  have hn := finiteSample_real_centered_mean_upper_probability_le hm hmκ (fun k => -f k)
    (by simpa using hbound) hu
  have hneg : finiteAverage (fun k => -f k) = -finiteAverage f := by
    simp [finiteAverage]
  simp only [hneg, Finset.sum_neg_distrib, mul_neg, neg_sub_neg] at hn
  have h := probability_or_le
    (fun Ω : FiniteSample κ m =>
      u < ((m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k) - finiteAverage f)
    (fun Ω : FiniteSample κ m =>
      u < finiteAverage f - (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k)
  have heq : (fun Ω : FiniteSample κ m =>
      u < |((m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k) - finiteAverage f|) =
      (fun Ω : FiniteSample κ m =>
        u < ((m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k) - finiteAverage f ∨
        u < finiteAverage f - (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, f k) := by
    funext Ω
    simp only [lt_abs, neg_sub]
  rw [heq]
  linarith

/-- Centered complex Hoeffding inequality for a uniform fixed-size subset.
The full-population mean is subtracted without changing the sharp coordinate
interval widths, giving the same exponent as in the zero-mean theorem. -/
theorem finiteSample_complex_centered_norm_probability_le {κ : Type*} [Fintype κ]
    [DecidableEq κ] {m : ℕ} (hm : 1 ≤ m) (hmκ : m ≤ Fintype.card κ)
    (f : κ → ℂ) (hbound : ∀ k, ‖f k‖ ≤ 1) {u : ℝ} (hu : 0 < u) :
    probability (fun Ω : FiniteSample κ m =>
      u < ‖((m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f k) -
        (Fintype.card κ : ℂ)⁻¹ * ∑ k, f k‖) ≤
      4 * Real.exp (-(m : ℝ) * u ^ 2 / 4) := by
  classical
  let μ : ℂ := (Fintype.card κ : ℂ)⁻¹ * ∑ k, f k
  have hv : 0 < u / Real.sqrt 2 := div_pos hu (Real.sqrt_pos.2 (by norm_num))
  have hr := finiteSample_real_centered_mean_abs_probability_le hm hmκ (fun k => (f k).re)
    (fun k => (Complex.abs_re_le_norm (f k)).trans (hbound k)) hv
  have hi := finiteSample_real_centered_mean_abs_probability_le hm hmκ (fun k => (f k).im)
    (fun k => (Complex.abs_im_le_norm (f k)).trans (hbound k)) hv
  have hprob := probability_mono (fun Ω : FiniteSample κ m => fun hΩ =>
    complex_norm_gt_imp_coordinate (z := ((m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f k) - μ) hu hΩ)
  have hunion := probability_or_le
    (fun Ω : FiniteSample κ m => u / Real.sqrt 2 <
      |(((m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f k) - μ).re|)
    (fun Ω : FiniteSample κ m => u / Real.sqrt 2 <
      |(((m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f k) - μ).im|)
  have hre_sum (c : ℕ) (S : Finset κ) :
      ((c : ℂ)⁻¹ * ∑ k ∈ S, f k).re = (c : ℝ)⁻¹ * ∑ k ∈ S, (f k).re := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    simp [Complex.mul_re]
  have him_sum (c : ℕ) (S : Finset κ) :
      ((c : ℂ)⁻¹ * ∑ k ∈ S, f k).im = (c : ℝ)⁻¹ * ∑ k ∈ S, (f k).im := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    simp [Complex.mul_im]
  have hre (Ω : FiniteSample κ m) :
      (((m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f k) - μ).re =
        ((m : ℝ)⁻¹ * ∑ k ∈ Ω.val, (f k).re) - finiteAverage (fun k => (f k).re) := by
    rw [Complex.sub_re, hre_sum]
    congr 1
    simp [μ, finiteAverage]
  have him (Ω : FiniteSample κ m) :
      (((m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f k) - μ).im =
        ((m : ℝ)⁻¹ * ∑ k ∈ Ω.val, (f k).im) - finiteAverage (fun k => (f k).im) := by
    rw [Complex.sub_im, him_sum]
    congr 1
    simp [μ, finiteAverage]
  simp_rw [hre, him] at hprob hunion
  have hsq : (u / Real.sqrt 2) ^ 2 = u ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsq] at hr hi
  have he : -(m : ℝ) * (u ^ 2 / 2) / 2 = -(m : ℝ) * u ^ 2 / 4 := by ring
  rw [he] at hr hi
  exact (hprob.trans hunion).trans (by linarith)

end LeanNumDetect.FiniteMatrixSampling
