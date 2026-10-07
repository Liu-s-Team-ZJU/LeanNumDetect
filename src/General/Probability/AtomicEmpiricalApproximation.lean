import General.Probability.ComplexAtomicSimplex
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Empirical approximation by a finite atomic probability simplex

The finite atomic representation is converted into its actual weighted
probability law. Independent draws have the prescribed barycenter, and
bounded real atom evaluations satisfy a Gaussian empirical-mean tail.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace LeanNumDetect.BoundedRieszConcentration

/-- A probability mass function from nonnegative simplex coordinates. -/
noncomputable def finiteSimplexPMF {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (w a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hw a), hsum]
    norm_num)

theorem finiteSimplexPMF_toReal {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1) (a : α) :
    (finiteSimplexPMF w hw hsum a).toReal = w a :=
  ENNReal.toReal_ofReal (hw a)

theorem integral_finiteSimplexPMF {α E : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1) (f : α → E) :
    (∫ a, f a ∂(finiteSimplexPMF w hw hsum).toMeasure) = ∑ a, w a • f a := by
  rw [PMF.integral_eq_sum]
  simp only [finiteSimplexPMF_toReal]

/-- Expectations of functions of one independent draw equal their
expectations under the reference law. -/
theorem integral_iid_evaluation {α E : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsProbabilityMeasure μ] {L : ℕ}
    (f : α → E) (i : Fin L) :
    (∫ ω : Fin L → α, f (ω i) ∂Measure.pi (fun _ : Fin L => μ)) = ∫ a, f a ∂μ := by
  have hmp := measurePreserving_eval (fun _ : Fin L => μ) i
  have hf : AEStronglyMeasurable f
      (Measure.map (Function.eval i) (Measure.pi (fun _ : Fin L => μ))) := by
    rw [hmp.map_eq]
    exact Integrable.of_finite.aestronglyMeasurable
  have h := integral_map hmp.measurable.aemeasurable hf
  rw [hmp.map_eq] at h
  exact h.symm

/-- Hoeffding's empirical-mean tail for independent draws from an arbitrary
finite weighted law. The atom distribution need not be uniform. -/
theorem iid_bounded_real_mean_upper_probability_le {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (y : α → ℝ)
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (hy : ∀ a, |y a| ≤ B)
    {L : ℕ} (hL : 0 < L) :
    (Measure.pi (fun _ : Fin L => μ)).real
      {ω | r < (L : ℝ)⁻¹ * ∑ i, y (ω i) - ∫ a, y a ∂μ} ≤
      Real.exp (-((L : ℝ) * r ^ 2 / (2 * B ^ 2))) := by
  let η := Measure.pi (fun _ : Fin L => μ)
  letI : IsProbabilityMeasure η := by dsimp [η]; infer_instance
  let c : ℝ≥0 := ⟨B ^ 2, sq_nonneg B⟩
  let Y := fun (_i : Fin L) a => y a - ∫ b, y b ∂μ
  have hmeas : Measurable y := measurable_of_countable _
  have hid : iIndepFun (fun i (ω : Fin L → α) => Y i (ω i)) η :=
    iIndepFun_pi (fun _ => (hmeas.sub_const _).aemeasurable)
  have hsub (i : Fin L) : HasSubgaussianMGF (fun ω : Fin L → α => Y i (ω i)) c η := by
    have h := hasSubgaussianMGF_of_mem_Icc
      ((hmeas.comp (measurable_pi_apply i)).aemeasurable (μ := η))
      (ae_of_all η (fun ω => abs_le.mp (hy (ω i))))
    change HasSubgaussianMGF
      (fun ω : Fin L → α => y (ω i) - ∫ ω : Fin L → α, y (ω i) ∂η)
      ((‖B - -B‖₊ / 2) ^ 2) η at h
    have hmean : (∫ ω : Fin L → α, y (ω i) ∂η) = ∫ a, y a ∂μ :=
      integral_iid_evaluation μ y i
    have hc : (‖B - -B‖₊ / 2) ^ 2 = c := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, NNReal.coe_ofNat,
        Real.norm_eq_abs, sub_neg_eq_add]
      rw [abs_of_nonneg (by linarith : 0 ≤ B + B)]
      change ((B + B) / 2) ^ 2 = B ^ 2
      ring
    rw [hmean, hc] at h
    exact h
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hid
    (s := Finset.univ) (c := fun _ => c) (fun i _ => hsub i)
    (ε := (L : ℝ) * r) (by positivity)
  have hmono : η.real {ω | r < (L : ℝ)⁻¹ * ∑ i, y (ω i) - ∫ a, y a ∂μ} ≤
      η.real {ω | (L : ℝ) * r ≤ ∑ i, Y i (ω i)} := by
    refine measureReal_mono ?_ (measure_ne_top η _)
    intro ω hω
    simp only [Set.mem_setOf_eq] at *
    dsimp [Y]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hω' : (L : ℝ) * (r + ∫ a, y a ∂μ) < ∑ i, y (ω i) := by
      rw [lt_sub_iff_add_lt] at hω
      have h := (lt_div_iff₀ hLr).mp
        (show r + ∫ a, y a ∂μ < (∑ i, y (ω i)) / L by
          simpa only [div_eq_mul_inv, mul_comm] using hω)
      nlinarith
    nlinarith
  have hs : (∑ _i : Fin L, c : ℝ≥0) = (L : ℝ≥0) * c := by simp
  rw [hs] at htail
  have hexp : -(L : ℝ) * r ^ 2 / (2 * B ^ 2) =
      -((L : ℝ) * r) ^ 2 / (2 * ((L : ℝ≥0) * c : ℝ≥0)) := by
    change -(L : ℝ) * r ^ 2 / (2 * B ^ 2) =
      -((L : ℝ) * r) ^ 2 / (2 * ((L : ℝ) * B ^ 2))
    field_simp
  rw [← hexp] at htail
  rw [show -(L : ℝ) * r ^ 2 / (2 * B ^ 2) =
    -((L : ℝ) * r ^ 2 / (2 * B ^ 2)) by ring] at htail
  exact hmono.trans htail

/-- The two real tails have the same Gaussian bound. -/
theorem iid_bounded_real_mean_abs_probability_le {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (y : α → ℝ)
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (hy : ∀ a, |y a| ≤ B)
    {L : ℕ} (hL : 0 < L) :
    (Measure.pi (fun _ : Fin L => μ)).real
      {ω | r < |(L : ℝ)⁻¹ * ∑ i, y (ω i) - ∫ a, y a ∂μ|} ≤
      2 * Real.exp (-((L : ℝ) * r ^ 2 / (2 * B ^ 2))) := by
  let η := Measure.pi (fun _ : Fin L => μ)
  letI : IsProbabilityMeasure η := by dsimp [η]; infer_instance
  let D := fun ω : Fin L → α => (L : ℝ)⁻¹ * ∑ i, y (ω i) - ∫ a, y a ∂μ
  have hp := iid_bounded_real_mean_upper_probability_le μ y hB hr hy hL
  have hn := iid_bounded_real_mean_upper_probability_le μ (fun a => -y a) hB hr
    (by simpa using hy) hL
  have hneg (ω : Fin L → α) :
      (L : ℝ)⁻¹ * ∑ i, -y (ω i) - ∫ a, -y a ∂μ = -D ω := by
    simp only [Finset.sum_neg_distrib, integral_neg]
    dsimp [D]
    ring
  simp_rw [hneg] at hn
  have hmono : η.real {ω | r < |D ω|} ≤
      η.real ({ω | r < D ω} ∪ {ω | r < -D ω}) := by
    refine measureReal_mono ?_ (measure_ne_top η _)
    intro ω hω
    by_cases hD : 0 ≤ D ω
    · exact Or.inl (by simpa only [Set.mem_setOf_eq, abs_of_nonneg hD] using hω)
    · exact Or.inr (by simpa only [Set.mem_setOf_eq, abs_of_neg (lt_of_not_ge hD)] using hω)
  exact hmono.trans ((measureReal_union_le _ _).trans (by linarith))

/-- Four scalar Hoeffding tails control one complex empirical mean.
The constants are absolute and independent of the atom-law weights. -/
theorem iid_bounded_complex_mean_probability_le {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (y : α → ℂ)
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (hy : ∀ a, ‖y a‖ ≤ B)
    {L : ℕ} (hL : 0 < L) :
    (Measure.pi (fun _ : Fin L => μ)).real
      {ω | r < ‖(L : ℝ)⁻¹ • (∑ i, y (ω i)) - ∫ a, y a ∂μ‖} ≤
      4 * Real.exp (-((L : ℝ) * r ^ 2 / (8 * B ^ 2))) := by
  let η := Measure.pi (fun _ : Fin L => μ)
  letI : IsProbabilityMeasure η := by dsimp [η]; infer_instance
  let D := fun ω : Fin L → α => (L : ℝ)⁻¹ • (∑ i, y (ω i)) - ∫ a, y a ∂μ
  have hre := iid_bounded_real_mean_abs_probability_le μ (fun a => (y a).re)
    hB (by positivity : 0 < r / 2)
    (fun a => (Complex.abs_re_le_norm _).trans (hy a)) hL
  have him := iid_bounded_real_mean_abs_probability_le μ (fun a => (y a).im)
    hB (by positivity : 0 < r / 2)
    (fun a => (Complex.abs_im_le_norm _).trans (hy a)) hL
  have heqRe (ω : Fin L → α) :
      (L : ℝ)⁻¹ * ∑ i, (y (ω i)).re - ∫ a, (y a).re ∂μ = (D ω).re := by
    dsimp [D]
    have h := Complex.reCLM.integral_comp_comm (Integrable.of_finite (f := y) (μ := μ))
    simp only [Complex.reCLM_apply] at h
    rw [h]
    simp
  have heqIm (ω : Fin L → α) :
      (L : ℝ)⁻¹ * ∑ i, (y (ω i)).im - ∫ a, (y a).im ∂μ = (D ω).im := by
    dsimp [D]
    have h := Complex.imCLM.integral_comp_comm (Integrable.of_finite (f := y) (μ := μ))
    simp only [Complex.imCLM_apply] at h
    rw [h]
    simp
  simp_rw [heqRe] at hre
  simp_rw [heqIm] at him
  have hmono : η.real {ω | r < ‖D ω‖} ≤
      η.real ({ω | r / 2 < |(D ω).re|} ∪ {ω | r / 2 < |(D ω).im|}) := by
    refine measureReal_mono ?_ (measure_ne_top η _)
    intro ω hω
    by_contra hbad
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hbad
    have hnorm := Complex.norm_le_abs_re_add_abs_im (D ω)
    simp only [Set.mem_setOf_eq] at hω
    linarith
  have hexp : -((L : ℝ) * (r / 2) ^ 2 / (2 * B ^ 2)) =
      -((L : ℝ) * r ^ 2 / (8 * B ^ 2)) := by
    field_simp
    ring
  rw [hexp] at hre him
  exact hmono.trans ((measureReal_union_le _ _).trans (by linarith))

/-- A finite probability law has at least one outcome no larger than its
expectation. This selection step does not discard low-probability atoms. -/
theorem finite_probability_exists_le_integral {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) :
    ∃ a, f a ≤ ∫ b, f b ∂μ := by
  obtain ⟨a, ha⟩ := (Set.range_nonempty f).csInf_mem (Set.finite_range f)
  have hmin : ∀ b, f a ≤ f b := by
    intro b
    rw [ha]
    exact csInf_le (Set.finite_range f).bddBelow ⟨b, rfl⟩
  have h := integral_mono (integrable_const (f a))
    (Integrable.of_finite (f := f) (μ := μ)) hmin
  refine ⟨a, ?_⟩
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- Empirical atoms approximate every tested coordinate except on a small
exceptional set. The number of tested rows appears only in the permitted
exceptional count, not in the number of atoms needed. -/
theorem exists_iid_complex_weak_approximation
    {α κ : Type*} [Fintype α] [Nonempty α] [Fintype κ]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (y : κ → α → ℂ)
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (hy : ∀ i a, ‖y i a‖ ≤ B)
    {L : ℕ} (hL : 0 < L) :
    ∃ ω : Fin L → α,
      ((Finset.univ.filter fun i =>
        r < ‖(L : ℝ)⁻¹ • (∑ l, y i (ω l)) - ∫ a, y i a ∂μ‖).card : ℝ) ≤
        4 * (Fintype.card κ : ℝ) * Real.exp (-((L : ℝ) * r ^ 2 / (8 * B ^ 2))) := by
  classical
  let η := Measure.pi (fun _ : Fin L => μ)
  letI : IsProbabilityMeasure η := by dsimp [η]; infer_instance
  let P := fun i (ω : Fin L → α) =>
    r < ‖(L : ℝ)⁻¹ • (∑ l, y i (ω l)) - ∫ a, y i a ∂μ‖
  let count := fun ω : Fin L → α => ((Finset.univ.filter fun i => P i ω).card : ℝ)
  have hcount (ω : Fin L → α) : count ω = ∑ i, if P i ω then (1 : ℝ) else 0 := by
    simp [count, Finset.sum_boole]
  have hindicator (i : κ) : (∫ ω : Fin L → α, (if P i ω then (1 : ℝ) else 0) ∂η) =
      η.real {ω | P i ω} := by
    simpa [Set.indicator, smul_eq_mul] using
      integral_indicator_const (μ := η) (1 : ℝ)
        ((Set.to_countable {ω | P i ω}).measurableSet)
  have hmean : (∫ ω, count ω ∂η) ≤
      4 * (Fintype.card κ : ℝ) * Real.exp (-((L : ℝ) * r ^ 2 / (8 * B ^ 2))) := by
    calc
      _ = ∫ ω : Fin L → α, ∑ i, if P i ω then (1 : ℝ) else 0 ∂η := by
        apply integral_congr_ae
        exact ae_of_all η hcount
      _ = ∑ i, ∫ ω : Fin L → α, (if P i ω then (1 : ℝ) else 0) ∂η :=
        integral_finsetSum _ (fun _ _ => Integrable.of_finite)
      _ = ∑ i, η.real {ω | P i ω} := Finset.sum_congr rfl (fun i _ => hindicator i)
      _ ≤ ∑ _i : κ, 4 * Real.exp (-((L : ℝ) * r ^ 2 / (8 * B ^ 2))) :=
        Finset.sum_le_sum fun i _ => iid_bounded_complex_mean_probability_le μ (y i) hB hr
          (hy i) hL
      _ = _ := by simp; ring
  obtain ⟨ω, hω⟩ := finite_probability_exists_le_integral η count
  exact ⟨ω, hω.trans hmean⟩

end LeanNumDetect.BoundedRieszConcentration
