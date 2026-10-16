import MultiTuran.Turan.WeakLog
import MultiTuran.Turan.Pruning

/-! # Zero-aware geometric means and geometric quotient control

The zero function is assigned geometric mean zero. For a nonzero exponential
sum the ordinary real logarithm is used only together with explicit
almost-everywhere nonvanishing and log-integrability hypotheses; changing
isolated zero values then does not affect the integral.

The weak-distribution-to-geometric-mean step is Section 4 of
arXiv:2606.24823, with its constant displayed as `exp(1)*K`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal

namespace LeanNumDetect.MultiTuran
noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- A literal logarithmic integral, with the identically zero function handled
separately rather than evaluating its real logarithm. -/
def measureGeometricMean (μ : Measure X) (f : X → ℂ) : ℝ := by
  classical
  exact if f = 0 then 0 else Real.exp ((∫ x, Real.log ‖f x‖ ∂μ)/(μ univ).toReal)

/-- The actual geometric mean on a measurable real set. -/
def geometricMean (E : Set ℝ) (f : ℝ → ℂ) : ℝ :=
  measureGeometricMean (volume.restrict E) f

/-- The regularity facts needed to use ordinary real-valued logarithms for a
nonzero function. These are explicit conditions, not an analytic assertion. -/
def LogRegular (μ : Measure X) (f : X → ℂ) : Prop :=
  Integrable (fun x => Real.log ‖f x‖) μ ∧ ∀ᵐ x ∂μ, f x ≠ 0

@[simp] theorem measureGeometricMean_zero (μ : Measure X) :
    measureGeometricMean μ (0 : X → ℂ) = 0 := by simp [measureGeometricMean]

@[simp] theorem geometricMean_zero (E : Set ℝ) : geometricMean E 0 = 0 := by
  simp [geometricMean]

theorem measureGeometricMean_nonneg (μ : Measure X) (f : X → ℂ) :
    0 ≤ measureGeometricMean μ f := by
  unfold measureGeometricMean
  split_ifs <;> positivity

theorem geometricMean_nonneg (E : Set ℝ) (f : ℝ → ℂ) : 0 ≤ geometricMean E f :=
  measureGeometricMean_nonneg _ _

/-- A weak quotient distribution on the original measure space controls the
geometric mean without discarding any part of that space. -/
theorem measureGeometricMean_le_of_weak_quotient (μ : Measure X) [IsFiniteMeasure μ]
    {P Q : X → ℂ} (hP : Measurable P) (hQ : Measurable Q) (hPzero : P ≠ 0)
    (hPreg : LogRegular μ P) (hQreg : Q ≠ 0 → LogRegular μ Q) {K : ℝ}
    (hα : 0 < (μ univ).toReal) (hαK : (μ univ).toReal ≤ K)
    (htail : ∀ u > 0, μ {x | u < ‖Q x / P x‖} ≤ ENNReal.ofReal (K/u)) :
    measureGeometricMean μ Q ≤
      (Real.exp 1*K/(μ univ).toReal)*measureGeometricMean μ P := by
  have hK : 0 < K := hα.trans_le hαK
  by_cases hQzero : Q = 0
  · rw [hQzero,measureGeometricMean_zero]
    exact mul_nonneg (by positivity) (measureGeometricMean_nonneg μ P)
  obtain ⟨hQint,hQae⟩ := hQreg hQzero
  let w : X → ℝ := fun x => ‖Q x/P x‖
  have hw : Measurable w := (hQ.div hP).norm
  have hwnn : ∀ x, 0 ≤ w x := fun x => norm_nonneg _
  have hwint := integrable_positiveLog_of_weak μ hw hwnn hα hαK htail
  have hwbound := integral_positiveLog_le_of_weak μ hw hwnn hα hαK htail
  have hpoint : (fun x => Real.log ‖Q x‖-Real.log ‖P x‖) ≤ᵐ[μ] positiveLog w := by
    filter_upwards [hPreg.2,hQae] with x hxP hxQ
    have he : Real.log (w x) = Real.log ‖Q x‖-Real.log ‖P x‖ := by
      dsimp [w]
      rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hxQ) (norm_ne_zero_iff.mpr hxP)]
    rw [← he]
    exact le_max_right _ _
  have hi := (integral_mono_ae (hQint.sub hPreg.1) hwint hpoint).trans hwbound
  change (∫ x, Real.log ‖Q x‖-Real.log ‖P x‖ ∂μ) ≤
    (μ univ).toReal*(Real.log (K/(μ univ).toReal)+1) at hi
  rw [integral_sub hQint hPreg.1] at hi
  have hdiv := div_le_div_of_nonneg_right hi hα.le
  rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hα)] at hdiv
  have hlogs : (∫ x, Real.log ‖Q x‖ ∂μ)/(μ univ).toReal ≤
      Real.log (K/(μ univ).toReal)+1+
        (∫ x, Real.log ‖P x‖ ∂μ)/(μ univ).toReal := by linarith
  calc
    _ = Real.exp ((∫ x, Real.log ‖Q x‖ ∂μ)/(μ univ).toReal) := by
      rw [measureGeometricMean, if_neg hQzero]
    _ ≤ Real.exp (Real.log (K/(μ univ).toReal)+1+
        (∫ x, Real.log ‖P x‖ ∂μ)/(μ univ).toReal) := Real.exp_le_exp.mpr hlogs
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hK hα),
        measureGeometricMean, if_neg hPzero]
      ring

/-- Set-integral version with the exact excursion set occurring in the weak
pruning estimate. The identically zero `Q` branch is included. -/
theorem geometricMean_le_of_weak_quotient {E : Set ℝ} (hE : MeasurableSet E)
    (hEfin : volume E < ∞) (hEpos : 0 < volume E) {P Q : ℝ → ℂ}
    (hP : Measurable P) (hQ : Measurable Q) (hPzero : P ≠ 0)
    (hPreg : LogRegular (volume.restrict E) P)
    (hQreg : Q ≠ 0 → LogRegular (volume.restrict E) Q) {K : ℝ}
    (hαK : (volume E).toReal ≤ K)
    (htail : ∀ u > 0, volume {t | t ∈ E ∧ P t ≠ 0 ∧ u*‖P t‖ < ‖Q t‖} ≤
      ENNReal.ofReal (K/u)) :
    geometricMean E Q ≤ (Real.exp 1*K/(volume E).toReal)*geometricMean E P := by
  let μ : Measure ℝ := volume.restrict E
  letI : IsFiniteMeasure μ := ⟨by simpa [μ] using hEfin⟩
  have hα : 0 < (μ univ).toReal := by
    simpa [μ] using ENNReal.toReal_pos (ne_of_gt hEpos) hEfin.ne
  have hαK' : (μ univ).toReal ≤ K := by simpa [μ] using hαK
  have hquot : ∀ u > 0, μ {t | u < ‖Q t/P t‖} ≤ ENNReal.ofReal (K/u) := by
    intro u hu
    have hm : MeasurableSet {t : ℝ | u < ‖Q t/P t‖} :=
      measurableSet_lt measurable_const (hQ.div hP).norm
    rw [show μ = volume.restrict E from rfl, Measure.restrict_apply hm]
    apply (measure_mono ?_).trans (htail u hu)
    intro t ht
    have hlt : u < ‖Q t/P t‖ := ht.1
    have hp : P t ≠ 0 := by
      intro hz
      rw [hz,div_zero,norm_zero] at hlt
      exact (not_lt_of_ge hu.le) hlt
    refine ⟨ht.2,hp,?_⟩
    exact (lt_div_iff₀ (norm_pos_iff.mpr hp)).mp (by simpa only [norm_div] using hlt)
  have h := measureGeometricMean_le_of_weak_quotient μ hP hQ hPzero hPreg hQreg
    hα hαK' hquot
  simpa only [μ, Measure.restrict_apply_univ, geometricMean] using h

/-- A nonnegative almost-everywhere bound controls the geometric mean. The
positive-bound version is enough to recover the zero-bound case by a limit. -/
theorem measureGeometricMean_le_of_ae_bound_pos (μ : Measure X) [IsFiniteMeasure μ]
    {P : X → ℂ} (hreg : P ≠ 0 → LogRegular μ P)
    (hα : 0 < (μ univ).toReal) {M : ℝ} (hM : 0 < M)
    (hbound : ∀ᵐ x ∂μ, ‖P x‖ ≤ M) : measureGeometricMean μ P ≤ M := by
  by_cases hzero : P = 0
  · simp only [hzero,measureGeometricMean_zero]
    exact hM.le
  have hlog : (fun x => Real.log ‖P x‖) ≤ᵐ[μ] (fun _ => Real.log M) := by
    filter_upwards [(hreg hzero).2,hbound] with x hne hx
    exact Real.log_le_log (norm_pos_iff.mpr hne) hx
  have hi := integral_mono_ae (hreg hzero).1 (integrable_const (Real.log M)) hlog
  simp only [integral_const, smul_eq_mul, measureReal_def] at hi
  have hdiv := div_le_div_of_nonneg_right hi hα.le
  rw [mul_div_cancel_left₀ _ (ne_of_gt hα)] at hdiv
  unfold measureGeometricMean
  rw [if_neg hzero]
  exact (Real.exp_le_exp.mpr hdiv).trans_eq (Real.exp_log hM)

/-- The scalar arithmetic which closes one geometric-mean pruning step. -/
theorem geometric_pruning_step {a b p A G Ga Gb : ℝ} {m : ℕ}
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hp : p ≤ a+b)
    (ha : a ≤ A^m*Ga) (hb : b ≤ A^m*Gb)
    (hGa : Ga ≤ (A/2)*G) (hGb : Gb ≤ (A/2)*G) : p ≤ A^(m+1)*G := by
  have hpow : 0 ≤ A^m := pow_nonneg hA _
  calc
    p ≤ a+b := hp
    _ ≤ A^m*Ga+A^m*Gb := add_le_add ha hb
    _ ≤ A^m*((A/2)*G)+A^m*((A/2)*G) :=
      add_le_add (mul_le_mul_of_nonneg_left hGa hpow) (mul_le_mul_of_nonneg_left hGb hpow)
    _ = A^(m+1)*G := by rw [pow_succ]; ring

end
end LeanNumDetect.MultiTuran
