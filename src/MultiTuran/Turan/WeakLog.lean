import MultiTuran.Turan.LogPotential

/-! # Weak distribution bounds control logarithmic excess

This is the layer-cake step in geometric quotient control (Section 4 of
arXiv:2606.24823). All measures and integrals below are actual measures and
integrals, and the threshold restriction prevents `log 0 = 0` from introducing
spurious positive level sets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal

namespace LeanNumDetect.MultiTuran
noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- The nonnegative excess of a logarithm over a fixed threshold. -/
def logExcess (T : ℝ) (w : X → ℝ) (x : X) : ℝ := max 0 (Real.log (w x)-T)

/-- The positive part of a logarithm, with the finite value at zero irrelevant
when applied to almost-everywhere nonzero analytic functions. -/
def positiveLog (w : X → ℝ) (x : X) : ℝ := max 0 (Real.log (w x))

theorem logExcess_nonneg (T : ℝ) (w : X → ℝ) (x : X) : 0 ≤ logExcess T w x :=
  le_max_left _ _

theorem measurable_logExcess {w : X → ℝ} (hw : Measurable w) (T : ℝ) :
    Measurable (logExcess T w) := measurable_const.max (hw.log.sub measurable_const)

theorem measurable_positiveLog {w : X → ℝ} (hw : Measurable w) :
    Measurable (positiveLog w) := measurable_const.max hw.log

/-- A weak `K/u` distribution estimate gives an exponentially decaying level
set estimate for positive logarithmic excess. -/
theorem logExcess_tail_le (μ : Measure X) {w : X → ℝ}
    (hwnn : ∀ x, 0 ≤ w x) {K T t : ℝ} (hT : 0 ≤ T) (ht : 0 < t)
    (htail : ∀ u > 0, μ {x | u < w x} ≤ ENNReal.ofReal (K/u)) :
    μ {x | t < logExcess T w x} ≤ ENNReal.ofReal (K*Real.exp (-T)*Real.exp (-t)) := by
  have hsub : {x | t < logExcess T w x} ⊆ {x | Real.exp (T+t) < w x} := by
    intro x hx
    have hlog : t < Real.log (w x)-T :=
      (lt_max_iff.mp hx).resolve_left (not_lt_of_ge ht.le)
    have hzero : w x ≠ 0 := by
      intro hz
      rw [hz,Real.log_zero] at hlog
      linarith
    have hp : 0 < w x := lt_of_le_of_ne (hwnn x) (Ne.symm hzero)
    have he := Real.exp_lt_exp.mpr (show T+t < Real.log (w x) by linarith)
    rwa [Real.exp_log hp] at he
  calc
    _ ≤ μ {x | Real.exp (T+t) < w x} := measure_mono hsub
    _ ≤ ENNReal.ofReal (K/Real.exp (T+t)) := htail _ (Real.exp_pos _)
    _ = _ := by
      congr 1
      simp only [Real.exp_add, Real.exp_neg, div_eq_mul_inv, mul_inv_rev]
      ring

/-- The literal layer-cake integral of a logarithmic excess. -/
theorem lintegral_logExcess_le (μ : Measure X) {w : X → ℝ}
    (hw : Measurable w) (hwnn : ∀ x, 0 ≤ w x) {K T : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T)
    (htail : ∀ u > 0, μ {x | u < w x} ≤ ENNReal.ofReal (K/u)) :
    (∫⁻ x, ENNReal.ofReal (logExcess T w x) ∂μ) ≤
      ENNReal.ofReal (K*Real.exp (-T)) := by
  rw [lintegral_eq_lintegral_meas_lt μ
    (Filter.Eventually.of_forall (logExcess_nonneg T w))
    (measurable_logExcess hw T).aemeasurable]
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (K*Real.exp (-T)*Real.exp (-t)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact logExcess_tail_le μ hwnn hT ht htail
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((integrableOn_exp_neg_Ioi 0).const_mul (K*Real.exp (-T)))
        (Filter.Eventually.of_forall (fun t => by positivity))]
      rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

/-- On a finite measure space of mass `α`, the exact logarithmic weak-type
bound is `α(log(K/α)+1)` once `K≥α>0`. -/
theorem lintegral_positiveLog_le_of_weak (μ : Measure X) [IsFiniteMeasure μ]
    {w : X → ℝ} (hw : Measurable w) (hwnn : ∀ x, 0 ≤ w x) {K : ℝ}
    (hα : 0 < (μ univ).toReal) (hαK : (μ univ).toReal ≤ K)
    (htail : ∀ u > 0, μ {x | u < w x} ≤ ENNReal.ofReal (K/u)) :
    (∫⁻ x, ENNReal.ofReal (positiveLog w x) ∂μ) ≤
      ENNReal.ofReal ((μ univ).toReal*(Real.log (K/(μ univ).toReal)+1)) := by
  let α := (μ univ).toReal
  let T := Real.log (K/α)
  have hα0 : 0 < α := hα
  have hK : 0 < K := hα.trans_le hαK
  have hT : 0 ≤ T := Real.log_nonneg ((le_div_iff₀ hα0).2 (by simpa using hαK))
  have hμ : μ univ = ENNReal.ofReal α := (ENNReal.ofReal_toReal (measure_ne_top μ univ)).symm
  have hc : K*Real.exp (-T) = α := by
    dsimp [T]
    rw [Real.exp_neg, Real.exp_log (div_pos hK hα0)]
    field_simp
  have he := lintegral_logExcess_le μ hw hwnn hK.le hT htail
  rw [hc] at he
  have hpoint (x : X) : positiveLog w x ≤ T+logExcess T w x := by
    apply max_le
    · exact add_nonneg hT (logExcess_nonneg T w x)
    · have h := le_max_right 0 (Real.log (w x)-T)
      change Real.log (w x) ≤ T+max 0 (Real.log (w x)-T)
      linarith
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal T+ENNReal.ofReal (logExcess T w x) ∂μ := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (positiveLog w x) ≤
        ENNReal.ofReal T+ENNReal.ofReal (logExcess T w x)
      rw [← ENNReal.ofReal_add hT (logExcess_nonneg T w x)]
      exact ENNReal.ofReal_le_ofReal (hpoint x)
    _ = ENNReal.ofReal T*μ univ + ∫⁻ x, ENNReal.ofReal (logExcess T w x) ∂μ := by
      rw [lintegral_add_left measurable_const]
      simp
    _ ≤ ENNReal.ofReal T*ENNReal.ofReal α+ENNReal.ofReal α := by
      rw [hμ]
      exact add_le_add le_rfl he
    _ = _ := by
      rw [← ENNReal.ofReal_mul hT,
        ← ENNReal.ofReal_add (mul_nonneg hT hα0.le) hα0.le]
      congr 1
      dsimp [T,α]
      ring

/-- Weak control also proves the needed integrability of the positive log. -/
theorem integrable_positiveLog_of_weak (μ : Measure X) [IsFiniteMeasure μ]
    {w : X → ℝ} (hw : Measurable w) (hwnn : ∀ x, 0 ≤ w x) {K : ℝ}
    (hα : 0 < (μ univ).toReal) (hαK : (μ univ).toReal ≤ K)
    (htail : ∀ u > 0, μ {x | u < w x} ≤ ENNReal.ofReal (K/u)) :
    Integrable (positiveLog w) μ := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_positiveLog hw).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => le_max_left 0 (Real.log (w x))))).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (lintegral_positiveLog_le_of_weak μ hw hwnn hα hαK htail)

/-- Bochner-integral version of the exact positive-log bound. -/
theorem integral_positiveLog_le_of_weak (μ : Measure X) [IsFiniteMeasure μ]
    {w : X → ℝ} (hw : Measurable w) (hwnn : ∀ x, 0 ≤ w x) {K : ℝ}
    (hα : 0 < (μ univ).toReal) (hαK : (μ univ).toReal ≤ K)
    (htail : ∀ u > 0, μ {x | u < w x} ≤ ENNReal.ofReal (K/u)) :
    (∫ x, positiveLog w x ∂μ) ≤
      (μ univ).toReal*(Real.log (K/(μ univ).toReal)+1) := by
  have hT : 0 ≤ Real.log (K/(μ univ).toReal) :=
    Real.log_nonneg ((le_div_iff₀ hα).2 (by simpa using hαK))
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hα.le (by linarith :
    0 ≤ Real.log (K/(μ univ).toReal)+1))).mp
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_positiveLog_of_weak μ hw hwnn hα hαK htail)
    (Filter.Eventually.of_forall (fun x => le_max_left 0 (Real.log (w x))))]
  exact lintegral_positiveLog_le_of_weak μ hw hwnn hα hαK htail

end
end LeanNumDetect.MultiTuran
