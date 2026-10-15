import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! The real-line logarithmic kernel used in geometric-mean Remez estimates.
The value assigned at a zero is finite, consistently with `Real.log 0 = 0`;
changing these isolated values does not affect any integral. -/

set_option autoImplicit false
open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The positive logarithmic potential of one complex centre on the real line. -/
def positiveLogPotential (r : ℝ) (z : ℂ) (x : ℝ) : ℝ :=
  max 0 (Real.log r - Real.log ‖(x : ℂ)-z‖)

theorem positiveLogPotential_nonneg (r : ℝ) (z : ℂ) (x : ℝ) :
    0 ≤ positiveLogPotential r z x := le_max_left _ _

theorem measurable_positiveLogPotential (r : ℝ) (z : ℂ) :
    Measurable (positiveLogPotential r z) := by
  unfold positiveLogPotential
  exact measurable_const.max (measurable_const.sub
    ((Complex.continuous_ofReal.sub continuous_const).norm.measurable.log))

/-- Each positive level set lies in a real interval of the indicated length. -/
theorem positiveLogPotential_tail_volume_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (z : ℂ) :
    volume {x : ℝ | t < positiveLogPotential r z x} ≤
      ENNReal.ofReal (2*r*Real.exp (-t)) := by
  have hsub : {x : ℝ | t < positiveLogPotential r z x} ⊆
      Ioo (z.re-r*Real.exp (-t)) (z.re+r*Real.exp (-t)) := by
    intro x hx
    have hlog : t < Real.log r-Real.log ‖(x : ℂ)-z‖ :=
      (lt_max_iff.mp hx).resolve_left (not_lt_of_ge ht.le)
    have hdist : ‖(x : ℂ)-z‖ < r*Real.exp (-t) := by
      by_cases hz : ‖(x : ℂ)-z‖ = 0
      · rw [hz]
        positivity
      · have hzpos : 0 < ‖(x : ℂ)-z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        have h := (Real.log_lt_iff_lt_exp hzpos).mp
          (show Real.log ‖(x : ℂ)-z‖ < Real.log r-t by linarith)
        rwa [show Real.log r-t=Real.log r+(-t) by ring,
          Real.exp_add, Real.exp_log hr] at h
    have hre : |x-z.re| ≤ ‖(x : ℂ)-z‖ := by
      simpa only [Complex.sub_re, Complex.ofReal_re] using Complex.abs_re_le_norm ((x : ℂ)-z)
    have hclose := abs_lt.mp (hre.trans_lt hdist)
    exact ⟨by linarith [hclose.1], by linarith [hclose.2]⟩
  calc
    _ ≤ volume (Ioo (z.re-r*Real.exp (-t)) (z.re+r*Real.exp (-t))) := measure_mono hsub
    _ = _ := by rw [Real.volume_Ioo]; congr 1; ring

/-- The complete real-line logarithmic mass is at most `2r`, independently
of the complex centre. The proof is the literal layer-cake integral. -/
theorem lintegral_positiveLogPotential_le {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (positiveLogPotential r z x)) ≤ ENNReal.ofReal (2*r) := by
  rw [lintegral_eq_lintegral_meas_lt volume
    (Filter.Eventually.of_forall (positiveLogPotential_nonneg r z))
    (measurable_positiveLogPotential r z).aemeasurable]
  calc
    _ ≤ ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (2*r*Real.exp (-t)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact positiveLogPotential_tail_volume_le hr ht z
    _ = ENNReal.ofReal (2*r) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((integrableOn_exp_neg_Ioi 0).const_mul (2*r))
        (Filter.Eventually.of_forall (fun t => by positivity))]
      rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

theorem integrable_positiveLogPotential {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Integrable (positiveLogPotential r z) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_positiveLogPotential r z).aestronglyMeasurable
    (Filter.Eventually.of_forall (positiveLogPotential_nonneg r z))).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_positiveLogPotential_le hr z)

/-- The same mass bound holds on every set, with actual Bochner integration. -/
theorem integral_positiveLogPotential_le {r : ℝ} (hr : 0 < r) (z : ℂ) (E : Set ℝ) :
    (∫ x in E, positiveLogPotential r z x) ≤ 2*r := by
  have hi := integrable_positiveLogPotential hr z
  have hb : (∫ x : ℝ, positiveLogPotential r z x) ≤ 2*r := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (positiveLogPotential_nonneg r z))]
    exact lintegral_positiveLogPotential_le hr z
  exact (setIntegral_le_integral hi
    (Filter.Eventually.of_forall (positiveLogPotential_nonneg r z))).trans hb

/-- Summing centres costs their actual number, with no loss depending on
how their disks overlap. -/
theorem integral_sum_positiveLogPotential_le {N : ℕ} (z : Fin N → ℂ)
    {r : ℝ} (hr : 0 < r) (E : Set ℝ) :
    (∫ x in E, ∑ j, positiveLogPotential r (z j) x) ≤ 2*N*r := by
  rw [integral_finsetSum _ (fun j _ => (integrable_positiveLogPotential hr (z j)).integrableOn)]
  calc
    _ ≤ ∑ _j : Fin N, 2*r := Finset.sum_le_sum (fun j _ => integral_positiveLogPotential_le hr (z j) E)
    _ = _ := by simp; ring

/-- A selected group of at most `d` centres is controlled by a constant
threshold and the full positive potential. No measurability of the choice is
needed for this pointwise assertion. -/
theorem selected_logPotential_le {N d : ℕ} (z : Fin N → ℂ) (s : Finset (Fin N))
    (hs : s.card ≤ d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (x : ℝ) :
    (∑ j ∈ s, max 0 (-Real.log ‖(x : ℂ)-z j‖)) ≤
      (d : ℝ)*(-Real.log r) + ∑ j, positiveLogPotential r (z j) x := by
  have hlog : 0 ≤ -Real.log r := neg_nonneg.mpr (Real.log_nonpos hr.le hr1)
  calc
    _ ≤ ∑ j ∈ s, (-Real.log r + positiveLogPotential r (z j) x) := by
      apply Finset.sum_le_sum
      intro j _
      apply max_le
      · exact add_nonneg hlog (positiveLogPotential_nonneg r (z j) x)
      · have h := le_max_right 0 (Real.log r-Real.log ‖(x : ℂ)-z j‖)
        dsimp [positiveLogPotential]
        linarith
    _ = (s.card : ℝ)*(-Real.log r) + ∑ j ∈ s, positiveLogPotential r (z j) x := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ (d : ℝ)*(-Real.log r) + ∑ j, positiveLogPotential r (z j) x := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hlog
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
          (fun j _ _ => positiveLogPotential_nonneg r (z j) x)

end
end LeanNumDetect.MultiTuran
