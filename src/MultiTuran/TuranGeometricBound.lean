import MultiTuran.TuranGeometricMean

/-! # From an actual logarithmic majorant to geometric-mean Remez bounds

An integrable lower logarithmic error and a finite upper bound prove the
required logarithmic integrability. Integration then produces the exact
`exp(K+B) * (1/α)^m` loss. No zero-count or analytic estimate is assumed
implicitly in these generic integration lemmas.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal

namespace LeanNumDetect.MultiTuran
noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- An integrable logarithmic lower error and a constant upper bound prove
actual logarithmic integrability and preserve a.e. nonvanishing explicitly. -/
theorem logRegular_of_logMajorant (μ : Measure X) [IsFiniteMeasure μ]
    {P : X → ℂ} (hP : Measurable P) (hPae : ∀ᵐ x ∂μ, P x ≠ 0)
    {M K : ℝ} (hM : 0 < M) {H : X → ℝ} (hH : Integrable H μ)
    (hupper : ∀ᵐ x ∂μ, ‖P x‖ ≤ M)
    (hlower : ∀ᵐ x ∂μ, Real.log M-K-H x ≤ Real.log ‖P x‖) :
    LogRegular μ P := by
  refine ⟨?_,hPae⟩
  have hupperlog : ∀ᵐ x ∂μ, Real.log ‖P x‖ ≤ Real.log M := by
    filter_upwards [hPae,hupper] with x hne hx
    exact Real.log_le_log (norm_pos_iff.mpr hne) hx
  have hdom : Integrable (fun x => |Real.log M|+|K|+|H x|) μ := by
    exact ((integrable_const _).add (integrable_const _)).add hH.abs
  apply hdom.mono' (hP.norm.log.aestronglyMeasurable)
  filter_upwards [hlower,hupperlog] with x hlo hhi
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log M), le_abs_self K, le_abs_self (H x)]
  · linarith [le_abs_self (Real.log M), abs_nonneg K, abs_nonneg (H x)]

/-- Integrating a logarithmic lower majorant yields the geometric-mean loss
with the exact exponent `m`. -/
theorem le_measureGeometricMean_of_logMajorant (μ : Measure X) [IsFiniteMeasure μ]
    {P : X → ℂ} (hP : Measurable P) (hPzero : P ≠ 0) (hPae : ∀ᵐ x ∂μ, P x ≠ 0)
    (hα : 0 < (μ univ).toReal) {M K B : ℝ} {m : ℕ} (hM : 0 < M)
    {H : X → ℝ} (hH : Integrable H μ)
    (hupper : ∀ᵐ x ∂μ, ‖P x‖ ≤ M)
    (hlower : ∀ᵐ x ∂μ, Real.log M-K-H x ≤ Real.log ‖P x‖)
    (hHint : (∫ x, H x ∂μ) ≤
      (μ univ).toReal*(B+(m : ℝ)*Real.log (1/(μ univ).toReal))) :
    M ≤ Real.exp (K+B)*(1/(μ univ).toReal)^m*measureGeometricMean μ P := by
  have hreg := logRegular_of_logMajorant μ hP hPae hM hH hupper hlower
  have hi := integral_mono_ae ((integrable_const (Real.log M-K)).sub hH) hreg.1 hlower
  change (∫ x, Real.log M-K-H x ∂μ) ≤ (∫ x, Real.log ‖P x‖ ∂μ) at hi
  rw [integral_sub (integrable_const (Real.log M-K)) hH,
    integral_const, smul_eq_mul, measureReal_def] at hi
  have hmean : Real.log M-K-B-(m : ℝ)*Real.log (1/(μ univ).toReal) ≤
      (∫ x, Real.log ‖P x‖ ∂μ)/(μ univ).toReal := by
    apply (le_div_iff₀ hα).2
    nlinarith only [hi,hHint]
  have hlogs : Real.log M ≤ K+B+(m : ℝ)*Real.log (1/(μ univ).toReal)+
      (∫ x, Real.log ‖P x‖ ∂μ)/(μ univ).toReal := by linarith
  calc
    M = Real.exp (Real.log M) := (Real.exp_log hM).symm
    _ ≤ Real.exp (K+B+(m : ℝ)*Real.log (1/(μ univ).toReal)+
        (∫ x, Real.log ‖P x‖ ∂μ)/(μ univ).toReal) := Real.exp_le_exp.mpr hlogs
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul,
        Real.exp_log (one_div_pos.mpr hα), measureGeometricMean, if_neg hPzero]

/-- The article's actual set-integral form, using the literal set measure. -/
theorem le_geometricMean_of_logMajorant {E : Set ℝ} (hEfin : volume E < ∞)
    (hEpos : 0 < volume E) {P : ℝ → ℂ} (hP : Measurable P) (hPzero : P ≠ 0)
    (hPae : ∀ᵐ x ∂volume.restrict E, P x ≠ 0)
    {M K B : ℝ} {m : ℕ} (hM : 0 < M) {H : ℝ → ℝ} (hH : IntegrableOn H E)
    (hupper : ∀ᵐ x ∂volume.restrict E, ‖P x‖ ≤ M)
    (hlower : ∀ᵐ x ∂volume.restrict E, Real.log M-K-H x ≤ Real.log ‖P x‖)
    (hHint : (∫ x in E, H x) ≤
      (volume E).toReal*(B+(m : ℝ)*Real.log (1/(volume E).toReal))) :
    M ≤ Real.exp (K+B)*(1/(volume E).toReal)^m*geometricMean E P := by
  letI : IsFiniteMeasure (volume.restrict E) := ⟨by simpa using hEfin⟩
  have hα : 0 < ((volume.restrict E) univ).toReal := by
    simpa using ENNReal.toReal_pos (ne_of_gt hEpos) hEfin.ne
  have hHint' : (∫ x, H x ∂volume.restrict E) ≤
      ((volume.restrict E) univ).toReal*(B+(m : ℝ)*Real.log (1/((volume.restrict E) univ).toReal)) := by
    simpa using hHint
  simpa only [Measure.restrict_apply_univ,geometricMean] using
    le_measureGeometricMean_of_logMajorant (volume.restrict E) hP hPzero hPae hα hM hH
      hupper hlower hHint'

end
end LeanNumDetect.MultiTuran
