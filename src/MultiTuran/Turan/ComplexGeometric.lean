import MultiTuran.Turan.DiskMajorant

/-! Actual logarithmic regularity and geometric-mean Remez estimates for
bounded complex spectra. Every root, potential and logarithmic integral in
this argument is obtained from the given exponential sum. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology ENNReal
open Set Metric MeasureTheory Filter

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- A generous universal numerical bound for the actual disk and root losses. -/
theorem turanRootError_add_rootCount_le (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (N : ℕ)
    (hN : (N : ℝ) ≤ 7*turanDiskGrowthBudget n σ) :
    turanRootError n σ N+2*(N : ℝ) ≤ 10000*((n : ℝ)+σ) := by
  have hlog16 : Real.log (16*Real.exp 1) ≤ 16 := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<16)
    linarith
  have hlog8 : Real.log (8*Real.exp 1) ≤ 8 := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<8)
    linarith
  have hlogR : Real.log (17/2 : ℝ) ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<17/2)
    linarith
  have hdegree : (((n-1 : ℕ) : ℝ)) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hbudget : turanDiskGrowthBudget n σ ≤ 4*σ+16*(n : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hlog16 (Nat.cast_nonneg (n-1))
    unfold turanDiskGrowthBudget
    nlinarith
  have hm8 := mul_le_mul_of_nonneg_left hlog8 (Nat.cast_nonneg (n-1))
  have hmR := mul_le_mul_of_nonneg_left hlogR (Nat.cast_nonneg N)
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold turanRootError
  nlinarith

private theorem finite_volume_of_unit_subset {E : Set ℝ}
    (hEsub : E ⊆ Icc (-1/2 : ℝ) (1/2)) : volume E < ∞ :=
  lt_of_le_of_lt (measure_mono hEsub) (by simp)

private theorem real_volume_le_one_of_unit_subset {E : Set ℝ}
    (hEsub : E ⊆ Icc (-1/2 : ℝ) (1/2)) : (volume E).toReal ≤ 1 := by
  have h := ENNReal.toReal_mono (by simp : volume (Icc (-1/2 : ℝ) (1/2)) ≠ ∞)
    (measure_mono hEsub)
  norm_num at h
  exact h

/-- A nonzero actual exponential sum has an integrable logarithm and is
nonzero almost everywhere on every measured subset of the unit interval. -/
theorem complexExponentialSum_logRegular_on_unit_subset {n : ℕ} (hn : 0 < n)
    (exponent c : Fin n → ℂ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hexponent : ∀ j, ‖exponent j‖ ≤ σ)
    (hzero : (fun x : ℝ => complexExponentialSum exponent c (x : ℂ)) ≠ 0)
    (E : Set ℝ) (hE : MeasurableSet E) (hEsub : E ⊆ Icc (-1/2 : ℝ) (1/2)) :
    LogRegular (volume.restrict E) (fun x : ℝ => complexExponentialSum exponent c (x : ℂ)) := by
  obtain ⟨N,roots,M,hM,hN,hupper,hlower⟩ :=
    complexExponentialSum_exists_logMajorant hn exponent c hσ hexponent hzero
  let P : ℝ → ℂ := fun x => complexExponentialSum exponent c (x : ℂ)
  have hP : Measurable P :=
    (differentiable_complexExponentialSum exponent c).continuous.measurable.comp
      Complex.continuous_ofReal.measurable
  have hEfin := finite_volume_of_unit_subset hEsub
  letI : IsFiniteMeasure (volume.restrict E) := ⟨by simpa using hEfin⟩
  have hroot : ∀ᵐ (x : ℝ) ∂volume.restrict E, ∀ j, (x : ℂ) ≠ roots j :=
    ae_restrict_of_ae (ae_ne_root_centres roots)
  have hPae : ∀ᵐ x ∂volume.restrict E, P x ≠ 0 := by
    filter_upwards [ae_restrict_mem hE,hroot] with x hx hr
    exact (hlower x (hEsub hx) hr).1
  have hup : ∀ᵐ x ∂volume.restrict E, ‖P x‖ ≤ M :=
    ae_restrict_of_forall_mem hE (fun x hx => hupper x (hEsub hx))
  have hlo : ∀ᵐ x ∂volume.restrict E,
      Real.log M-turanRootError n σ N-effectiveLogPotential (n-1) roots x ≤ Real.log ‖P x‖ := by
    filter_upwards [ae_restrict_mem hE,hroot] with x hx hr
    exact (hlower x (hEsub hx) hr).2
  exact logRegular_of_logMajorant (volume.restrict E) hP hPae hM
    (integrable_effectiveLogPotential (n-1) roots).integrableOn hup hlo

/-- The actual geometric-mean Remez bound on the centred unit interval for
any bounded complex spectrum. The zero function and repeated exponents are
included. No Turan or logarithmic-regularity premise is assumed. -/
theorem complexExponentialSum_geometric_bound_unit {n : ℕ} (hn : 0 < n)
    (exponent c : Fin n → ℂ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hexponent : ∀ j, ‖exponent j‖ ≤ σ)
    (E : Set ℝ) (hE : MeasurableSet E) (hEsub : E ⊆ Icc (-1/2 : ℝ) (1/2))
    (hEpos : 0 < volume E) (t : ℝ) (ht : t ∈ Icc (-1/2 : ℝ) (1/2)) :
    ‖complexExponentialSum exponent c (t : ℂ)‖ ≤
      Real.exp (10000*((n : ℝ)+σ))*(1/(volume E).toReal)^(n-1)*
        geometricMean E (fun x : ℝ => complexExponentialSum exponent c (x : ℂ)) := by
  let P : ℝ → ℂ := fun x => complexExponentialSum exponent c (x : ℂ)
  by_cases hzero : P=0
  · have htzero : complexExponentialSum exponent c (t : ℂ)=0 := congrFun hzero t
    rw [htzero,norm_zero,show (fun x : ℝ => complexExponentialSum exponent c (x : ℂ))=0 from hzero,
      geometricMean_zero,mul_zero]
  obtain ⟨N,roots,M,hM,hN,hupper,hlower⟩ :=
    complexExponentialSum_exists_logMajorant hn exponent c hσ hexponent hzero
  have hP : Measurable P :=
    (differentiable_complexExponentialSum exponent c).continuous.measurable.comp
      Complex.continuous_ofReal.measurable
  have hEfin := finite_volume_of_unit_subset hEsub
  have hα : 0 < (volume E).toReal := ENNReal.toReal_pos (ne_of_gt hEpos) hEfin.ne
  have hα1 := real_volume_le_one_of_unit_subset hEsub
  have hroot : ∀ᵐ (x : ℝ) ∂volume.restrict E, ∀ j, (x : ℂ) ≠ roots j :=
    ae_restrict_of_ae (ae_ne_root_centres roots)
  have hPae : ∀ᵐ x ∂volume.restrict E, P x ≠ 0 := by
    filter_upwards [ae_restrict_mem hE,hroot] with x hx hr
    exact (hlower x (hEsub hx) hr).1
  have hup : ∀ᵐ x ∂volume.restrict E, ‖P x‖ ≤ M :=
    ae_restrict_of_forall_mem hE (fun x hx => hupper x (hEsub hx))
  have hlo : ∀ᵐ x ∂volume.restrict E,
      Real.log M-turanRootError n σ N-effectiveLogPotential (n-1) roots x ≤ Real.log ‖P x‖ := by
    filter_upwards [ae_restrict_mem hE,hroot] with x hx hr
    exact (hlower x (hEsub hx) hr).2
  have hint := integral_effectiveLogPotential_le (n-1) roots E hα hα1
  have hgeom := le_geometricMean_of_logMajorant hEfin hEpos hP hzero hPae hM
    (integrable_effectiveLogPotential (n-1) roots).integrableOn hup hlo hint
  have hnum := turanRootError_add_rootCount_le n hσ N hN
  calc
    _ ≤ M := hupper t ht
    _ ≤ Real.exp (turanRootError n σ N+2*(N : ℝ))*(1/(volume E).toReal)^(n-1)*
        geometricMean E P := hgeom
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hnum) (by positivity))
      (geometricMean_nonneg _ _)

end
end LeanNumDetect.MultiTuran
