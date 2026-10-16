import MultiTuran.Turan.GeometricMean

/-! Elementary zero, one-term and upper-bound cases for geometric means. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ENNReal

namespace LeanNumDetect.MultiTuran
noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Nonnegative a.e. bounds, including the zero bound, dominate the actual
geometric mean whenever nonzero functions have the stated log regularity. -/
theorem measureGeometricMean_le_of_ae_bound (μ : Measure X) [IsFiniteMeasure μ]
    {P : X → ℂ} (hreg : P ≠ 0 → LogRegular μ P)
    (hα : 0 < (μ univ).toReal) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂μ, ‖P x‖ ≤ M) : measureGeometricMean μ P ≤ M := by
  by_contra hnot
  have hgap : M < measureGeometricMean μ P := lt_of_not_ge hnot
  let ε := (measureGeometricMean μ P-M)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hu := measureGeometricMean_le_of_ae_bound_pos μ hreg hα
    (show 0 < M+ε by linarith)
    (hbound.mono (fun x hx => hx.trans (by linarith : M ≤ M+ε)))
  dsimp [ε] at hu
  linarith

/-- Actual pointwise bounds on a finite measurable set dominate its geometric
mean, with the zero-function and zero-bound cases included. -/
theorem geometricMean_le_of_bound {E : Set ℝ} (hE : MeasurableSet E)
    (hEfin : volume E < ∞) (hEpos : 0 < volume E) {P : ℝ → ℂ}
    (hreg : P ≠ 0 → LogRegular (volume.restrict E) P) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x ∈ E, ‖P x‖ ≤ M) : geometricMean E P ≤ M := by
  letI : IsFiniteMeasure (volume.restrict E) := ⟨by simpa using hEfin⟩
  have hα : 0 < ((volume.restrict E) univ).toReal := by
    simpa using ENNReal.toReal_pos (ne_of_gt hEpos) hEfin.ne
  exact measureGeometricMean_le_of_ae_bound _ hreg hα hM
    (ae_restrict_of_forall_mem hE hbound)

/-- A single imaginary exponential has constant modulus, including a zero
coefficient. -/
theorem norm_exponentialSum_one (frequency : Fin 1 → ℝ) (c : Fin 1 → ℂ) (t : ℝ) :
    ‖ExponentialSumEstimates.exponentialSum frequency c t‖ = ‖c 0‖ := by
  simp only [ExponentialSumEstimates.exponentialSum,Fin.sum_univ_one,norm_mul,
    Complex.norm_exp_I_mul_ofReal,mul_one]

/-- The one-term base case is an equality for the actual geometric mean. -/
theorem measureGeometricMean_exponentialSum_one (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hα : 0 < (μ univ).toReal) (frequency : Fin 1 → ℝ) (c : Fin 1 → ℂ) :
    measureGeometricMean μ (ExponentialSumEstimates.exponentialSum frequency c) = ‖c 0‖ := by
  by_cases hc : c 0 = 0
  · have hz : ExponentialSumEstimates.exponentialSum frequency c = 0 := by
      funext t
      simp [ExponentialSumEstimates.exponentialSum,hc]
    simp [hz,hc]
  have hzero : ExponentialSumEstimates.exponentialSum frequency c ≠ 0 := by
    intro hz
    have h := congrFun hz 0
    apply hc
    simpa [ExponentialSumEstimates.exponentialSum] using h
  rw [measureGeometricMean,if_neg hzero]
  simp_rw [norm_exponentialSum_one]
  rw [integral_const,smul_eq_mul,measureReal_def,mul_div_cancel_left₀ _ (ne_of_gt hα),
    Real.exp_log (norm_pos_iff.mpr hc)]

/-- The actual set-integral one-term equality. -/
theorem geometricMean_exponentialSum_one {E : Set ℝ} (hEfin : volume E < ∞)
    (hEpos : 0 < volume E) (frequency : Fin 1 → ℝ) (c : Fin 1 → ℂ) :
    geometricMean E (ExponentialSumEstimates.exponentialSum frequency c) = ‖c 0‖ := by
  letI : IsFiniteMeasure (volume.restrict E) := ⟨by simpa using hEfin⟩
  have hα : 0 < ((volume.restrict E) univ).toReal := by
    simpa using ENNReal.toReal_pos (ne_of_gt hEpos) hEfin.ne
  exact measureGeometricMean_exponentialSum_one _ hα frequency c

end
end LeanNumDetect.MultiTuran
