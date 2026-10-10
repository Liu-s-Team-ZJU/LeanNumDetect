import General.MatrixAnalysis.FiniteFrameGram
import General.MatrixAnalysis.CappedRowLeverage
import General.MatrixAnalysis.CappedWeightIteration
import General.Probability.CappedWeightEntropy

/-! Capped finite-frame covariance updates and their row bounds. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.CappedWeightIteration

open FiniteMatrixSampling
noncomputable section

def frameMetricWeight {N d : ℕ} (f : Fin N → EuclideanSpace ℂ (Fin d))
    (R : ℝ) (G : Matrix (Fin d) (Fin d) ℂ) (k : Fin N) : ℝ :=
  cappedWeight R (quadratic G⁻¹ (f k))

def cappedGram {N d : ℕ} (f : Fin N → EuclideanSpace ℂ (Fin d))
    (R : ℝ) (G : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  mean (weightedPopulation (framePopulation f) (frameMetricWeight f R G))

theorem frameMetricWeight_bounds {N d : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin d)) {R : ℝ} (hR : 0 < R)
    {G : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosDef) (k : Fin N) :
    0 < frameMetricWeight f R G k ∧ frameMetricWeight f R G k ≤ 1 :=
  cappedWeight_pos_le_one hR (quadratic_nonneg hG.posSemidef.inv (f k))

theorem cappedGram_posDef {N d : ℕ} (hN : 0 < N)
    (f : Fin N → EuclideanSpace ℂ (Fin d)) {R : ℝ} (hR : 0 < R)
    {G : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosDef)
    (hfull : (mean (framePopulation f)).PosDef) : (cappedGram f R G).PosDef :=
  mean_weighted_posDef hN (framePopulation f) _ (framePopulation_posSemidef f)
    (fun k => (frameMetricWeight_bounds f hR hG k).1) hfull

theorem cappedGram_le_full {N d : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin d)) {R : ℝ} (hR : 0 < R)
    {G : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosDef)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadratic (cappedGram f R G) x ≤ quadratic (mean (framePopulation f)) x :=
  mean_weighted_le (framePopulation f) _ (framePopulation_posSemidef f)
    (fun k => (frameMetricWeight_bounds f hR hG k).2) x

theorem cappedGram_monotone {N d : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin d)) {R : ℝ} (hR : 0 < R)
    {G H : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosDef) (hH : H.PosDef)
    (hGH : ∀ x : EuclideanSpace ℂ (Fin d), quadratic G x ≤ quadratic H x)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadratic (cappedGram f R G) x ≤ quadratic (cappedGram f R H) x := by
  rw [cappedGram, cappedGram, quadratic_mean_eq, quadratic_mean_eq]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply Finset.sum_le_sum
  intro k _
  simp only [weightedPopulation, quadratic_smul_matrix, frameMetricWeight]
  apply mul_le_mul_of_nonneg_right _ (quadratic_nonneg (framePopulation_posSemidef f k) x)
  exact cappedWeight_antitone hR (quadratic_nonneg hH.posSemidef.inv (f k))
    (quadratic_nonneg hG.posSemidef.inv (f k)) (inverse_quadratic_antitone hG hH hGH (f k))

/-- Every updated row has leverage at most R relative to the preceding metric. -/
theorem capped_row_bound {N d : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin d)) {R : ℝ} (hR : 0 < R)
    {G : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosDef)
    (k : Fin N) (x : EuclideanSpace ℂ (Fin d)) :
    quadratic (weightedPopulation (framePopulation f) (frameMetricWeight f R G) k) x ≤
      R * quadratic G x := by
  rw [weightedPopulation, quadratic_smul_matrix, quadratic_framePopulation]
  have h := mul_le_mul_of_nonneg_left (row_energy_le_inverse_metric G hG (f k) x)
    (frameMetricWeight_bounds f hR hG k).1.le
  have hc := cappedWeight_mul_le hR (quadratic_nonneg hG.posSemidef.inv (f k))
  have hb := mul_le_mul_of_nonneg_right hc (quadratic_nonneg hG.posSemidef x)
  exact h.trans (by simpa only [frameMetricWeight, mul_assoc] using hb)

/-- The covariance update decreases the capped entropy potential. -/
theorem cappedGram_entropy_descent {N d : ℕ} (hN : 0 < N)
    (f : Fin N → EuclideanSpace ℂ (Fin d)) {R : ℝ} (hR : 0 < R)
    {G : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosDef)
    (hfull : (mean (framePopulation f)).PosDef) :
    Real.log (realDet (cappedGram f R G)) + (N : ℝ)⁻¹ *
      ∑ k, cappedEntropy R (quadratic (cappedGram f R G)⁻¹ (f k)) ≤
    Real.log (realDet G) + (N : ℝ)⁻¹ *
      ∑ k, cappedEntropy R (quadratic G⁻¹ (f k)) := by
  let B := cappedGram f R G
  have hB : B.PosDef := cappedGram_posDef hN f hR hG hfull
  letI := hB.isUnit.invertible
  have ht : (N : ℝ)⁻¹ * ∑ k, frameMetricWeight f R G k * quadratic G⁻¹ (f k) =
      (G⁻¹ * B).trace.re := (trace_mul_weightedMean f _ _).symm
  have hu : (N : ℝ)⁻¹ * ∑ k, frameMetricWeight f R G k * quadratic B⁻¹ (f k) =
      (d : ℝ) := by
    rw [← trace_mul_weightedMean]
    change (B⁻¹ * B).trace.re = (d : ℝ)
    rw [Matrix.inv_mul_of_invertible]
    simp
  have hs : (∑ k, cappedEntropy R (quadratic B⁻¹ (f k))) ≤
      (∑ k, cappedEntropy R (quadratic G⁻¹ (f k))) +
      (∑ k, frameMetricWeight f R G k * quadratic B⁻¹ (f k)) -
      (∑ k, frameMetricWeight f R G k * quadratic G⁻¹ (f k)) := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
      (fun k _ => cappedEntropy_tangent hR
        (quadratic_nonneg hG.posSemidef.inv (f k))
        (quadratic_nonneg hB.posSemidef.inv (f k)))
    simpa only [frameMetricWeight, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, add_sub_assoc] using h
  have hmul := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg N))
  rw [mul_sub, mul_add, ht, hu] at hmul
  have hdet := relative_log_realDet_le_trace hG hB
  change Real.log (realDet B) + _ ≤ _
  linarith

end
end LeanNumDetect.CappedWeightIteration
