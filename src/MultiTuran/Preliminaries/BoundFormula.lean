import MultiTuran.Preliminaries.SegmentedGrid

/-! # The manuscript's explicit segmented-array coefficient

This file defines the literal right-hand side of `eq:sv-md-array`. Defining
the coefficient is separate from proving that it bounds a singular value.
-/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- Literal coefficient in `eq:sv-md-array`, with the actual torus separation,
actual aperture, actual filling ratio, and actual minimum block lengths. -/
def segmentedArrayLowerBound {d n : ℕ} (C_T : ℝ) (G : SegmentedGrid d)
    (Y : Fin n → Point d) : ℝ :=
  1 / Real.sqrt (2 * (n : ℝ)) *
    (2 / (Real.pi * n)) ^ d *
    G.rhoL *
    (G.fillingRatio / (C_T * d)) ^ (n - 1) *
    ((G.minAperture : ℝ) / (2 * n)) ^ ((d : ℝ) / 2) *
    ((G.minAperture : ℝ) * nodeSeparation Y / (2 * Real.pi * n)) ^ (n - 1)

/-- Literal geometric sufficient condition `eq:md-block-condition`. -/
def SegmentedBlockCondition {d : ℕ} (C_disc : ℝ) (G : SegmentedGrid d) (n : ℕ) : Prop :=
  (C_disc * (G.rowCount : ℝ) * (n : ℝ) ^ (4 * d + 5)) ^ (1 / ((d : ℝ) + 1)) ≤
    (G.minLength : ℝ)

/-- Raising the article's real-root condition to its positive integer power
gives the exact arithmetic threshold used in the Riemann error estimate. -/
theorem blockCondition_power_threshold {d n : ℕ} {C_disc : ℝ}
    (hC : 0 ≤ C_disc) (G : SegmentedGrid d)
    (hblock : SegmentedBlockCondition C_disc G n) :
    C_disc * (G.rowCount : ℝ) * (n : ℝ) ^ (4 * d + 5) ≤
      (G.minLength : ℝ) ^ (d + 1) := by
  have hA : 0 ≤ C_disc * (G.rowCount : ℝ) * (n : ℝ) ^ (4 * d + 5) := by
    positivity
  have hd : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hA _)
    hblock hd.le
  rw [← Real.rpow_mul hA, one_div_mul_cancel hd.ne', Real.rpow_one] at h
  have hdcast : (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) := by push_cast; rfl
  rw [hdcast, Real.rpow_natCast] at h
  exact h

/-- The positive thickened block length is at least the manuscript's integer
degree; thus the literal sufficient condition also controls thickened cells. -/
theorem blockCondition_thickened_power_threshold {d n : ℕ} {C_disc : ℝ}
    (hC : 0 ≤ C_disc) (G : SegmentedGrid d)
    (hblock : SegmentedBlockCondition C_disc G n) :
    C_disc * (G.rowCount : ℝ) * (n : ℝ) ^ (4 * d + 5) ≤
      (G.minThickLength : ℝ) ^ (d + 1) := by
  apply (blockCondition_power_threshold hC G hblock).trans
  apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ (d + 1)
  exact_mod_cast le_trans (Nat.le_add_right G.minLength 1)
    G.minLength_add_one_le_minThickLength

theorem segmentedArrayLowerBound_nonneg {d n : ℕ} {C_T : ℝ}
    (hC_T : 0 ≤ C_T) (G : SegmentedGrid d) (Y : Fin n → Point d) :
    0 ≤ segmentedArrayLowerBound C_T G Y := by
  have hρ := G.fillingRatio_pos.le
  have hθ := nodeSeparation_nonneg Y
  unfold segmentedArrayLowerBound SegmentedGrid.rhoL
  positivity

end
end LeanNumDetect.MultiTuran
