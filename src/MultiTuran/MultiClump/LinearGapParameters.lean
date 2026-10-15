import MultiTuran.MultiClump.BlockFeasibility
import MultiTuran.MultiClump.LinearGapConstants

/-! # Selector width for the linear clump-separation threshold -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

def linearGapSelectorWidthParameter {d : ℕ} (G : SegmentedGrid d) (nStar : ℕ) : ℕ :=
  2 * ((3 * G.minThickLength) / (16 * nStar))

theorem linearGap_blockCondition_minimumLength_lower {d nStar : ℕ}
    (G : SegmentedGrid d) (hd : 2 ≤ d) (hnStar : 2 ≤ nStar) {τ C_B : ℝ}
    (hτ : 0 ≤ τ) (hC_B : 24 ≤ C_B)
    (hblock : multiClumpBlockConstant d C_B * G.rowCount *
      ((nStar : ℝ) ^ (4 * d + 5) / (G.minThickLength : ℝ) ^ (d + 1) +
        (nStar : ℝ) ^ (4 * d + 1) * τ / (G.minThickLength : ℝ) ^ d) ≤ 1) :
    80 * (nStar : ℝ) ≤ G.minThickLength := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (2 : ℝ) ≤ nStar := by exact_mod_cast hnStar
  have hB : (32 : ℝ) ≤ multiClumpBlockConstant d C_B :=
    (show (32 : ℝ) ≤ 16 * (d : ℝ) by nlinarith).trans (multiClumpBlockConstant_lower hC_B)
  have hpow : (nStar : ℝ) ^ 3 ≤ (nStar : ℝ) ^ (4 * d + 5) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hproduct := mul_le_mul hB hpow (by positivity)
    (show 0 ≤ multiClumpBlockConstant d C_B by linarith)
  have hlength := blockCondition_minimumLength_power_lower G hτ hC_B hblock
  have hsq : 4 ≤ (nStar : ℝ) ^ 2 := by nlinarith
  have hcube := mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg nStar)
  nlinarith only [hproduct, hlength, hcube, hnR]

theorem linearGapSelectorWidthParameter_eight_mul_le {d : ℕ}
    (G : SegmentedGrid d) (nStar : ℕ) :
    8 * (nStar * linearGapSelectorWidthParameter G nStar) ≤ 3 * G.minThickLength := by
  have h := Nat.div_mul_le_self (3 * G.minThickLength) (16 * nStar)
  unfold linearGapSelectorWidthParameter
  nlinarith only [h]

theorem linearGapSelectorWidthParameter_fits_blocks {d : ℕ}
    (G : SegmentedGrid d) (nStar : ℕ) :
    2 * (nStar * linearGapSelectorWidthParameter G nStar) < G.minThickLength := by
  have h := linearGapSelectorWidthParameter_eight_mul_le G nStar
  have hL := minThickLength_pos G
  nlinarith only [h, hL]

theorem linearGapSelectorWidthParameter_pos {d nStar : ℕ}
    (G : SegmentedGrid d) (hnStar : 0 < nStar)
    (hL : 80 * (nStar : ℝ) ≤ G.minThickLength) :
    0 < linearGapSelectorWidthParameter G nStar := by
  have hLN : 80 * nStar ≤ G.minThickLength := by exact_mod_cast hL
  have hden : 0 < 16 * nStar := by omega
  have hq : 1 ≤ (3 * G.minThickLength) / (16 * nStar) :=
    (Nat.le_div_iff_mul_le hden).mpr (by nlinarith only [hLN])
  unfold linearGapSelectorWidthParameter
  omega

/-- The lower bandwidth estimate displayed in the manuscript. -/
theorem linearGapSelectorWidthParameter_lower {d nStar : ℕ}
    (G : SegmentedGrid d) (hnStar : 0 < nStar)
    (hL : 80 * (nStar : ℝ) ≤ G.minThickLength) :
    7 * (G.minThickLength : ℝ) / (20 * nStar) ≤
      linearGapSelectorWidthParameter G nStar := by
  have hden : 0 < 16 * nStar := by omega
  have hdiv := Nat.div_add_mod (3 * G.minThickLength) (16 * nStar)
  have hmod := Nat.mod_lt (3 * G.minThickLength) hden
  have hfloor : 3 * G.minThickLength ≤
      8 * nStar * linearGapSelectorWidthParameter G nStar + 16 * nStar := by
    unfold linearGapSelectorWidthParameter
    nlinarith only [hdiv, hmod]
  have hfloorR : 3 * (G.minThickLength : ℝ) ≤
      8 * (nStar : ℝ) * linearGapSelectorWidthParameter G nStar + 16 * nStar := by
    exact_mod_cast hfloor
  apply (div_le_iff₀ (show (0 : ℝ) < 20 * nStar by positivity)).mpr
  nlinarith only [hfloorR, hL]

theorem linearGapSelectorWidthParameter_separation {d nStar : ℕ}
    (G : SegmentedGrid d) (hnStar : 0 < nStar)
    (hL : 80 * (nStar : ℝ) ≤ G.minThickLength) :
    4 * Real.pi * (7 / 5 : ℝ) * d /
        ((linearGapSelectorWidthParameter G nStar : ℝ) + 1) ≤
      16 * Real.pi * d * nStar / G.minThickLength := by
  have hden : 0 < 16 * nStar := by omega
  have hdiv := Nat.div_add_mod (3 * G.minThickLength) (16 * nStar)
  have hmod := Nat.mod_lt (3 * G.minThickLength) hden
  have hfloor : 3 * G.minThickLength ≤
      8 * nStar * linearGapSelectorWidthParameter G nStar + 16 * nStar := by
    unfold linearGapSelectorWidthParameter
    nlinarith only [hdiv, hmod]
  have hfloorR : 3 * (G.minThickLength : ℝ) ≤
      8 * (nStar : ℝ) * linearGapSelectorWidthParameter G nStar + 16 * nStar := by
    exact_mod_cast hfloor
  have hbase : (7 / 20 : ℝ) * G.minThickLength ≤
      (nStar : ℝ) * ((linearGapSelectorWidthParameter G nStar : ℝ) + 1) := by
    nlinarith only [hfloorR, hL]
  have hK : 0 < (linearGapSelectorWidthParameter G nStar : ℝ) + 1 := by positivity
  have hlength : (0 : ℝ) < G.minThickLength := by exact_mod_cast minThickLength_pos G
  apply (div_le_div_iff₀ hK hlength).mpr
  convert mul_le_mul_of_nonneg_left hbase
    (show 0 ≤ 16 * Real.pi * (d : ℝ) by positivity) using 1 <;> ring

theorem linearGapSeparationThreshold_le_pi {d nStar : ℕ}
    (G : SegmentedGrid d) (hnStar : 0 < nStar) {τ C_B : ℝ}
    (hτ : 0 ≤ τ) (hC_B : 24 ≤ C_B)
    (hblock : multiClumpBlockConstant d C_B * G.rowCount *
      ((nStar : ℝ) ^ (4 * d + 5) / (G.minThickLength : ℝ) ^ (d + 1) +
        (nStar : ℝ) ^ (4 * d + 1) * τ / (G.minThickLength : ℝ) ^ d) ≤ 1) :
    16 * Real.pi * d * nStar / G.minThickLength ≤ Real.pi := by
  have hn : (1 : ℝ) ≤ nStar := by exact_mod_cast hnStar
  have hns : (nStar : ℝ) ≤ (nStar : ℝ) ^ 2 := by nlinarith
  have hlength : (0 : ℝ) ≤ G.minThickLength := Nat.cast_nonneg _
  have hgap := mul_le_mul_of_nonneg_left hns
    (show 0 ≤ 16 * Real.pi * (d : ℝ) by positivity)
  exact (div_le_div_of_nonneg_right hgap hlength).trans
    (blockCondition_separationThreshold_le_pi G hnStar hτ hC_B hblock)

end
end LeanNumDetect.MultiTuran.MultiClump
