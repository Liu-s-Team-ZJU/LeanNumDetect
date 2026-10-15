import MultiTuran.MultiClump.BlockParameters

/-! # Block feasibility already forced by the Riemann condition

The explicit `B_d` hypothesis implies the minimum block length needed for
the selector construction.  It is therefore unnecessary to impose a second
upper bound on an auxiliary clump-separation parameter.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

theorem minThickLength_pow_dimension_le_rowCount {d : ℕ} (G : SegmentedGrid d) :
    G.minThickLength ^ d ≤ G.rowCount := by
  have hcoord (q : Fin d) : G.minThickLength ≤ (G.coordinateRows q).card := by
    calc
      G.minThickLength ≤ G.coordinateMinLength q :=
        minThickLength_le_coordinateMinLength G q
      _ ≤ G.thickLength q 0 := G.coordinateMinLength_le q 0
      _ ≤ ∑ m, G.thickLength q m :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      _ = (G.coordinateRows q).card := (G.coordinateRows_card q).symm
  calc
    G.minThickLength ^ d = ∏ _q : Fin d, G.minThickLength := by simp
    _ ≤ G.rowCount := by
      unfold SegmentedGrid.rowCount
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun q _ => hcoord q)

theorem multiClumpBlockConstant_lower {d : ℕ} {C_B : ℝ} (hC_B : 24 ≤ C_B) :
    16 * (d : ℝ) ≤ multiClumpBlockConstant d C_B := by
  have hC : 0 ≤ C_B := by linarith
  have hpowTwo : 1 ≤ (2 : ℝ) ^ (d + 2) := one_le_pow₀ (by norm_num)
  have hsqrt : 1 ≤ Real.sqrt 108 + 1 := by linarith [Real.sqrt_nonneg (108 : ℝ)]
  have hpi : 1 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hpowPi : 1 ≤ (Real.pi / 2) ^ (2 * d) := one_le_pow₀ hpi
  have hDC : 0 ≤ (d : ℝ) * C_B := by positivity
  have hfirst : (d : ℝ) * C_B ≤ 2 ^ (d + 2) * d * C_B := by
    simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right hpowTwo hDC
  have hsecond : 2 ^ (d + 2) * (d : ℝ) * C_B ≤
      2 ^ (d + 2) * d * C_B * (Real.sqrt 108 + 1) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 2 ^ (d + 2) * (d : ℝ) * C_B by positivity)
  have hthird : 2 ^ (d + 2) * (d : ℝ) * C_B * (Real.sqrt 108 + 1) ≤
      multiClumpBlockConstant d C_B := by
    unfold multiClumpBlockConstant
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowPi
      (show 0 ≤ 2 ^ (d + 2) * (d : ℝ) * C_B * (Real.sqrt 108 + 1) by positivity)
  calc
    16 * (d : ℝ) ≤ d * C_B := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (show (16 : ℝ) ≤ C_B by linarith) (Nat.cast_nonneg d)
    _ ≤ _ := hfirst.trans (hsecond.trans hthird)

theorem blockCondition_minimumLength_power_lower {d nStar : ℕ}
    (G : SegmentedGrid d) {τ C_B : ℝ} (hτ : 0 ≤ τ) (hC_B : 24 ≤ C_B)
    (hblock : multiClumpBlockConstant d C_B * G.rowCount *
      ((nStar : ℝ) ^ (4 * d + 5) / (G.minThickLength : ℝ) ^ (d + 1) +
        (nStar : ℝ) ^ (4 * d + 1) * τ / (G.minThickLength : ℝ) ^ d) ≤ 1) :
    multiClumpBlockConstant d C_B * (nStar : ℝ) ^ (4 * d + 5) ≤ G.minThickLength := by
  let L : ℝ := G.minThickLength
  let B : ℝ := multiClumpBlockConstant d C_B
  have hL : 0 < L := by dsimp [L]; exact_mod_cast minThickLength_pos G
  have hB : 0 ≤ B :=
    (mul_nonneg (by norm_num) (Nat.cast_nonneg d)).trans (multiClumpBlockConstant_lower hC_B)
  have hrows : L ^ d ≤ (G.rowCount : ℝ) := by
    dsimp [L]
    exact_mod_cast minThickLength_pow_dimension_le_rowCount G
  have hfirst : B * G.rowCount * ((nStar : ℝ) ^ (4 * d + 5) / L ^ (d + 1)) ≤ 1 := by
    have hsecond : 0 ≤ (nStar : ℝ) ^ (4 * d + 1) * τ / L ^ d := by positivity
    have hBR : 0 ≤ B * G.rowCount := by positivity
    change B * G.rowCount *
      ((nStar : ℝ) ^ (4 * d + 5) / L ^ (d + 1) +
        (nStar : ℝ) ^ (4 * d + 1) * τ / L ^ d) ≤ 1 at hblock
    nlinarith only [hblock, mul_nonneg hBR hsecond]
  have hsmall : B * L ^ d * ((nStar : ℝ) ^ (4 * d + 5) / L ^ (d + 1)) ≤ 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrows hB)
      (by positivity)).trans hfirst
  have heq : B * L ^ d * ((nStar : ℝ) ^ (4 * d + 5) / L ^ (d + 1)) =
      B * (nStar : ℝ) ^ (4 * d + 5) / L := by
    rw [pow_succ L d]
    field_simp [ne_of_gt hL]
  rw [heq] at hsmall
  simpa only [one_mul] using (div_le_iff₀ hL).mp hsmall

/-- The Riemann hypothesis already implies the block length required to
choose the explicit inter-clump separation threshold below `π`. -/
theorem blockCondition_minimumLength_lower {d nStar : ℕ}
    (G : SegmentedGrid d) (hnStar : 0 < nStar) {τ C_B : ℝ}
    (hτ : 0 ≤ τ) (hC_B : 24 ≤ C_B)
    (hblock : multiClumpBlockConstant d C_B * G.rowCount *
      ((nStar : ℝ) ^ (4 * d + 5) / (G.minThickLength : ℝ) ^ (d + 1) +
        (nStar : ℝ) ^ (4 * d + 1) * τ / (G.minThickLength : ℝ) ^ d) ≤ 1) :
    16 * (d : ℝ) * (nStar : ℝ) ^ 2 ≤ G.minThickLength := by
  have hn : 1 ≤ (nStar : ℝ) := by exact_mod_cast hnStar
  have hpow : (nStar : ℝ) ^ 2 ≤ (nStar : ℝ) ^ (4 * d + 5) :=
    pow_le_pow_right₀ hn (by omega)
  have hcoeff := multiClumpBlockConstant_lower (d := d) hC_B
  have hB : 0 ≤ multiClumpBlockConstant d C_B :=
    (mul_nonneg (by norm_num) (Nat.cast_nonneg d)).trans hcoeff
  exact (mul_le_mul hcoeff hpow (by positivity) hB).trans
    (blockCondition_minimumLength_power_lower G hτ hC_B hblock)

theorem blockCondition_separationThreshold_le_pi {d nStar : ℕ}
    (G : SegmentedGrid d) (hnStar : 0 < nStar) {τ C_B : ℝ}
    (hτ : 0 ≤ τ) (hC_B : 24 ≤ C_B)
    (hblock : multiClumpBlockConstant d C_B * G.rowCount *
      ((nStar : ℝ) ^ (4 * d + 5) / (G.minThickLength : ℝ) ^ (d + 1) +
        (nStar : ℝ) ^ (4 * d + 1) * τ / (G.minThickLength : ℝ) ^ d) ≤ 1) :
    16 * Real.pi * d * (nStar : ℝ) ^ 2 / G.minThickLength ≤ Real.pi := by
  have hL : (0 : ℝ) < G.minThickLength := by exact_mod_cast minThickLength_pos G
  apply (div_le_iff₀ hL).mpr
  have h := mul_le_mul_of_nonneg_left
    (blockCondition_minimumLength_lower G hnStar hτ hC_B hblock) Real.pi_pos.le
  nlinarith only [h]

end
end LeanNumDetect.MultiTuran.MultiClump
