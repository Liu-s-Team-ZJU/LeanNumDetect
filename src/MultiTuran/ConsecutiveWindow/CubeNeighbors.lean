import MultiTuran.MultiClump.FullCube
import SegmentedVDM.NeighborFactors

/-! # Torus neighbor interpolation without a clump-diameter restriction

A selected coordinate realizes the periodic maximum distance. Quantizing its
frequency controls every shortest representative in `[-π,π]`, including the
far half of the circle. The resulting canonical factors retain the original
coefficient mass and bandwidth budgets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
open Set

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

/-- The natural floor is at least half its argument already for `t ≥ 1`. -/
theorem floor_ge_half_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    t / 2 ≤ (⌊t⌋₊ : ℝ) := by
  by_cases ht2 : 2 ≤ t
  · exact SegmentedVDM.floor_ge_half ht2
  · have hk : 1 ≤ ⌊t⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ t)).mpr (by simpa using ht)
    have hkR : (1 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hk
    linarith

/-- A bounded integer frequency separates a shortest torus difference, with
no shortness hypothesis beyond the intrinsic bound `|u| ≤ π`. -/
theorem exists_quantized_torus_chord {T Δ u : ℝ}
    (hT : 2 ≤ T) (hΔ : 0 < Δ) (hΔu : Δ ≤ |u|)
    (hu : |u| ≤ Real.pi) (hscale : T * Δ ≤ Real.pi) :
    ∃ k : ℕ, (k : ℝ) ≤ T ∧
      Real.sqrt 2 * (T * Δ / Real.pi) ≤
        ‖1 - Complex.exp (Complex.I * (((k : ℝ) * u : ℝ) : ℂ))‖ := by
  have hup : 0 < |u| := hΔ.trans_le hΔu
  let t : ℝ := min T (Real.pi / |u|)
  have ht : 1 ≤ t := le_min (by linarith)
    ((one_le_div hup).mpr hu)
  let k : ℕ := ⌊t⌋₊
  have hk : (k : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hkh : t / 2 ≤ (k : ℝ) := floor_ge_half_of_one_le ht
  have htU : t * |u| ≤ Real.pi :=
    (le_div_iff₀ hup).mp (min_le_right T (Real.pi / |u|))
  have htΔ : T * Δ ≤ t * |u| := by
    dsimp [t]
    rw [min_mul_of_nonneg _ _ hup.le]
    apply le_min
    · exact mul_le_mul_of_nonneg_left hΔu (by linarith)
    · simpa only [div_mul_cancel₀ _ hup.ne'] using hscale
  have hphase : |(k : ℝ) * u| = (k : ℝ) * |u| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hhi : |(k : ℝ) * u| ≤ Real.pi := by
    rw [hphase]
    exact (mul_le_mul_of_nonneg_right hk hup.le).trans htU
  have hlo : t * |u| / 2 ≤ |(k : ℝ) * u| := by
    rw [hphase]
    calc
      t * |u| / 2 = (t / 2) * |u| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hkh hup.le
  have ht0 : 0 ≤ t := by linarith
  have hb0 : 0 ≤ t * |u| / 2 := by positivity
  have hden := SegmentedVDM.exp_sub_one_lower hb0
    (by linarith : t * |u| / 2 ≤ Real.pi / 2) hlo hhi
  rw [norm_sub_rev] at hden
  refine ⟨k, hk.trans (min_le_left _ _), ?_⟩
  calc
    _ = (Real.sqrt 2 / Real.pi) * (T * Δ) := by ring
    _ ≤ (Real.sqrt 2 / Real.pi) * (t * |u|) :=
      mul_le_mul_of_nonneg_left htΔ (by positivity)
    _ = (2 * Real.sqrt 2 / Real.pi) * (t * |u| / 2) := by ring
    _ ≤ _ := hden

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
