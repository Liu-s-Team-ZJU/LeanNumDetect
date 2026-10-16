import MultiTuran.ConsecutiveWindow.ProductNorming
import MultiTuran.ConsecutiveWindow.Chart
import MultiTuran.ConsecutiveWindow.Restriction
import MultiTuran.SingleClump.Scaling

/-! # The single-clump bound with consecutive samples in every block

Correspondence: `cor:single-clump` in the consecutive-window supplement.
The public result constructs its chart and norming estimate internally.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

theorem singleClump_lower_of_norming {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (hn : 0 < n) (hN : 2 * n ≤ G.minAperture)
    {η : ℝ} (hη : 0 ≤ η) (hnorming : ContinuousNorming G Y η)
    (hshort : ((G.minAperture / n : ℕ) : ℝ) * nodeDiameter Y ≤ Real.pi) :
    Real.sqrt η / Real.sqrt (n : ℝ) * (2 / (Real.pi * n)) ^ d * G.rhoL *
      (G.fillingRatio / (multidimensionalTuranConstant * d)) ^ (n - 1) *
      ((G.minAperture : ℝ) / (2 * n)) ^ ((d : ℝ) / 2) *
      ((G.minAperture : ℝ) * nodeSeparation Y / (2 * Real.pi * n)) ^ (n - 1) ≤
        matrixSingularValue (generalizedVandermonde G Y) (n - 1) := by
  let M : ℕ := G.minAperture / n
  let s : ℕ := n - 1
  have hM : 0 < M := Nat.div_pos (by omega) hn
  have hfull : (s + 1) * M ≤ G.minAperture := by
    have hs : s + 1 = n := by dsimp [s]; omega
    rw [hs]
    exact Nat.mul_div_le G.minAperture n
  have hadm : FullApertureAdmissible G M s := by
    constructor
    · exact hM
    · nlinarith
    · nlinarith
  have hcube := elementary_fullCube_no_wrap_lower (M := M) G.dimension_pos hn
    (show n - 1 ≤ s by rfl) Y hshort
  have hrestriction := product_restriction_lower G Y hn hη hnorming hadm
  rw [fullApertureWidth_eq_dilation G hfull] at hrestriction
  let A : ℝ := Real.sqrt η * (2 / (Real.pi * n)) ^ d * G.rhoL *
    (G.fillingRatio / (multidimensionalTuranConstant * d)) ^ (n - 1)
  have hA : 0 ≤ A := by
    have hL := G.rhoL_pos.le
    have hρ := G.fillingRatio_pos.le
    have hC := multidimensionalTuranConstant_pos.le
    dsimp [A]
    positivity
  have hraw : A / Real.sqrt (n : ℝ) *
      ((M : ℝ) ^ ((d : ℝ) / 2) *
        ((M : ℝ) * nodeSeparation Y / Real.pi) ^ (n - 1)) ≤
        matrixSingularValue (generalizedVandermonde G Y) (n - 1) := by
    calc
      _ = (A * (M : ℝ) ^ ((d : ℝ) / 2)) *
          ((1 / Real.sqrt (n : ℝ)) *
            ((M : ℝ) * nodeSeparation Y / Real.pi) ^ (n - 1)) := by ring
      _ ≤ (A * (M : ℝ) ^ ((d : ℝ) / 2)) *
          matrixSingularValue (fullCubeVandermonde M s Y) (n - 1) :=
        mul_le_mul_of_nonneg_left hcube
          (mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      _ ≤ _ := by convert hrestriction using 1; dsimp [A]; ring
  have hscaled := aperture_scaled_factors_lower d G.minAperture n hn hN
    (nodeSeparation_nonneg Y)
  calc
    _ = (A / Real.sqrt (n : ℝ)) *
        (((G.minAperture : ℝ) / (2 * n)) ^ ((d : ℝ) / 2) *
          ((G.minAperture : ℝ) * nodeSeparation Y / (2 * Real.pi * n)) ^ (n - 1)) := by
      dsimp [A]
      ring
    _ ≤ (A / Real.sqrt (n : ℝ)) *
        ((M : ℝ) ^ ((d : ℝ) / 2) *
          ((M : ℝ) * nodeSeparation Y / Real.pi) ^ (n - 1)) :=
      mul_le_mul_of_nonneg_left hscaled (div_nonneg hA (Real.sqrt_nonneg _))
    _ ≤ _ := hraw

theorem singleClump_lower_of_long_consecutive_blocks {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d)
    (hY : ∃ center : Point d, ∀ j,
      InOpenCube (2 * Real.pi / (G.omega : ℝ)) center (Y j))
    (hN : 2 * n ≤ G.minAperture)
    (hblocks : ∀ q (m : G.Block q), n ≤ G.thickLength q m) (hn : 4 ≤ n) :
    Real.sqrt (windowNormingConstant d n) / Real.sqrt (n : ℝ) *
      (2 / (Real.pi * n)) ^ d * G.rhoL *
      (G.fillingRatio / (multidimensionalTuranConstant * d)) ^ (n - 1) *
      ((G.minAperture : ℝ) / (2 * n)) ^ ((d : ℝ) / 2) *
      ((G.minAperture : ℝ) * nodeSeparation Y / (2 * Real.pi * n)) ^ (n - 1) ≤
        matrixSingularValue (generalizedVandermonde G Y) (n - 1) := by
  obtain ⟨localizedCenter, hlocalized⟩ := hY
  have hshort := G.noWrap_of_nodes_in_open_cube Y localizedCenter hn hlocalized
  obtain ⟨center, winding, hchart⟩ := exists_translated_short_chart (by omega : 2 ≤ n) Y
  let Z : Fin n → Point d := chartNodes Y center winding
  have hnorming : ContinuousNorming G Z (windowNormingConstant d n) :=
    continuousNorming_of_long_consecutive_blocks G (by omega) Z hchart hblocks
  have hshortZ : ((G.minAperture / n : ℕ) : ℝ) * nodeDiameter Z ≤ Real.pi := by
    simpa only [Z, nodeDiameter_chartNodes] using hshort
  have h := singleClump_lower_of_norming G Z (by omega) hN
    (windowNormingConstant_pos (by omega : 0 < n)).le hnorming hshortZ
  have hσ : matrixSingularValue (generalizedVandermonde G Z) (n - 1) =
      matrixSingularValue (generalizedVandermonde G Y) (n - 1) := by
    simpa only [generalizedVandermonde, Int.cast_natCast, Z] using
      matrixSingularValue_chartNodes (fun k : G.Row => fun q => (G.rowVector k q : ℤ))
        Y center winding (n - 1)
  rw [hσ] at h
  simpa only [Z, nodeSeparation_chartNodes] using h

/-- Literal `cor:single-clump`, with the original open-cube localization,
integer block degrees, and the explicit consecutive-window constant. -/
theorem singleClump_minimumSingularValue_lower {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d)
    (hY : ∃ center : Point d, ∀ j,
      InOpenCube (2 * Real.pi / (G.omega : ℝ)) center (Y j))
    (hN : 2 * n ≤ G.minAperture)
    (hblocks : ∀ q (m : G.Block q), n - 1 ≤ G.length q m) (hn : 4 ≤ n) :
    Real.sqrt (windowNormingConstant d n) / Real.sqrt (n : ℝ) *
      (2 / (Real.pi * n)) ^ d * G.rhoL *
      (G.fillingRatio / (multidimensionalTuranConstant * d)) ^ (n - 1) *
      ((G.minAperture : ℝ) / (2 * n)) ^ ((d : ℝ) / 2) *
      ((G.minAperture : ℝ) * nodeSeparation Y / (2 * Real.pi * n)) ^ (n - 1) ≤
        matrixSingularValue (generalizedVandermonde G Y) (n - 1) := by
  apply singleClump_lower_of_long_consecutive_blocks G Y hY hN _ hn
  intro q m
  have h := hblocks q m
  simp only [SegmentedGrid.thickLength]
  omega

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
