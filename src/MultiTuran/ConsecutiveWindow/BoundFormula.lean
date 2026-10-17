import MultiTuran.ConsecutiveWindow.ProductNorming
import MultiTuran.ConsecutiveWindow.Chart
import MultiTuran.MultiClump.GeneralProduct

/-! # The consecutive-window coefficient and shared spectral transfer

All measured rows enter the norming and restriction factors. The aperture
may be specified independently of the measured product grid.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
open MultiClump
noncomputable section

def consecutiveWindowProductArrayLowerBound {d n : ℕ} (G H : SegmentedGrid d)
    (Y : Fin n → Point d) (nStar : ℕ) : ℝ :=
  Real.sqrt (windowNormingConstant d n/((n : ℝ)*6^nStar)) *
    (2/(Real.pi*n))^d * enclosingLongBlockFactor G H *
    (enclosingFillingRatio G H/(multidimensionalTuranConstant*d))^(n-1) *
    ((H.minAperture : ℝ)/(3*nStar))^((d : ℝ)/2) *
    ((H.minAperture : ℝ)*nodeSeparation Y/(5*Real.pi*nStar))^(nStar-1)

@[simp] theorem consecutiveWindowProductArrayLowerBound_chartNodes {d n : ℕ}
    (G H : SegmentedGrid d) (Y : Fin n → Point d) (center : Point d)
    (winding : Fin n → Fin d → ℤ) (nStar : ℕ) :
    consecutiveWindowProductArrayLowerBound G H (chartNodes Y center winding) nStar =
      consecutiveWindowProductArrayLowerBound G H Y nStar := by
  simp only [consecutiveWindowProductArrayLowerBound,nodeSeparation_chartNodes]

theorem consecutiveWindowProductArrayLowerBound_le_of_norming_cube
    {d n s nStar : ℕ} (G H : SegmentedGrid d) (Y : Fin n → Point d)
    (houter : ∀ q, G.aperture q ≤ H.aperture q) (hn : 0 < n)
    (hnorming : ContinuousNorming G Y (windowNormingConstant d n))
    (hfull : s+1 ≤ H.minAperture)
    (hcube : 1/Real.sqrt ((n : ℝ)*6^nStar) *
      ((H.minAperture : ℝ)/(3*nStar))^((d : ℝ)/2) *
      ((H.minAperture : ℝ)*nodeSeparation Y/(5*Real.pi*nStar))^(nStar-1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n-1)) :
    consecutiveWindowProductArrayLowerBound G H Y nStar ≤
      matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  have hη := (windowNormingConstant_pos (d := d) hn).le
  have h := singularValue_lower_of_enclosing_norming_and_cube G H Y houter hn hη
    (show 0 ≤ 1/Real.sqrt ((n : ℝ)*6^nStar) *
      ((H.minAperture : ℝ)/(3*nStar))^((d : ℝ)/2) *
      ((H.minAperture : ℝ)*nodeSeparation Y/(5*Real.pi*nStar))^(nStar-1) by
        have hθ := nodeSeparation_nonneg Y
        positivity)
    hnorming hfull hcube
  unfold consecutiveWindowProductArrayLowerBound
  rw [Real.sqrt_div hη]
  convert h using 1
  ring

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
