import General.Fourier.CubeFrameBasis
import General.Fourier.ConnectedCubeBasisThickness

/-! Uniform subspace thickness for the whitened Fourier-cube frame.
This result uses the same basis constants as the direct logarithmic determinant
estimate, and remains available as a separate reusable consequence. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open scoped BigOperators InnerProductSpace
open Matrix WithLp

namespace LeanNumDetect.CubeFrameThickness

export CubeFrameBasis
  (cubeFramePathLength cubeFrameUpperConstant cubeFrameCoefficient cubeFrameThreshold
   cubeFrameRow cubeFrameCoarseShift comparisonConstant_one_le comparisonConstant_pos
   upperConstant_pos coefficient_pos threshold_pos cubeFrameRow_coordinate_shift
   cubeFrameRow_shiftPath cubeFrameRow_connectedBasis)

open CubeShiftBounds TranslatedBasisThickness ConnectedBasisBounds
noncomputable section

/-- Every subspace misses a uniform fraction of quantitatively separated cube
rows. The threshold depends only on the dimension and the source count. -/
theorem cubeFrameRow_thickCard {d n L : ℕ} [NeZero d]
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L)
    (U : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    (n + 1) * (n - Module.finrank ℂ U) * (L + 1) ^ d ≤
      2 * n ^ 2 * Nat.card {k : CubePoint d L //
        FarFromSubspace (cubeFrameRow z P L k) U (cubeFrameThreshold d n)} := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hc := coefficient_pos hd hn
  have hK := comparisonConstant_pos d n
  have hθ : cubeFrameThreshold d n <
      cubeFrameCoefficient d n / cubeShiftComparisonConstant d n := by
    unfold cubeFrameThreshold
    apply (div_lt_div_iff₀ (by positivity) hK).mpr
    nlinarith [mul_pos hc hK]
  obtain ⟨basis⟩ := cubeFrameRow_connectedBasis z P hP hwhite hz hn hL
  have hbudget : 2 * n * (L / (2 * n)) ≤ L := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self L (2 * n)
  have hnz : ∀ j r, z j r ≠ 0 := by
    intro j r h
    have hh := hz j r
    rw [h, norm_zero] at hh
    norm_num at hh
  let T : CubeTranslations d L basis.width →
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    fun t => naturalCubeTranslation z P (fun r => (t r).val)
  have htrans : ∀ t j,
      cubeFrameRow z P L (translatedPoint basis.point basis.width basis.point_le_width t j) =
        T t (cubeFrameRow z P L (basis.point j)) := by
    intro t j
    have h := isotropicCubeRootRow_natural_translation z P hP hnz (L + 1)
      (fun r => (basis.point j r).val) (fun r => (t r).val)
    have he : (fun r => (basis.point j r).val) + (fun r => (t r).val) =
        (fun r => (basis.point j r).val + (t r).val) := by
      funext r
      rfl
    rw [he] at h
    simpa only [cubeFrameRow, translatedPoint, T] using h
  have hconorm : ∀ t v, ‖v‖ ≤ cubeShiftComparisonConstant d n * ‖T t v‖ := by
    intro t v
    apply naturalCubeTranslation_conorm_le z P hP hwhite hz hn hL
    intro r
    have ht := (t r).isLt
    omega
  have h := basis.thick_card (by omega) hbudget hK hθ T htrans hconorm U
  simpa only [card_cubePoint, Nat.card_eq_fintype_card] using h

#print axioms cubeFrameRow_thickCard

end
end LeanNumDetect.CubeFrameThickness
