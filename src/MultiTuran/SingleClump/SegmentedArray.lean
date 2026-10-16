import MultiTuran.Turan.Main
import MultiTuran.SingleClump.ScaledRestriction

/-! # The manuscript's segmented-array minimum singular value estimate

The public theorem has precisely the localization, aperture, block-length
and term-count hypotheses of `lem:sv-md-array`. The displayed coefficient
is the literal right-hand side of `eq:sv-md-array`; no norming, derivative,
continuous-energy or Turán comparison is an additional assumption.
-/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The exact numerical inequality in manuscript `lem:sv-md-array`.
Existence of a common cube center is the article's common-translation
localization convention. The cube is open, as in the manuscript. -/
theorem segmentedArray_minimumSingularValue_lower {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d)
    (hY : ∃ center : Point d, ∀ j, InOpenCube (2*Real.pi/(G.omega : ℝ)) center (Y j))
    (hN : 2*n ≤ G.minAperture)
    (hblock : SegmentedBlockCondition (discretizationConstant d) G n) (hn : 4 ≤ n) :
    1 / Real.sqrt (2*(n : ℝ)) * (2/(Real.pi*n))^d * G.rhoL *
      (G.fillingRatio/(multidimensionalTuranConstant*d))^(n-1) *
      ((G.minAperture : ℝ)/(2*n))^((d : ℝ)/2) *
      ((G.minAperture : ℝ)*nodeSeparation Y/(2*Real.pi*n))^(n-1) ≤
        matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  obtain ⟨center,hcenter⟩ := hY
  exact segmentedArrayLowerBound_le_of_supNorm_comparison multidimensionalTuranConstant_pos
    G Y center hn hN hcenter hblock
    (fun c => aperture_supNorm_turan G (by omega) Y c)

/-- The same complete result using the named literal coefficient. -/
theorem segmentedArrayLowerBound_le_minimumSingularValue {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d)
    (hY : ∃ center : Point d, ∀ j, InOpenCube (2*Real.pi/(G.omega : ℝ)) center (Y j))
    (hN : 2*n ≤ G.minAperture)
    (hblock : SegmentedBlockCondition (discretizationConstant d) G n) (hn : 4 ≤ n) :
    segmentedArrayLowerBound multidimensionalTuranConstant G Y ≤
      matrixSingularValue (generalizedVandermonde G Y) (n-1) :=
  segmentedArray_minimumSingularValue_lower G Y hY hN hblock hn

end
end LeanNumDetect.MultiTuran
