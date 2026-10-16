import MultiTuran.ConsecutiveWindow.Chart
import MultiTuran.ConsecutiveWindow.ProductNorming
import MultiTuran.ConsecutiveWindow.Restriction

/-! # Chart construction and literal window restriction

Correspondence: `prop:norming` and `lem:restriction` of the supplement.
The chart is obtained internally from the original torus nodes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

theorem exists_chart_continuousNorming {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (hn : 2 ≤ n)
    (hblocks : ∀ q, n ≤ G.coordinateMinLength q) :
    ∃ center : Point d, ∃ winding : Fin n → Fin d → ℤ,
      (∀ j q, |chartNodes Y center winding j q| ≤ Real.pi-Real.pi/n) ∧
      ContinuousNorming G (chartNodes Y center winding) (windowNormingConstant d n) := by
  obtain ⟨center,winding,hchart⟩ := exists_translated_short_chart hn Y
  refine ⟨center,winding,hchart,?_⟩
  exact continuousNorming_of_long_consecutive_blocks G hn _ hchart
    (fun q m => (hblocks q).trans (G.coordinateMinLength_le q m))

@[simp] theorem generalizedVandermonde_minimumSingularValue_chartNodes {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d)
    (center : Point d) (winding : Fin n → Fin d → ℤ) :
    matrixSingularValue (generalizedVandermonde G (chartNodes Y center winding)) (n-1) =
      matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  simpa only [generalizedVandermonde,Int.cast_natCast] using
    matrixSingularValue_chartNodes (fun k q => (G.rowVector k q : ℤ))
      Y center winding (n-1)

/-- Literal `lem:restriction` with the supplement's fixed coefficient. -/
theorem window_restriction_lower_of_norming {d n M s : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (hn : 2 ≤ n)
    (hnorming : ContinuousNorming G Y (windowNormingConstant d n))
    (hadm : FullApertureAdmissible G M s) :
    Real.sqrt (windowNormingConstant d n) * (fullApertureWidth G M s : ℝ)^((d : ℝ)/2) *
      (2/(Real.pi*n))^d * G.rhoL *
      (G.fillingRatio/(multidimensionalTuranConstant*d))^(n-1) *
      matrixSingularValue (fullCubeVandermonde M s Y) (n-1) ≤
        matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  have hn0 : 0 < n := by omega
  exact product_restriction_lower G Y hn0 (windowNormingConstant_pos hn0).le hnorming hadm

theorem window_product_restriction_lower {d n M s : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (hn : 2 ≤ n)
    (hchart : ∀ j q, |Y j q| ≤ Real.pi-Real.pi/n)
    (hblocks : ∀ q, n ≤ G.coordinateMinLength q)
    (hadm : FullApertureAdmissible G M s) :
    Real.sqrt (windowNormingConstant d n) * (fullApertureWidth G M s : ℝ)^((d : ℝ)/2) *
      (2/(Real.pi*n))^d * G.rhoL *
      (G.fillingRatio/(multidimensionalTuranConstant*d))^(n-1) *
      matrixSingularValue (fullCubeVandermonde M s Y) (n-1) ≤
        matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  have hn0 : 0 < n := by omega
  exact product_restriction_lower G Y hn0 (windowNormingConstant_pos hn0).le
    (continuousNorming_of_long_consecutive_blocks G hn Y hchart
      (fun q m => (hblocks q).trans (G.coordinateMinLength_le q m))) hadm

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
