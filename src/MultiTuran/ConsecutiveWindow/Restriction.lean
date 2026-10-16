import MultiTuran.MultiClump.GeneralProduct

/-! # Product restriction for every full-aperture admissible pair

The actual full-aperture energy theorem is passed to the shared restriction
and norming interface; no interpolation-to-singular-value proof is repeated.
Correspondence: `lem:restriction` in the consecutive-window supplement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
open MultiClump
noncomputable section

theorem singularValue_lower_of_enclosing_norming_and_admissible_cube
    {d n M s : ℕ} (G H : SegmentedGrid d) (Y : Fin n → Point d)
    (houter : ∀ q, G.aperture q ≤ H.aperture q) (hn : 0 < n)
    {η : ℝ} (hη : 0 ≤ η) (hnorming : ContinuousNorming G Y η)
    (hadm : FullApertureAdmissible H M s) :
    Real.sqrt η * (fullApertureWidth H M s : ℝ)^((d : ℝ)/2) *
      (2/(Real.pi*n))^d * enclosingLongBlockFactor G H *
      (enclosingFillingRatio G H/(multidimensionalTuranConstant*d))^(n-1) *
      matrixSingularValue (fullCubeVandermonde M s Y) (n-1) ≤
        matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  have hσ : 0 ≤ matrixSingularValue (fullCubeVandermonde M s Y) (n-1) :=
    (fullCubeVandermonde M s Y).toEuclideanLin.singularValues_nonneg _
  let b : ℝ := (fullApertureWidth H M s : ℝ)^((d : ℝ)/2) *
    matrixSingularValue (fullCubeVandermonde M s Y) (n-1)
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hσ
  have haperture (c : Fin n → ℂ) :
      b * Real.sqrt (∑ j, ‖c j‖^2) ≤ Real.sqrt (setEnergy Y c H.apertureBox) :=
    fullAperture_L2_lower H Y c hn hadm
  have h := singularValue_lower_of_enclosing_norming_and_aperture_lower
    G H Y houter hn hη hb hnorming haperture
  convert h using 1
  dsimp [b]
  ring

/-- Literal same-aperture form of the supplement's restriction lemma. -/
theorem product_restriction_lower {d n M s : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (hn : 0 < n)
    {η : ℝ} (hη : 0 ≤ η) (hnorming : ContinuousNorming G Y η)
    (hadm : FullApertureAdmissible G M s) :
    Real.sqrt η * (fullApertureWidth G M s : ℝ)^((d : ℝ)/2) *
      (2/(Real.pi*n))^d * G.rhoL *
      (G.fillingRatio/(multidimensionalTuranConstant*d))^(n-1) *
      matrixSingularValue (fullCubeVandermonde M s Y) (n-1) ≤
        matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  simpa only [enclosingFillingRatio,SegmentedGrid.fillingRatio,
    enclosingLongBlockFactor,SegmentedGrid.rhoL] using
      singularValue_lower_of_enclosing_norming_and_admissible_cube G G Y
        (fun _ => le_rfl) hn hη hnorming hadm

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
