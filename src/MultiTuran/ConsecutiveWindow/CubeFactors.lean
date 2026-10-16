import MultiTuran.ConsecutiveWindow.CubeNeighbors

/-! # Canonical torus factors for unrestricted clumps -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
open Set

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
open NumDetect
noncomputable section

/-- A coordinate factor with the exact clipped-spacing mass, without any
upper bound on the distance between the two torus nodes. -/
theorem torus_neighbor_factor {d : ℕ} (hd : 0 < d)
    {T Δ : ℝ} (hT : 2 ≤ T) (hΔ : 0 < Δ) (hscale : T * Δ ≤ Real.pi)
    (anchor y : Point d) (ha : InAngularCube anchor) (hy : InAngularCube y)
    (hmin : Δ ≤ torusLInfDistance y anchor) :
    ∃ P : SegmentedPolynomial d 0 ⌊T⌋₊ 1,
      P.angularValue anchor = 1 ∧ P.angularValue y = 0 ∧
      P.mass ≤ Real.sqrt 2 / (T * Δ / Real.pi) := by
  classical
  obtain ⟨q,hq⟩ := exists_coordinate_eq_torusLInfDistance hd y anchor
  let u : Point d := wrappedDifference y anchor
  have huq : |u q| = torusLInfDistance y anchor := by
    dsimp [u,wrappedDifference]
    rw [abs_wrappedCoordinateDifference (hy q) (ha q)]
    rw [← MultiClump.torusCoordinateDistance_eq_periodicCoordinateDistance (hy q) (ha q)]
    exact hq.symm
  have hupi : |u q| ≤ Real.pi := by
    dsimp [u,wrappedDifference]
    rw [abs_wrappedCoordinateDifference (hy q) (ha q)]
    exact periodicCoordinateDistance_le_pi (hy q) (ha q)
  obtain ⟨k,hk,hden⟩ := exists_quantized_torus_chord hT hΔ
    (by simpa only [huq] using hmin) hupi hscale
  have hkN : k ≤ ⌊T⌋₊ := Nat.le_floor hk
  let v : Fin d → ℤ := fun p => if p = q then (k : ℤ) else 0
  have hv (p : Fin d) : (v p).natAbs ≤ ⌊T⌋₊ := by
    by_cases hp : p = q
    · simpa [v,hp] using hkN
    · simp [v,hp]
  have hsum : (∑ p, (v p : ℝ) * u p) = (k : ℝ) * u q := by
    simp [v]
  let z : ℂ := Complex.exp (Complex.I * (((k : ℝ) * u q : ℝ) : ℂ))
  have hzn : ‖z‖ = 1 := by simp [z,Complex.norm_exp]
  have hden' : Real.sqrt 2 * (T * Δ / Real.pi) ≤ ‖1-z‖ := hden
  have hA : 0 < T * Δ / Real.pi := by
    have hT0 : 0 < T := by linarith
    exact div_pos (mul_pos hT0 hΔ) Real.pi_pos
  have hz : z ≠ 1 := by
    intro he
    have hp : 0 < Real.sqrt 2 * (T * Δ / Real.pi) := by positivity
    simp [he] at hden'
    linarith
  let P := (SegmentedPolynomial.twoPointRecentered (by norm_num : 0 < (1 : ℕ))
    v hv z).translate anchor
  refine ⟨P,?_,?_,?_⟩
  · rw [SegmentedPolynomial.angularValue_translate,sub_self]
    exact SegmentedPolynomial.angularValue_twoPointRecentered_zero _ v hv z hz
  · rw [SegmentedPolynomial.angularValue_translate,
      SegmentedPolynomial.angularValue_sub_eq_wrappedDifference]
    apply SegmentedPolynomial.angularValue_twoPointRecentered_vanishes
    simp only [Nat.cast_one,one_mul]
    change z = Complex.exp (Complex.I * ((∑ p, (v p : ℝ) * u p : ℝ) : ℂ))
    rw [hsum]
  · rw [SegmentedPolynomial.mass_translate]
    calc
      _ ≤ 2 / ‖1-z‖ := SegmentedPolynomial.mass_twoPointRecentered_le _ v hv z hzn
      _ ≤ 2 / (Real.sqrt 2 * (T * Δ / Real.pi)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hden'
      _ = _ := by
        have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        field_simp
        nlinarith

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
