import RandSamp.MultidimensionalClumpSingularBounds
import RandSamp.MultidimensionalClumpPhase

/-! The largest clump supplies a tensor-box moment upper bound. Its
one-dimensional exponent is exactly the maximum clump size minus one. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect.RandSamp
noncomputable section

/-- Upper spectral coefficient; its dependence on the spacing ratio is
chosen before the bandwidth and source configuration. -/
def multidimensionalClumpUpperConstant (d nstar : ℕ) (K : ℝ) : ℝ :=
  Real.sqrt (nstar : ℝ) * (d : ℝ) * (3 : ℝ) ^ d * 2 *
    K ^ multidimensionalClumpUpperExponent d nstar /
      ((multidimensionalClumpUpperExponent d nstar).factorial : ℝ)

theorem multidimensionalClumpUpperConstant_pos {d nstar : ℕ}
    (hd : 1 ≤ d) (hnstar : 2 ≤ nstar) {K : ℝ} (hK : 1 ≤ K) :
    0 < multidimensionalClumpUpperConstant d nstar K := by
  unfold multidimensionalClumpUpperConstant
  positivity

/-- The concrete clump geometry and comparable spacings imply the box-moment
upper bound without any condition on the internal arrangement. -/
theorem cube_multiclump_singular_upper {d M n A nstar : ℕ}
    (hd : 1 ≤ d) (hn : 0 < n) (hnstar : 2 ≤ nstar) (hM : 0 < M)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A)
    (hmax : HasMaxClumpSize P nstar) {c0 C0 Δ K : ℝ}
    (hc0 : c0 ≤ 1) (hgeom : MultidimensionalMultiClumpGeometry M c0 C0 Y P)
    (hΔ : 0 < Δ) (hK : 1 ≤ K)
    (hspacing : ComparableMultidimensionalClumpSpacing P Y Δ K) :
    matrixSingularValue (cubeFullVandermonde M Y) (n - 1) ≤
      multidimensionalClumpUpperConstant d nstar K *
        ((M : ℝ) * Δ) ^ multidimensionalClumpUpperExponent d nstar := by
  classical
  obtain ⟨a, ha⟩ := hmax.2
  let eQ : Fin nstar ≃ ↥(P.members a) := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin, Fintype.card_coe, ClumpPartition.size] using ha.symm)
  let e : Fin nstar → Fin n := fun j => (eQ j).val
  have he : Function.Injective e := Subtype.val_injective.comp eQ.injective
  have hlabel (j : Fin nstar) : P.label (e j) = a :=
    (P.mem_members a (e j)).1 (eQ j).property
  let j0 : Fin nstar := ⟨0, by omega⟩
  choose p hp using fun (j : Fin nstar) (r : Fin d) =>
    angularTorusDistance_eq_winding (Y (e j) r) (Y (e j0) r)
  let offset : Fin nstar → Fin d → ℝ := fun j r =>
    Y (e j) r - Y (e j0) r + 2 * Real.pi * p j r
  have habs (j : Fin nstar) (r : Fin d) :
      |offset j r| = angularTorusDistance (Y (e j) r) (Y (e j0) r) := (hp j r).symm
  have hrep (j : Fin nstar) (r : Fin d) :
      Y (e j) r = offset j r + Y (e j0) r + 2 * Real.pi * ((-p j r : ℤ) : ℝ) := by
    dsimp [offset]
    push_cast
    ring
  have hB : 0 ≤ K * Δ := mul_nonneg (by linarith) hΔ.le
  have hoffset (j : Fin nstar) (r : Fin d) : |offset j r| ≤ K * Δ := by
    rw [habs]
    by_cases hj : j = j0
    · subst j
      simpa using hB
    · exact (angularTorusDistance_le_multidimensional _ _ r).trans
        (hspacing _ _ (fun h => hj (he h)) (by rw [hlabel, hlabel])).2
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hshort (j : Fin nstar) (r : Fin d) : (M : ℝ) * |offset j r| ≤ 1 := by
    rw [habs]
    have h := (angularTorusDistance_le_multidimensional _ _ r).trans
      (hgeom.within (e j) (e j0) (by rw [hlabel, hlabel]))
    calc
      _ ≤ (M : ℝ) * (c0 / (M : ℝ)) := mul_le_mul_of_nonneg_left h hMR.le
      _ = c0 := by field_simp
      _ ≤ 1 := hc0
  obtain ⟨u, hu, hb⟩ := exists_unit_short_cube_clump_upper
    (multidimensionalClumpUpperExponent_pos hd hnstar)
    (multidimensionalClumpUpperExponent_power_lt hd hnstar) offset hB hoffset hshort
  apply (cubeFullVandermonde_minimumSingularValue_le_subclump_signal hn Y e he u hu).trans
  rw [cubeFullVandermonde_norm_of_lifts (Y ∘ e) offset (Y (e j0))
    (fun j r => -p j r) hrep]
  calc
    _ ≤ (Real.sqrt (nstar : ℝ) * (d : ℝ) * (3 : ℝ) ^ d * 2 /
        ((multidimensionalClumpUpperExponent d nstar).factorial : ℝ)) *
          ((M : ℝ) * (K * Δ)) ^ multidimensionalClumpUpperExponent d nstar := hb
    _ = _ := by
      unfold multidimensionalClumpUpperConstant
      simp only [mul_pow]
      ring

end
end LeanNumDetect.RandSamp
