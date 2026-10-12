import NumDetect.Preliminaries.Basic

/-! Positivity of periodic distances and the minimum separation of angular nodes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Periodic coordinate distance is positive for distinct angular representatives. -/
theorem periodicCoordinateDistance_pos
    {u v : ℝ}
    (hu : -Real.pi < u ∧ u ≤ Real.pi)
    (hv : -Real.pi < v ∧ v ≤ Real.pi)
    (hne : u ≠ v) :
    0 < periodicCoordinateDistance u v := by
  unfold periodicCoordinateDistance
  rw [lt_min_iff]
  constructor
  · exact abs_pos.mpr (sub_ne_zero.mpr hne)
  · rw [sub_pos]
    rw [abs_lt]
    constructor <;> nlinarith [Real.pi_pos]

/-- Periodic coordinate distance is nonnegative on the angular cube. -/
theorem periodicCoordinateDistance_nonneg
    {u v : ℝ}
    (hu : -Real.pi < u ∧ u ≤ Real.pi)
    (hv : -Real.pi < v ∧ v ≤ Real.pi) :
    0 ≤ periodicCoordinateDistance u v := by
  by_cases h : u = v
  · subst v
    simp [periodicCoordinateDistance, Real.pi_pos.le]
  · exact (periodicCoordinateDistance_pos hu hv h).le

/-- Distinct angular representatives have positive periodic `ℓ¹` distance. -/
theorem periodicL1Distance_pos_of_ne
    {d : ℕ} {u v : Point d}
    (hu : InAngularCube u) (hv : InAngularCube v) (hne : u ≠ v) :
    0 < periodicL1Distance u v := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, u k ≠ v k := by
    by_contra h
    apply hne
    funext j
    exact not_ne_iff.mp (not_exists.mp h j)
  unfold periodicL1Distance
  exact Finset.sum_pos'
    (fun j _ => periodicCoordinateDistance_nonneg (hu j) (hv j))
    ⟨k, Finset.mem_univ k, periodicCoordinateDistance_pos (hu k) (hv k) hk⟩

/-- A reduced family in the angular cube has positive minimum periodic separation. -/
theorem periodicMinimumL1Separation_pos
    {d n : ℕ} (μ : AtomicMeasure d n) (hn : 2 ≤ n)
    (hcube : ∀ j, InAngularCube (μ.node j)) :
    0 < periodicMinimumL1Separation μ.node hn := by
  rw [periodicMinimumL1Separation, minimumOverDistinctPairs,
    Finset.lt_inf'_iff]
  intro ij hij
  have hne : ij.1 ≠ ij.2 := by
    simpa [distinctPairs] using hij
  exact periodicL1Distance_pos_of_ne (hcube ij.1) (hcube ij.2)
    (fun h => hne (μ.node_injective h))

end

end NumDetect
end LeanNumDetect
