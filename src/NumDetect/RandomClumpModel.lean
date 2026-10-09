import NumDetect.MUSICPerturbation
import NumDetect.Segmented.ClumpBasics
import RandSamp.MultidimensionalMultiClumpModel

/-!
The manuscript's angular clump model, expressed in the exact partition and
torus metrics used by the random-cube Fourier estimates. The conversion uses
only reduced atomic measures and the angular representative convention; it
adds no comparability or arrangement conditions inside a clump.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open LeanNumDetect.RandSamp

namespace LeanNumDetect.NumDetect

noncomputable section

/-- On the angular fundamental domain the manuscript's minimum formula is
the winding-invariant angular distance used by the random Fourier model. -/
theorem periodicCoordinateDistance_eq_angularTorusDistance
    {u v : ℝ}
    (hu : -Real.pi < u ∧ u ≤ Real.pi)
    (hv : -Real.pi < v ∧ v ≤ Real.pi) :
    periodicCoordinateDistance u v = angularTorusDistance u v := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := angularTorusDistance_eq_winding u v
    rw [hp]
    simpa only [Int.cast_neg, mul_neg, sub_neg_eq_add] using
      periodicCoordinateDistance_le_integerTranslate hu hv (-p)
  · unfold periodicCoordinateDistance
    apply le_min
    · simpa using angularTorusDistance_le_winding u v 0
    · by_cases h : 0 ≤ u - v
      · have hturn : u - v - 2 * Real.pi ≤ 0 := by linarith
        have hbound := angularTorusDistance_le_winding u v (-1)
        simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one,
          ← sub_eq_add_neg, abs_of_nonpos hturn] at hbound
        rw [abs_of_nonneg h]
        linarith
      · have hnonpos : u - v ≤ 0 := le_of_not_ge h
        have hturn : 0 ≤ u - v + 2 * Real.pi := by linarith
        have hbound := angularTorusDistance_le_winding u v 1
        simp only [Int.cast_one, mul_one, abs_of_nonneg hturn] at hbound
        rw [abs_of_nonpos hnonpos]
        linarith

/-- Equality of the two periodic one-norm conventions on angular nodes. -/
theorem periodicL1Distance_eq_multidimensionalAngularTorusL1Distance
    {d : ℕ} {u v : Point d}
    (hu : InAngularCube u) (hv : InAngularCube v) :
    periodicL1Distance u v = multidimensionalAngularTorusL1Distance u v := by
  unfold periodicL1Distance multidimensionalAngularTorusL1Distance
  exact Finset.sum_congr rfl fun r _ =>
    periodicCoordinateDistance_eq_angularTorusDistance (hu r) (hv r)

/-- Equality of the norm and supremum formulations of periodic infinity
distance in every positive dimension. -/
theorem periodicLInfDistance_eq_multidimensionalAngularTorusDistance
    {d : ℕ} (hd : 1 ≤ d) {u v : Point d}
    (hu : InAngularCube u) (hv : InAngularCube v) :
    periodicLInfDistance u v = multidimensionalAngularTorusDistance u v := by
  apply le_antisymm
  · unfold periodicLInfDistance
    apply (pi_norm_le_iff_of_nonneg
      (multidimensionalAngularTorusDistance_nonneg hd u v)).2
    intro r
    rw [Real.norm_eq_abs,
      abs_of_nonneg (periodicCoordinateDistance_nonneg (hu r) (hv r)),
      periodicCoordinateDistance_eq_angularTorusDistance (hu r) (hv r)]
    exact angularTorusDistance_le_multidimensional u v r
  · obtain ⟨r, hr⟩ := multidimensionalAngularTorusDistance_attained hd u v
    rw [← hr, ← periodicCoordinateDistance_eq_angularTorusDistance (hu r) (hv r)]
    simpa only [periodicLInfDistance, Real.norm_eq_abs,
      abs_of_nonneg (periodicCoordinateDistance_nonneg (hu r) (hv r))] using
      norm_le_pi_norm (fun k => periodicCoordinateDistance (u k) (v k)) r

/-- Reduced atomic angular representatives are distinct on the product torus. -/
theorem AtomicMeasure.distinctMultidimensionalAngularNodes
    {d n : ℕ} (μ : AtomicMeasure d n)
    (hcube : ∀ j, InAngularCube (μ.node j)) :
    DistinctMultidimensionalAngularNodes μ.node := by
  classical
  intro i j hij
  have hne : μ.node i ≠ μ.node j := fun h => hij (μ.node_injective h)
  obtain ⟨r, hr⟩ : ∃ r, μ.node i r ≠ μ.node j r := by
    by_contra h
    apply hne
    funext r
    exact not_ne_iff.mp (not_exists.mp h r)
  have hpos := periodicCoordinateDistance_pos (hcube i r) (hcube j r) hr
  rw [periodicCoordinateDistance_eq_angularTorusDistance
    (hcube i r) (hcube j r)] at hpos
  exact hpos.trans_le (angularTorusDistance_le_multidimensional (μ.node i) (μ.node j) r)

/-- The nonempty partition already present in the manuscript's clump predicate. -/
def angularClumpPartition
    {d n A nStar : ℕ} {x : Fin n → Point d} {τ η : ℝ}
    (hclumps : IsAngularClumpStructure x A nStar τ η) : ClumpPartition n A where
  label := Classical.choose hclumps.2.2.2.2
  surjective := (Classical.choose_spec hclumps.2.2.2.2).1

/-- The partition conversion preserves every clump cardinality exactly. -/
theorem angularClumpPartition_size
    {d n A nStar : ℕ} {x : Fin n → Point d} {τ η : ℝ}
    (hclumps : IsAngularClumpStructure x A nStar τ η) (a : Fin A) :
    (angularClumpPartition hclumps).size a =
      (Finset.univ.filter fun j =>
        (Classical.choose hclumps.2.2.2.2) j = a).card := rfl

/-- The manuscript's maximum-size bound and its attainment are unchanged. -/
theorem angularClumpPartition_hasMaxClumpSize
    {d n A nStar : ℕ} {x : Fin n → Point d} {τ η : ℝ}
    (hclumps : IsAngularClumpStructure x A nStar τ η) :
    HasMaxClumpSize (angularClumpPartition hclumps) nStar := by
  exact ⟨(Classical.choose_spec hclumps.2.2.2.2).2.1,
    (Classical.choose_spec hclumps.2.2.2.2).2.2.1⟩

/-- Exact strict multiclump geometry for the random Fourier model. -/
theorem angularClumpPartition_structure
    {d n A nStar : ℕ} {τ η : ℝ}
    (μ : AtomicMeasure d n) (hd : 1 ≤ d)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η) :
    MultidimensionalClumpStructure nStar τ η μ.node (angularClumpPartition hclumps) := by
  have hcube := hclumps.2.2.2.1
  have hlabel := Classical.choose_spec hclumps.2.2.2.2
  refine ⟨hclumps.2.1, hclumps.2.2.1,
    angularClumpPartition_hasMaxClumpSize hclumps,
    μ.distinctMultidimensionalAngularNodes hcube, ?_, ?_⟩
  · intro i j hij
    rw [← periodicLInfDistance_eq_multidimensionalAngularTorusDistance hd (hcube i) (hcube j)]
    exact hlabel.2.2.2.1 i j hij
  · intro i j hij
    rw [← periodicLInfDistance_eq_multidimensionalAngularTorusDistance hd (hcube i) (hcube j)]
    exact hlabel.2.2.2.2 i j hij

/-- The scaled within- and between-clump assumptions of the random cube
estimate follow directly from the manuscript's strict clump structure. -/
theorem angularClumpPartition_geometry
    {d n A nStar L : ℕ} {τ η c0 C0 : ℝ}
    (μ : AtomicMeasure d n) (hd : 1 ≤ d)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hτ : τ ≤ c0 / (L : ℝ)) (hη : C0 / (L : ℝ) ≤ η) :
    MultidimensionalMultiClumpGeometry L c0 C0 μ.node (angularClumpPartition hclumps) :=
  (angularClumpPartition_structure μ hd hclumps).toGeometry hτ hη

/-- The global periodic minimum is a lower bound for every intraclump pair;
no upper spacing or distance-ratio assumption is introduced. -/
theorem angularClumpPartition_l1SpacingLowerBound
    {d n A nStar : ℕ} {τ η : ℝ}
    (μ : AtomicMeasure d n) (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η) :
    MultidimensionalClumpL1SpacingLowerBound (angularClumpPartition hclumps) μ.node
      (periodicMinimumL1Separation μ.node hn) := by
  intro i j hij _hlabel
  rw [← periodicL1Distance_eq_multidimensionalAngularTorusL1Distance
    (hclumps.2.2.2.1 i) (hclumps.2.2.2.1 j)]
  exact periodicMinimumL1Separation_le hn hij

/-- The random sampling size parameter is exactly the sum of the original
clump sizes to the power `2*d`. -/
theorem angularClumpPartition_sizePowerSum
    {d n A nStar : ℕ} {x : Fin n → Point d} {τ η : ℝ}
    (hclumps : IsAngularClumpStructure x A nStar τ η) :
    (angularClumpPartition hclumps).sizePowerSum d =
      ∑ a : Fin A,
        (Finset.univ.filter fun j =>
          (Classical.choose hclumps.2.2.2.2) j = a).card ^ (2 * d) := rfl

/-- A maximum clump size also gives the coarser explicit sampling parameter. -/
theorem angularClumpPartition_sizePowerSum_le
    {d n A nStar : ℕ} {x : Fin n → Point d} {τ η : ℝ}
    (hd : 1 ≤ d) (hclumps : IsAngularClumpStructure x A nStar τ η) :
    (angularClumpPartition hclumps).sizePowerSum d ≤ n * nStar ^ (2 * d - 1) :=
  (angularClumpPartition hclumps).sizePowerSum_le hd
    (angularClumpPartition_hasMaxClumpSize hclumps).1

end
end LeanNumDetect.NumDetect
