import RandSamp.MultidimensionalMultiClumpModel

/-! Collinear arithmetic clumps are admissible in every positive dimension.
Their periodic distances agree exactly with their ordinary arithmetic gaps
whenever the total width is at most π. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.RandSamp

noncomputable section

/-- Within a half-turn, the ordinary distance is the shortest winding. -/
theorem angularTorusDistance_eq_abs_sub_of_le_pi (x y : ℝ)
    (hshort : |x - y| ≤ Real.pi) : angularTorusDistance x y = |x - y| := by
  apply le_antisymm
  · simpa using angularTorusDistance_le_winding x y 0
  · apply (le_angularTorusDistance_iff x y |x-y|).2
    intro p
    by_cases hp : p = 0
    · simp [hp]
    · have hi : (1 : ℝ) ≤ |(p : ℝ)| := by
        by_cases hp0 : 0 < p
        · rw [abs_of_pos (by exact_mod_cast hp0)]
          exact_mod_cast (show 1 ≤ p by omega)
        · rw [abs_of_neg (by exact_mod_cast (show p < 0 by omega))]
          exact_mod_cast (show (1 : ℤ) ≤ -p by omega)
      have hw : 2 * Real.pi ≤ |2 * Real.pi * p| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
        nlinarith [Real.pi_pos]
      have ht := abs_sub (x - y + 2 * Real.pi * p) (x - y)
      rw [show x-y+2*Real.pi*p-(x-y)=2*Real.pi*p by ring] at ht
      linarith

/-- Equally spaced nodes along the first coordinate, with no assumptions on
any other coordinate or arrangement. -/
def arithmeticClumpNodes (d s : ℕ) (Δ : ℝ) : Fin s → Fin d → ℝ :=
  fun j r => if r.val = 0 then (j.val : ℝ) * Δ else 0

/-- The single clump consisting of all source indices. -/
def arithmeticClumpPartition (s : ℕ) (hs : 0 < s) : ClumpPartition s 1 where
  label := fun _ => 0
  surjective := by
    intro a
    refine ⟨⟨0, hs⟩, ?_⟩
    exact Subsingleton.elim _ _

@[simp] theorem arithmeticClumpPartition_size (s : ℕ) (hs : 0 < s) (a : Fin 1) :
    (arithmeticClumpPartition s hs).size a = s := by
  simp [ClumpPartition.size, ClumpPartition.members, arithmeticClumpPartition,
    Subsingleton.elim (0 : Fin 1) a]

theorem arithmeticClumpPartition_hasMaxClumpSize (s : ℕ) (hs : 0 < s) :
    HasMaxClumpSize (arithmeticClumpPartition s hs) s := by
  refine ⟨fun a => by simp, ⟨0, by simp⟩⟩

/-- Each arithmetic gap is no larger than the total width. -/
theorem arithmeticClump_gap_le_width {s : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (i j : Fin s) : |(i.val : ℝ) - j.val| * Δ ≤ ((s - 1 : ℕ) : ℝ) * Δ := by
  have hi : (i.val : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show i.val ≤ s - 1 by omega)
  have hj : (j.val : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show j.val ≤ s - 1 by omega)
  have hab : |(i.val : ℝ) - j.val| ≤ ((s - 1 : ℕ) : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [(Nat.cast_nonneg i.val : (0 : ℝ) ≤ i.val),
      (Nat.cast_nonneg j.val : (0 : ℝ) ≤ j.val)]
  exact mul_le_mul_of_nonneg_right hab hΔ

/-- Exact coordinatewise periodic distances of the arithmetic family. -/
theorem arithmeticClump_coordinate_distance {d s : ℕ} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hshort : ((s - 1 : ℕ) : ℝ) * Δ ≤ Real.pi)
    (i j : Fin s) (r : Fin d) :
    angularTorusDistance (arithmeticClumpNodes d s Δ i r)
      (arithmeticClumpNodes d s Δ j r) =
        if r.val = 0 then |(i.val : ℝ) - j.val| * Δ else 0 := by
  by_cases hr : r.val = 0
  · simp only [arithmeticClumpNodes, hr, if_true]
    rw [angularTorusDistance_eq_abs_sub_of_le_pi]
    · rw [← sub_mul, abs_mul, abs_of_nonneg hΔ]
    · rw [← sub_mul, abs_mul, abs_of_nonneg hΔ]
      exact (arithmeticClump_gap_le_width hΔ i j).trans hshort
  · simp [arithmeticClumpNodes, hr]

/-- The angular L∞ gap is exactly the ordinary arithmetic gap in any
positive dimension. -/
theorem arithmeticClump_distance {d s : ℕ} (hd : 1 ≤ d) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hshort : ((s - 1 : ℕ) : ℝ) * Δ ≤ Real.pi)
    (i j : Fin s) :
    multidimensionalAngularTorusDistance (arithmeticClumpNodes d s Δ i)
      (arithmeticClumpNodes d s Δ j) = |(i.val : ℝ) - j.val| * Δ := by
  apply le_antisymm
  · apply (multidimensionalAngularTorusDistance_le_iff hd _ _ _).2
    intro r
    rw [arithmeticClump_coordinate_distance hΔ hshort]
    split_ifs
    · exact le_refl _
    · positivity
  · have h := angularTorusDistance_le_multidimensional
      (arithmeticClumpNodes d s Δ i) (arithmeticClumpNodes d s Δ j)
      (⟨0, by omega⟩ : Fin d)
    simpa only [arithmeticClump_coordinate_distance hΔ hshort, if_true] using h

/-- Only the first coordinate contributes, so the angular L1 gap has the
same exact value as the angular L∞ gap. -/
theorem arithmeticClump_l1_distance {d s : ℕ} (hd : 1 ≤ d) {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hshort : ((s - 1 : ℕ) : ℝ) * Δ ≤ Real.pi)
    (i j : Fin s) :
    multidimensionalAngularTorusL1Distance (arithmeticClumpNodes d s Δ i)
      (arithmeticClumpNodes d s Δ j) = |(i.val : ℝ) - j.val| * Δ := by
  let r0 : Fin d := ⟨0, by omega⟩
  unfold multidimensionalAngularTorusL1Distance
  simp_rw [arithmeticClump_coordinate_distance hΔ hshort]
  rw [Finset.sum_eq_single r0]
  · simp [r0]
  · intro r _ hr
    have hv : r.val ≠ 0 := by
      intro h
      apply hr
      exact Fin.ext h
    simp [hv]
  · simp

/-- The step is attained by the first two sources in both periodic metrics,
so it is the exact internal minimum spacing. -/
theorem arithmeticClump_step_attained {d s : ℕ} (hd : 1 ≤ d) (hs : 2 ≤ s)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hshort : ((s - 1 : ℕ) : ℝ) * Δ ≤ Real.pi) :
    ∃ i j : Fin s, i ≠ j ∧
      multidimensionalAngularTorusDistance (arithmeticClumpNodes d s Δ i)
          (arithmeticClumpNodes d s Δ j) = Δ ∧
      multidimensionalAngularTorusL1Distance (arithmeticClumpNodes d s Δ i)
          (arithmeticClumpNodes d s Δ j) = Δ := by
  let i : Fin s := ⟨0, by omega⟩
  let j : Fin s := ⟨1, by omega⟩
  refine ⟨i, j, ?_, ?_, ?_⟩
  · intro h
    have hh := congrArg Fin.val h
    simp [i, j] at hh
  · simpa [i, j] using arithmeticClump_distance hd hΔ hshort i j
  · simpa [i, j] using arithmeticClump_l1_distance hd hΔ hshort i j

/-- Different source indices have at least one unit of arithmetic gap. -/
theorem arithmeticClump_index_gap_pos {s : ℕ} (i j : Fin s) (hij : i ≠ j) :
    0 < |(i.val : ℝ) - j.val| := by
  apply abs_pos.mpr
  intro h
  apply hij
  apply Fin.ext
  exact_mod_cast (sub_eq_zero.mp h)

/-- Different integral source indices differ by at least one. -/
theorem arithmeticClump_index_gap_ge_one {s : ℕ} (i j : Fin s) (hij : i ≠ j) :
    1 ≤ |(i.val : ℝ) - j.val| := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  by_cases hlt : i.val < j.val
  · rw [abs_of_neg (by exact_mod_cast (show (i.val : ℤ) - j.val < 0 by omega))]
    have h : (i.val : ℝ) + 1 ≤ j.val := by
      exact_mod_cast (show i.val + 1 ≤ j.val by omega)
    linarith
  · rw [abs_of_pos (by exact_mod_cast (show (i.val : ℤ) - j.val > 0 by omega))]
    have h : (j.val : ℝ) + 1 ≤ i.val := by
      exact_mod_cast (show j.val + 1 ≤ i.val by omega)
    linarith

/-- The same arithmetic step is a lower bound for both periodic metrics. -/
theorem arithmeticClump_spacing_lower {d s : ℕ} (hd : 1 ≤ d) (hs : 0 < s)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hshort : ((s - 1 : ℕ) : ℝ) * Δ ≤ Real.pi) :
    MultidimensionalClumpSpacingLowerBound (arithmeticClumpPartition s hs)
        (arithmeticClumpNodes d s Δ) Δ ∧
      MultidimensionalClumpL1SpacingLowerBound (arithmeticClumpPartition s hs)
        (arithmeticClumpNodes d s Δ) Δ := by
  constructor <;> intro i j hij _
  · rw [arithmeticClump_distance hd hΔ hshort]
    simpa using mul_le_mul_of_nonneg_right (arithmeticClump_index_gap_ge_one i j hij) hΔ
  · rw [arithmeticClump_l1_distance hd hΔ hshort]
    simpa using mul_le_mul_of_nonneg_right (arithmeticClump_index_gap_ge_one i j hij) hΔ

/-- All internal gaps are comparable with ratio `s-1`. -/
theorem arithmeticClump_comparableSpacing {d s : ℕ} (hd : 1 ≤ d) (hs : 0 < s)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hshort : ((s - 1 : ℕ) : ℝ) * Δ ≤ Real.pi) :
    ComparableMultidimensionalClumpSpacing (arithmeticClumpPartition s hs)
      (arithmeticClumpNodes d s Δ) Δ ((s - 1 : ℕ) : ℝ) := by
  intro i j hij _
  rw [arithmeticClump_distance hd hΔ hshort]
  constructor
  · simpa using mul_le_mul_of_nonneg_right (arithmeticClump_index_gap_ge_one i j hij) hΔ
  · exact arithmeticClump_gap_le_width hΔ i j

/-- The periodic source tuple is distinct for every positive arithmetic step. -/
theorem arithmeticClump_distinct {d s : ℕ} (hd : 1 ≤ d) {Δ : ℝ}
    (hΔ : 0 < Δ) (hshort : ((s - 1 : ℕ) : ℝ) * Δ ≤ Real.pi) :
    DistinctMultidimensionalAngularNodes (arithmeticClumpNodes d s Δ) := by
  intro i j hij
  rw [arithmeticClump_distance hd hΔ.le hshort]
  exact mul_pos (arithmeticClump_index_gap_pos i j hij) hΔ

/-- The complete arithmetic family lies in a single clump of the prescribed
Rayleigh-scale diameter. The separation requirement is vacuous. -/
theorem arithmeticClump_geometry {d s M : ℕ} (hd : 1 ≤ d) (hs : 0 < s)
    {Δ c0 C0 : ℝ} (hΔ : 0 < Δ) (hM : 0 < M)
    (hshort : ((s - 1 : ℕ) : ℝ) * Δ ≤ Real.pi)
    (hwidth : ((s - 1 : ℕ) : ℝ) * (M : ℝ) * Δ ≤ c0) :
    MultidimensionalMultiClumpGeometry M c0 C0 (arithmeticClumpNodes d s Δ)
      (arithmeticClumpPartition s hs) := by
  refine ⟨arithmeticClump_distinct hd hΔ hshort, ?_, ?_⟩
  · intro i j _
    rw [arithmeticClump_distance hd hΔ.le hshort]
    apply (arithmeticClump_gap_le_width hΔ.le i j).trans
    apply (le_div_iff₀ (by exact_mod_cast hM : (0 : ℝ) < M)).2
    nlinarith [hwidth]
  · intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))

/-- The arithmetic family also satisfies the original strict NumDetect
clump structure for every separation parameter above its positive width. -/
theorem arithmeticClump_structure {d s : ℕ} (hd : 1 ≤ d) (hs : 2 ≤ s)
    {Δ τ η : ℝ} (hΔ : 0 < Δ) (hτ : 0 < τ) (hτη : τ ≤ η)
    (hshort : ((s - 1 : ℕ) : ℝ) * Δ ≤ Real.pi)
    (hwidth : ((s - 1 : ℕ) : ℝ) * Δ ≤ τ) :
    MultidimensionalClumpStructure s τ η (arithmeticClumpNodes d s Δ)
      (arithmeticClumpPartition s (by omega)) := by
  refine ⟨hτ, hτη, arithmeticClumpPartition_hasMaxClumpSize s (by omega),
    arithmeticClump_distinct hd hΔ hshort, ?_, ?_⟩
  · intro i j _
    rw [arithmeticClump_distance hd hΔ.le hshort]
    exact (arithmeticClump_gap_le_width hΔ.le i j).trans hwidth
  · intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))

/-- For a diameter threshold at most one, the Rayleigh-width hypothesis
already puts the arithmetic family inside a half-turn. -/
theorem arithmeticClump_geometry_of_width {d s M : ℕ} (hd : 1 ≤ d) (hs : 0 < s)
    {Δ c0 C0 : ℝ} (hΔ : 0 < Δ) (hM : 0 < M) (hc0 : c0 ≤ 1)
    (hwidth : ((s - 1 : ℕ) : ℝ) * (M : ℝ) * Δ ≤ c0) :
    MultidimensionalMultiClumpGeometry M c0 C0 (arithmeticClumpNodes d s Δ)
      (arithmeticClumpPartition s hs) := by
  apply arithmeticClump_geometry hd hs hΔ hM _ hwidth
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hw0 : 0 ≤ ((s - 1 : ℕ) : ℝ) * Δ := by positivity
  have hwM := mul_le_mul_of_nonneg_left hMr hw0
  have hπ : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  nlinarith

end
end LeanNumDetect.RandSamp
