import MultiTuran.ConsecutiveWindow.ChartIntervals
import MultiTuran.Preliminaries.Translation
import MultiTuran.MultiClump.Lifting

/-! # A common short chart for arbitrary angular-torus nodes

Every coordinate cut uses a largest empty gap, including repeated coordinate
values. The resulting bound is closed, as required at equally spaced endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

theorem exists_translated_short_chart_one_dimensional {n : ℕ}
    (hn : 2 ≤ n) (y : Fin n → ℝ) :
    ∃ center : ℝ, ∃ winding : Fin n → ℤ,
      ∀ j, |y j - center - 2 * Real.pi * (winding j : ℝ)| ≤
        Real.pi - Real.pi / n := by
  classical
  let p : ℝ := 2 * Real.pi
  have hp : 0 < p := by dsimp [p]; positivity
  let initial (j : Fin n) : ℤ := ⌊y j / p⌋
  let x (j : Fin n) : ℝ := y j - p * (initial j : ℝ)
  have hzero (j : Fin n) : 0 ≤ x j := by
    have h := (le_div_iff₀ hp).mp (Int.floor_le (y j / p))
    dsimp [x, initial]
    nlinarith only [h]
  have hperiod (j : Fin n) : x j < p := by
    have h := (div_lt_iff₀ hp).mp (Int.lt_floor_add_one (y j / p))
    dsimp [x, initial]
    nlinarith only [h]
  obtain ⟨center, extra, he⟩ := exists_short_chart_of_bounded_points hp
    (show 0 < n by omega) x hzero hperiod
  refine ⟨center, fun j => initial j + extra j, ?_⟩
  intro j
  have hright : p / 2 - p / (2 * (n : ℝ)) = Real.pi - Real.pi / n := by
    dsimp [p]
    ring
  rw [hright] at he
  convert he j using 1
  congr 1
  dsimp [x, p]
  push_cast
  ring

/-- The chart is constructed internally; it is not a premise of the public
consecutive-window result. -/
theorem exists_translated_short_chart {d n : ℕ} (hn : 2 ≤ n)
    (Y : Fin n → Point d) :
    ∃ center : Point d, ∃ winding : Fin n → Fin d → ℤ,
      ∀ j q, |Y j q - center q - 2 * Real.pi * (winding j q : ℝ)| ≤
        Real.pi - Real.pi / n := by
  classical
  have hcoord (q : Fin d) : ∃ center : ℝ, ∃ winding : Fin n → ℤ,
      ∀ j, |Y j q - center - 2 * Real.pi * (winding j : ℝ)| ≤
        Real.pi - Real.pi / n :=
    exists_translated_short_chart_one_dimensional hn (fun j => Y j q)
  choose center winding hw using hcoord
  exact ⟨center, fun j q => winding q j, fun j q => hw q j⟩

def chartNodes {d n : ℕ} (Y : Fin n → Point d) (center : Point d)
    (winding : Fin n → Fin d → ℤ) : Fin n → Point d :=
  MultiClump.liftNodes (translateNodes Y center) winding

@[simp] theorem chartNodes_apply {d n : ℕ} (Y : Fin n → Point d)
    (center : Point d) (winding : Fin n → Fin d → ℤ) (j : Fin n) (q : Fin d) :
    chartNodes Y center winding j q =
      Y j q - center q - 2 * Real.pi * (winding j q : ℝ) := rfl

@[simp] theorem torusLInfDistance_chartNodes {d n : ℕ} (Y : Fin n → Point d)
    (center : Point d) (winding : Fin n → Fin d → ℤ) (i j : Fin n) :
    torusLInfDistance (chartNodes Y center winding i) (chartNodes Y center winding j) =
      torusLInfDistance (Y i) (Y j) := by
  rw [chartNodes, MultiClump.torusLInfDistance_liftNodes]
  exact torusLInfDistance_sub_common (Y i) (Y j) center

@[simp] theorem nodeSeparation_chartNodes {d n : ℕ} (Y : Fin n → Point d)
    (center : Point d) (winding : Fin n → Fin d → ℤ) :
    nodeSeparation (chartNodes Y center winding) = nodeSeparation Y := by
  simp only [nodeSeparation, torusLInfDistance_chartNodes]

@[simp] theorem nodeDiameter_chartNodes {d n : ℕ} (Y : Fin n → Point d)
    (center : Point d) (winding : Fin n → Fin d → ℤ) :
    nodeDiameter (chartNodes Y center winding) = nodeDiameter Y := by
  simp only [nodeDiameter, torusLInfDistance_chartNodes]

/-- All integer-frequency singular values survive the common translation
and the separate coordinate windings. -/
theorem vandermondeMatrix_singularValues_chartNodes {ι : Type*} [Fintype ι]
    {d n : ℕ} (frequency : ι → Fin d → ℤ) (Y : Fin n → Point d)
    (center : Point d) (winding : Fin n → Fin d → ℤ) :
    (vandermondeMatrix (fun k q => (frequency k q : ℝ))
      (chartNodes Y center winding)).toEuclideanLin.singularValues =
        (vandermondeMatrix (fun k q => (frequency k q : ℝ)) Y).toEuclideanLin.singularValues := by
  have hmatrix : vandermondeMatrix (fun k q => (frequency k q : ℝ))
      (chartNodes Y center winding) =
        vandermondeMatrix (fun k q => (frequency k q : ℝ)) (translateNodes Y center) := by
    funext k j
    exact MultiClump.integerFourierPhase_sub_winding (frequency k) (winding j)
      (translateNodes Y center j)
  rw [hmatrix]
  exact vandermondeMatrix_singularValues_translateNodes _ Y center

theorem matrixSingularValue_chartNodes {ι : Type*} [Fintype ι] {d n : ℕ}
    (frequency : ι → Fin d → ℤ) (Y : Fin n → Point d)
    (center : Point d) (winding : Fin n → Fin d → ℤ) (i : ℕ) :
    matrixSingularValue (vandermondeMatrix (fun k q => (frequency k q : ℝ))
      (chartNodes Y center winding)) i =
        matrixSingularValue (vandermondeMatrix (fun k q => (frequency k q : ℝ)) Y) i := by
  simp only [matrixSingularValue, vandermondeMatrix_singularValues_chartNodes]

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
