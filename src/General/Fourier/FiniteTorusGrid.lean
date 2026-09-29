import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! Explicit finite grids covering a real torus. The construction uses floor
indices after reducing each coordinate to the interval `[0, 2π)`. -/

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect

noncomputable section

/-- A uniform grid on a half-open interval approximates every point from below. -/
theorem exists_interval_grid_near {p x : ℝ} (hp : 0 < p) {n : ℕ} (hn : 0 < n)
    (hx0 : 0 ≤ x) (hxp : x < p) :
    ∃ j : Fin n, |x - p * (j : ℝ) / n| ≤ p / n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  let y := (n : ℝ) * x / p
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hyn : y < n := by
    dsimp [y]
    apply (div_lt_iff₀ hp).2
    nlinarith
  let j : Fin n := ⟨Nat.floor y, (Nat.floor_lt hy0).2 hyn⟩
  refine ⟨j, ?_⟩
  have he : x - p * (j : ℝ) / n = (p / n) * (y - (Nat.floor y : ℝ)) := by
    dsimp [j, y]
    field_simp
  have hfloor := Nat.floor_le hy0
  have hlt := Nat.lt_floor_add_one y
  have habs : |y - (Nat.floor y : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ p / n)]
  simpa using mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ p / n)

/-- The tensor grid with `n` equally spaced points in each angular coordinate. -/
def torusGridPoint {d n : ℕ} (j : Fin d → Fin n) (r : Fin d) : ℝ :=
  2 * Real.pi * (j r : ℝ) / n

/-- Coordinatewise reduction of a real vector to the standard angular period. -/
def torusWrap {d : ℕ} (t : Fin d → ℝ) (r : Fin d) : ℝ :=
  toIcoMod Real.two_pi_pos 0 (t r)

/-- A grid of spacing `2π/n` covers the torus in the coordinate-sum distance. -/
theorem exists_torusGridPoint_near_of_size {d n : ℕ} (hn : 0 < n)
    (t : Fin d → ℝ) :
    ∃ j : Fin d → Fin n,
      (∑ r, |torusWrap t r - torusGridPoint j r|) ≤ 2 * Real.pi * d / n := by
  have hc (r : Fin d) := exists_interval_grid_near Real.two_pi_pos hn
    (toIcoMod_mem_Ico' Real.two_pi_pos (t r)).1
    (toIcoMod_mem_Ico' Real.two_pi_pos (t r)).2
  choose j hj using hc
  refine ⟨j, ?_⟩
  calc
    _ ≤ ∑ _r : Fin d, 2 * Real.pi / n := Finset.sum_le_sum (fun r _ => hj r)
    _ = _ := by simp; ring

/-- Grid size for a torus net of coordinate-sum radius `ε/(4M)`. -/
def torusCoverSize (d M : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil (8 * Real.pi * d * M / ε)

/-- The chosen covering grid has at least one point per coordinate. -/
theorem torusCoverSize_pos {d M : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M)
    {ε : ℝ} (hε : 0 < ε) : 0 < torusCoverSize d M ε := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  apply Nat.one_le_ceil_iff.mpr
  positivity

/-- The tensor-grid cardinality obeys the explicit covering-number bound. -/
theorem torusCoverSize_pow_le {d M : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    (torusCoverSize d M ε : ℝ) ^ d ≤ (1 + 8 * Real.pi * d * M / ε) ^ d := by
  have ha : 0 ≤ 8 * Real.pi * d * M / ε := by positivity
  have h := (Nat.ceil_lt_add_one ha).le
  exact pow_le_pow_left₀ (by positivity) (by simpa [torusCoverSize, add_comm] using h) d

/-- The exact size of the tensor grid has the same real covering-number bound. -/
theorem torusGrid_card_le {d M : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    (Fintype.card (Fin d → Fin (torusCoverSize d M ε)) : ℝ) ≤
      (1 + 8 * Real.pi * d * M / ε) ^ d := by
  simpa using torusCoverSize_pow_le hd hM hε

/-- The explicit covering grid approximates every torus point within `ε/(4M)`
in the sum of absolute coordinate differences after wrapping. -/
theorem exists_torusGridPoint_near {d M : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M)
    {ε : ℝ} (hε : 0 < ε) (t : Fin d → ℝ) :
    ∃ j : Fin d → Fin (torusCoverSize d M ε),
      (∑ r, |torusWrap t r - torusGridPoint j r|) ≤ ε / (4 * M) := by
  have hn := torusCoverSize_pos hd hM hε
  obtain ⟨j, hj⟩ := exists_torusGridPoint_near_of_size hn t
  refine ⟨j, hj.trans ?_⟩
  have hnr : (0 : ℝ) < torusCoverSize d M ε := by exact_mod_cast hn
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hc : 8 * Real.pi * d * M ≤ (torusCoverSize d M ε : ℝ) * ε := by
    exact (div_le_iff₀ hε).mp (Nat.le_ceil (8 * Real.pi * d * M / ε))
  apply (div_le_div_iff₀ hnr (by positivity : (0 : ℝ) < 4 * M)).2
  nlinarith

end

end LeanNumDetect
