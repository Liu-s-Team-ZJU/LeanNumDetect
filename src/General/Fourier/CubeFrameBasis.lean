import General.Fourier.ConnectedCubeBasis
import General.Fourier.CubeShiftPaths
import General.Fourier.CubeTranslationBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open scoped BigOperators InnerProductSpace
open Matrix WithLp

namespace LeanNumDetect.CubeFrameBasis

open CubeShiftBounds ConnectedBasisBounds
noncomputable section

def cubeFramePathLength (d n : ℕ) : ℕ := (4 * n) * d

def cubeFrameUpperConstant (d n : ℕ) : ℝ :=
  cubeShiftComparisonConstant d n * Real.sqrt n

def cubeFrameCoefficient (d n : ℕ) : ℝ :=
  basisCoefficient (1 / cubeShiftComparisonConstant d n)
    (cubeFrameUpperConstant d n)
    (cubeShiftComparisonConstant d n * cubeFrameUpperConstant d n) (n - 1)

def cubeFrameThreshold (d n : ℕ) : ℝ :=
  cubeFrameCoefficient d n / (2 * cubeShiftComparisonConstant d n)

def cubeFrameRow {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (L : ℕ) (k : CubePoint d L) :
    EuclideanSpace ℂ (Fin n) :=
  isotropicCubeRootRow z P (L + 1) (fun r => (k r).val)

def cubeFrameCoarseShift {d n L : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (s : Fin d × Fin (L / (2 * n) + 1)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (coordinateShift z P s.1 s.2.val).toEuclideanLin.toContinuousLinearMap

theorem comparisonConstant_one_le (d n : ℕ) : 1 ≤ cubeShiftComparisonConstant d n := by
  unfold cubeShiftComparisonConstant
  exact one_le_pow₀ (one_le_pow₀ (by norm_num))

theorem comparisonConstant_pos (d n : ℕ) : 0 < cubeShiftComparisonConstant d n :=
  lt_of_lt_of_le zero_lt_one (comparisonConstant_one_le d n)

theorem upperConstant_pos {d n : ℕ} (hn : 0 < n) : 0 < cubeFrameUpperConstant d n := by
  unfold cubeFrameUpperConstant
  exact mul_pos (comparisonConstant_pos d n) (Real.sqrt_pos.2 (by exact_mod_cast hn))

theorem coefficient_pos {d n : ℕ} (_hd : 0 < d) (hn : 0 < n) :
    0 < cubeFrameCoefficient d n := by
  unfold cubeFrameCoefficient
  exact basisCoefficient_pos (one_div_pos.mpr (comparisonConstant_pos d n))
    (upperConstant_pos hn)
    (mul_pos (comparisonConstant_pos d n) (upperConstant_pos hn)) (n - 1)

theorem threshold_pos {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    0 < cubeFrameThreshold d n := by
  unfold cubeFrameThreshold
  exact div_pos (coefficient_pos hd hn)
    (mul_pos (by norm_num) (comparisonConstant_pos d n))

/-- The concrete cube-coordinate shifts satisfy the abstract connected-basis interface. -/
theorem cubeFrameRow_coordinate_shift {d n L : ℕ}
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (p : CubePoint d L) (l : Fin d) (q : Fin (L / (2 * n) + 1))
    (hadd : (p l).val + q.val ≤ L) :
    cubeFrameRow z P L (addCubeCoordinate p l q.val hadd) =
      cubeFrameCoarseShift (L := L) z P (l, q) (cubeFrameRow z P L p) := by
  have he : (fun r => (addCubeCoordinate p l q.val hadd r).val) =
      Function.update (fun r => (p r).val) l ((p l).val + q.val) := by
    funext r
    by_cases hr : r = l
    · subst r
      simp [addCubeCoordinate]
    · simp [addCubeCoordinate, hr]
  unfold cubeFrameRow
  rw [he, isotropicCubeRootRow_coordinate_shift z P hP]
  rfl

/-- Every cube row is reached by a uniformly bounded positive coarse-shift path. -/
theorem cubeFrameRow_shiftPath {d n L : ℕ} [NeZero d]
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L)
    (k : CubePoint d L) :
    ∃ path : BoundedShiftPath (cubeFrameCoarseShift (L := L) z P)
      (cubeFrameRow z P L (fun _ => 0)) (cubeFrameRow z P L k)
      (cubeFrameUpperConstant d n), path.length ≤ cubeFramePathLength d n := by
  classical
  let Q := L / (2 * n)
  let e := cubeFramePathLength d n
  have hb := coarseBudget_of_bandwidth hn hL
  have hk : ∀ r, (k r).val ≤ (4 * n) * Q := by
    intro r
    have hr := (k r).isLt
    exact (by omega : (k r).val ≤ L).trans hb.2.2
  let p := coordinatePath (4 * n) Q k
  have hstep : ∀ t, t < e → ∃ r : Fin d, ∃ q : ℕ, q ≤ Q ∧
      (fun s => (p (t + 1) s).val) = Function.update (fun s => (p t s).val) r
        ((p t r).val + q) := by
    intro t ht
    exact coordinatePath_step (4 * n) Q (by omega) k hk t ht
  choose r q hq hchange using hstep
  let direction : ℕ → Fin d × Fin (Q + 1) := fun t =>
    if ht : t < e then (r t ht, ⟨q t ht, by have := hq t ht; omega⟩) else default
  let path : BoundedShiftPath (cubeFrameCoarseShift (L := L) z P)
      (cubeFrameRow z P L (fun _ => 0)) (cubeFrameRow z P L k)
      (cubeFrameUpperConstant d n) := {
    length := e
    value := fun t => cubeFrameRow z P L (p t)
    direction := direction
    start_eq := by
      dsimp [p]
      rw [coordinatePath_zero _ _ _ (by omega)]
      rfl
    end_eq := by
      dsimp [p, e, cubeFramePathLength]
      rw [coordinatePath_end _ _ _ hk]
    norm_le := by
      intro t ht
      exact (isotropicCubeRootRow_norm_bounds z P hP hwhite hz hn hL (p t)).2
    step_eq := by
      intro t ht
      dsimp [direction]
      rw [dif_pos ht]
      dsimp [cubeFrameRow, cubeFrameCoarseShift]
      rw [hchange t ht]
      exact isotropicCubeRootRow_coordinate_shift z P hP (L + 1) _ _ _ }
  exact ⟨path, le_rfl⟩


/-- The concrete Fourier cube has a connected quantitative basis with constants
independent of the bandwidth and the frequencies. -/
theorem cubeFrameRow_connectedBasis {d n L : ℕ} [NeZero d]
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L) :
    Nonempty (CubeBasisPrefix d L (L / (2 * n)) n (cubeFrameRow z P L)
      (cubeFrameCoefficient d n)) := by
  let K := cubeShiftComparisonConstant d n
  let M := cubeFrameUpperConstant d n
  have hn1 : 1 ≤ n := by omega
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hK : 0 < K := comparisonConstant_pos d n
  have hK1 : 1 ≤ K := comparisonConstant_one_le d n
  have hM : 0 < M := upperConstant_pos hn
  have hsqrt : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnR
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le hK1 hsqrt
  have hKM : 1 ≤ K * M := one_le_mul_of_one_le_of_one_le hK1 hM1
  have hB : 2 ≤ (2 : ℝ) ^ n := by
    simpa using pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hn1
  have hc₀M : 1 / K ≤ M := (div_le_iff₀ hK).mpr (by nlinarith)
  have hbudget : n * (L / (2 * n)) ≤ L := by
    have hfull : 2 * n * (L / (2 * n)) ≤ L := by
      simpa only [Nat.mul_comm] using Nat.div_mul_le_self L (2 * n)
    exact (Nat.mul_le_mul_right (L / (2 * n)) (by omega : n ≤ 2 * n)).trans hfull
  have hzero : 1 / K ≤ ‖cubeFrameRow z P L (fun _ => 0)‖ := by
    calc
      1 / K ≤ Real.sqrt n / K := by gcongr
      _ ≤ ‖cubeFrameRow z P L (fun _ => 0)‖ :=
        (isotropicCubeRootRow_norm_bounds z P hP hwhite hz hn hL (fun _ => 0)).1
  have hiso : ∀ u : EuclideanSpace ℂ (Fin n),
      (∑ p : CubePoint d L, ‖inner ℂ u (cubeFrameRow z P L p)‖ ^ 2) =
        (Fintype.card (CubePoint d L) : ℝ) * ‖u‖ ^ 2 := by
    intro u
    calc
      _ = ∑ p : CubePoint d L, ‖inner ℂ (cubeFrameRow z P L p) u‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [norm_inner_symm]
      _ = _ := by
        simpa only [cubeFrameRow, Fintype.card_fin, card_cubePoint] using
          isotropicCubeRootRow_parseval z P (L + 1) hwhite u
  have hA : ∀ s x, ‖cubeFrameCoarseShift (L := L) z P s x‖ ≤ (2 : ℝ) ^ n * ‖x‖ := by
    intro s x
    have hq : s.2.val ≤ L / (2 * n) := by omega
    have hnq : n * s.2.val ≤ L + 1 :=
      (Nat.mul_le_mul_left n hq).trans (coarseBudget_of_bandwidth hn hL).2.1
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right
        (coordinateShift_norm_le z P hP (L + 1) hwhite s.1 (fun j => (hz j s.1).le) _ hnq)
        (norm_nonneg x))
  have hsize : ((2 : ℝ) ^ n) ^ cubeFramePathLength d n * M ≤ K * M := by
    change K * M ≤ K * M
    exact le_rfl
  exact exists_connected_cube_basis hn1 hbudget (cubeFrameRow z P L)
    (by simp) (one_div_pos.mpr hK) hM hKM hc₀M hB
    hzero (fun p => (isotropicCubeRootRow_norm_bounds z P hP hwhite hz hn hL p).2)
    hiso (cubeFrameCoarseShift (L := L) z P) hA (cubeFrameRow_coordinate_shift z P hP)
    (cubeFramePathLength d n) (cubeFrameRow_shiftPath z P hP hwhite hz hn hL) hsize


#print axioms cubeFrameRow_connectedBasis

end
end LeanNumDetect.CubeFrameBasis
