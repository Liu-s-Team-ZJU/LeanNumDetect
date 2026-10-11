import General.Fourier.CubeFrameThickness
import General.MatrixAnalysis.GreedyBasisBounds

/-! Fourier-cube constants and population inputs for the greedy-cycle proof. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect.CubeGreedyFrameBounds

open CubeFrameBasis CubeFrameThickness CubeShiftBounds ConnectedBasisBounds
open TranslatedBasisThickness FiniteMatrixSampling GreedyBasisBounds

noncomputable section

def cubeGreedyEnergy (d n : ℕ) : ℝ :=
  greedyBasisEnergy n (cubeFrameThreshold d n) (cubeFrameUpperConstant d n)

/-- The shift constant in the manuscript's closed form. -/
theorem comparisonConstant_closedForm (d n : ℕ) :
    cubeShiftComparisonConstant d n = (2 : ℝ) ^ (4 * d * n ^ 2) := by
  unfold cubeShiftComparisonConstant
  rw [← pow_mul]
  congr 1
  ring

/-- The basis recurrence has exactly the manuscript denominator `3 K M²`. -/
theorem cubeBasisCoefficient_succ (d n r : ℕ) :
    basisCoefficient (1 / cubeShiftComparisonConstant d n)
      (cubeFrameUpperConstant d n)
      (cubeShiftComparisonConstant d n * cubeFrameUpperConstant d n) (r + 1) =
    basisCoefficient (1 / cubeShiftComparisonConstant d n)
      (cubeFrameUpperConstant d n)
      (cubeShiftComparisonConstant d n * cubeFrameUpperConstant d n) r ^ 2 /
      (3 * cubeShiftComparisonConstant d n * cubeFrameUpperConstant d n ^ 2) := by
  rw [basisCoefficient]
  congr 1
  ring

theorem threshold_le_upperConstant {d n : ℕ} (hn : 0 < n) :
    cubeFrameThreshold d n ≤ cubeFrameUpperConstant d n := by
  let K := cubeShiftComparisonConstant d n
  let M := cubeFrameUpperConstant d n
  have hK : 0 < K := comparisonConstant_pos d n
  have hK1 : 1 ≤ K := comparisonConstant_one_le d n
  have hM : 0 < M := upperConstant_pos hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le hK1 (Real.one_le_sqrt.mpr hn1)
  have hKM1 : 1 ≤ K * M := one_le_mul_of_one_le_of_one_le hK1 hM1
  have hcM : 1 / K ≤ M := by
    apply (div_le_iff₀ hK).mpr
    nlinarith
  have hc : cubeFrameCoefficient d n ≤ M :=
    (basisCoefficient_le_initial (one_div_pos.mpr hK) hM hKM1 hcM (n - 1)).trans hcM
  change cubeFrameCoefficient d n / (2 * K) ≤ M
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

theorem cubeGreedyEnergy_pos {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    0 < cubeGreedyEnergy d n := by
  unfold cubeGreedyEnergy greedyBasisEnergy
  exact div_pos (pow_pos (threshold_pos hd hn) _)
    (pow_pos (mul_pos (by exact_mod_cast hn)
      (sq_pos_of_pos (upperConstant_pos hn))) _)

/-- Cube rows have the upper norm used in the Gram determinant estimate. -/
theorem cubeFrameRow_norm_le {d n L : ℕ} [NeZero d]
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L)
    (k : CubePoint d L) :
    ‖cubeFrameRow z P L k‖ ≤ cubeFrameUpperConstant d n :=
  (isotropicCubeRootRow_norm_bounds z P hP hwhite hz hn hL k).2

/-- The dimension-sensitive thickness count gives the acceptance probability
`(n-r)/(2n)` for a uniform row draw. -/
theorem cubeFrameRow_probability_far {d n L : ℕ} [NeZero d]
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L)
    (U : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    ((n - Module.finrank ℂ U : ℕ) : ℝ) / (2 * n) ≤
      probability (fun k : CubePoint d L =>
        FarFromSubspace (cubeFrameRow z P L k) U (cubeFrameThreshold d n)) := by
  classical
  let A := Nat.card {k : CubePoint d L //
    FarFromSubspace (cubeFrameRow z P L k) U (cubeFrameThreshold d n)}
  have hcard := cubeFrameRow_thickCard z P hP hwhite hz hn hL U
  have hcardR : ((n : ℝ) + 1) * (n - Module.finrank ℂ U : ℕ) * (L + 1 : ℝ) ^ d ≤
      2 * (n : ℝ) ^ 2 * A := by
    exact_mod_cast hcard
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hN : 0 < (L + 1 : ℝ) ^ d := by positivity
  have hprob : probability (fun k : CubePoint d L =>
      FarFromSubspace (cubeFrameRow z P L k) U (cubeFrameThreshold d n)) =
      (A : ℝ) / (L + 1 : ℝ) ^ d := by
    unfold probability
    simp only [A, Nat.card_eq_fintype_card, Fintype.card_subtype,
      card_cubePoint, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  rw [hprob]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ)) hN).mpr
  have hcod : 0 ≤ ((n - Module.finrank ℂ U : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ (A : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- The same acceptance probability written with real codimension. -/
theorem cubeFrameRow_probability_far_real {d n L : ℕ} [NeZero d]
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L)
    (U : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    ((n : ℝ) - Module.finrank ℂ U) / (2 * n) ≤
      probability (fun k : CubePoint d L =>
        FarFromSubspace (cubeFrameRow z P L k) U (cubeFrameThreshold d n)) := by
  have hdim : Module.finrank ℂ U ≤ n := by simpa using U.finrank_le
  simpa only [Nat.cast_sub hdim] using
    cubeFrameRow_probability_far z P hP hwhite hz hn hL U

end
end LeanNumDetect.CubeGreedyFrameBounds
