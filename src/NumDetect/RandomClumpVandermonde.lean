import RandSamp.CubeGreedyLowerSampling
import RandSamp.MultidimensionalClumpSingularBounds
import NumDetect.LiCubeClumpBounds
import NumDetect.RandomClumpModel
import NumDetect.RandomCubeMUSIC

/-! The manuscript's lower-only random VDM theorem under Li's cube geometry.
The geometric frame thickness, greedy basis process, and scalar-potential
sampling bound are proved, without a leverage or norming hypothesis. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open LeanNumDetect.FiniteMatrixSampling LeanNumDetect.RandSamp
open scoped BigOperators

namespace LeanNumDetect.NumDetect
noncomputable section

/-- Exact manuscript coefficient; its only dependencies are d, n, nStar, β. -/
def positiveCubeClumpCoefficient (d n nStar : ℕ) (β : ℝ) : ℝ :=
  cubeGreedySamplingCoefficient d n * liCubeClumpUniformCoefficient d n nStar β

/-- Bandwidth and spacing occur only in the final displayed power. -/
def positiveCubeClumpLower (d n nStar L : ℕ) (β Δ : ℝ) : ℝ :=
  positiveCubeClumpCoefficient d n nStar β * ((L : ℝ) * Δ) ^ (nStar - 1)

theorem positiveCubeClumpCoefficient_pos {d n nStar : ℕ} {β : ℝ}
    (hd : 1 ≤ d) (hn : 0 < n) (hStar : 0 < nStar)
    (hβ : 1 / (2 * Real.log 2) < β) :
    0 < positiveCubeClumpCoefficient d n nStar β := by
  unfold positiveCubeClumpCoefficient
  exact mul_pos (cubeGreedySamplingCoefficient_pos (by omega : 0 < d) hn)
    (liCubeClumpUniformCoefficient_pos hn hStar hβ)

theorem positiveCubeClumpLower_pos {d n nStar L : ℕ}
    (hd : 1 ≤ d) (hn : 0 < n) (hStar : 0 < nStar) (hL : 0 < L)
    {β Δ : ℝ} (hβ : 1 / (2 * Real.log 2) < β) (hΔ : 0 < Δ) :
    0 < positiveCubeClumpLower d n nStar L β Δ := by
  exact mul_pos (positiveCubeClumpCoefficient_pos hd hn hStar hβ)
    (pow_pos (mul_pos (Nat.cast_pos.mpr hL) hΔ) _)

/-- Squaring preserves precisely the manuscript's noise-condition exponent. -/
theorem positiveCubeClumpLower_sq {d n nStar L : ℕ}
    (hStar : 1 ≤ nStar) (β Δ : ℝ) :
    (positiveCubeClumpLower d n nStar L β Δ) ^ 2 =
      (positiveCubeClumpCoefficient d n nStar β) ^ 2 *
        ((L : ℝ) * Δ) ^ (2 * nStar - 2) := by
  have hexponent : (nStar - 1) * 2 = 2 * nStar - 2 := by omega
  simp only [positiveCubeClumpLower, mul_pow, ← pow_mul, hexponent]

/-- Uniform row sampling under the original angular clump predicate and Li's
simple cube parameters. Every sampling prerequisite is derived in the proof. -/
theorem positiveCubeClumpVandermonde_normalized_lower_probability
    {d n nStar L A m : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n)
    (μ : AtomicMeasure d n) {τ η β ε : ℝ}
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hgeom : LiCubeClumpGeometry μ A nStar L τ η β hn)
    (hm : 1 ≤ m) (hmN : m ≤ (L + 1) ^ d)
    (hε0 : 0 < ε) (_hε1 : ε < 1)
    (hsample : 3 * (n : ℝ) * Real.log ((n : ℝ) / ε) ≤ (m : ℝ)) :
    1 - ε ≤ probability (fun W : FiniteSample (CubeFrequency d L) m =>
      positiveCubeClumpLower d n nStar L β
        (periodicMinimumL1Separation μ.node hn) ≤
      matrixSingularValue (cubeSampledVandermonde m μ.node W.val) (n - 1)) := by
  have hL : 8 * n ≤ L := hgeom.2.1
  have hG := cube_fullGram_posDef_of_distinct hd (by omega : n ≤ L) μ.node
    (μ.distinctMultidimensionalAngularNodes hclumps.2.2.2.1)
  have hp := cubeFixedSupport_greedy_minSingularValue_probability
    (d := d) (n := n) (m := m) (by omega : 0 < d) (by omega : 0 < n)
    hL hm hmN μ.node hG hε0 hsample
  have hfull := liCubeClumpVandermonde_normalized_uniform_lower μ hd hn hgeom
  apply hp.trans
  apply probability_mono
  intro W hW
  have h := mul_le_mul_of_nonneg_left hfull
    (cubeGreedySamplingCoefficient_pos (by omega : 0 < d) (by omega : 0 < n)).le
  have hl : positiveCubeClumpLower d n nStar L β
      (periodicMinimumL1Separation μ.node hn) ≤
      cubeGreedySamplingCoefficient d n *
        matrixSingularValue (cubeFullVandermonde L μ.node) (n - 1) := by
    simpa only [positiveCubeClumpLower, positiveCubeClumpCoefficient, mul_assoc] using h
  exact hl.trans hW

/-- Unnormalized manuscript statement: the lower bound scales by sqrt(m). -/
theorem positiveCubeClumpVandermonde_unnormalized_lower_probability
    {d n nStar L A m : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n)
    (μ : AtomicMeasure d n) {τ η β ε : ℝ}
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hgeom : LiCubeClumpGeometry μ A nStar L τ η β hn)
    (hm : 1 ≤ m) (hmN : m ≤ (L + 1) ^ d)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hsample : 3 * (n : ℝ) * Real.log ((n : ℝ) / ε) ≤ (m : ℝ)) :
    1 - ε ≤ probability (fun W : FiniteSample (CubeFrequency d L) m =>
      Real.sqrt (m : ℝ) * positiveCubeClumpCoefficient d n nStar β *
        ((L : ℝ) * periodicMinimumL1Separation μ.node hn) ^ (nStar - 1) ≤
      matrixSingularValue (generalizedVandermonde (positiveCubeFrequency W) μ.node) (n - 1)) := by
  have hL0 : 0 < L := by have h := hgeom.2.1; omega
  have hΔ := periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
  have hStar : 0 < nStar := by have h := hclumps.1; omega
  have hb := positiveCubeClumpLower_pos hd (by omega : 0 < n) hStar hL0
    hgeom.2.2.2.1 hΔ
  have hp := positiveCubeClumpVandermonde_normalized_lower_probability hd hn μ
    hclumps hgeom hm hmN hε0 hε1 hsample
  apply hp.trans
  apply probability_mono
  intro W hW
  have h := unnormalizedCubeVandermonde_singular_lower (by omega) (by omega) W μ.node
    hb.le hW
  simpa only [positiveCubeClumpLower, mul_assoc] using h

/-- Node-only theorem with exactly the manuscript's geometric and sampling
hypotheses. Unit amplitudes are internal witnesses, not assumptions. -/
theorem positiveCubeClumpVandermonde_lower_highProbability
    {d n nStar L A m : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n)
    (x : Fin n → Point d) (hx : Function.Injective x) {τ η β ε : ℝ}
    (hclumps : IsAngularClumpStructure x A nStar τ η)
    (hEven : Even L) (hL : 8 * n ≤ L)
    (hβ : 1 / (2 * Real.log 2) < β)
    (hτlower : 8 * Real.pi * β * d * nStar / L ≤ τ)
    (hτupper : τ ≤ Real.pi / (2 * d))
    (hscale : periodicMinimumL1Separation x hn ≤ 4 * Real.pi * nStar / L)
    (hm : 1 ≤ m) (hmN : m ≤ (L + 1) ^ d)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hsample : 3 * (n : ℝ) * Real.log ((n : ℝ) / ε) ≤ (m : ℝ)) :
    1 - ε ≤ probability (fun W : FiniteSample (CubeFrequency d L) m =>
      Real.sqrt (m : ℝ) * positiveCubeClumpCoefficient d n nStar β *
        ((L : ℝ) * periodicMinimumL1Separation x hn) ^ (nStar - 1) ≤
      matrixSingularValue (generalizedVandermonde (positiveCubeFrequency W) x) (n - 1)) := by
  let μ : AtomicMeasure d n := {
    amplitude := fun _ => 1
    node := x
    amplitude_ne_zero := fun _ => one_ne_zero
    node_injective := hx }
  have hgeom : LiCubeClumpGeometry μ A nStar L τ η β hn :=
    ⟨hEven, hL, hclumps, hβ, hτlower, hτupper, hscale⟩
  exact positiveCubeClumpVandermonde_unnormalized_lower_probability hd hn μ
    hclumps hgeom hm hmN hε0 hε1 hsample

end
end LeanNumDetect.NumDetect
