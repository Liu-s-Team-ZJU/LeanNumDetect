import RandSamp.MultidimensionalMultiClumpLowerSampling
import NumDetect.RandomClumpModel
import NumDetect.RandomCubeMUSIC

/-! The lower-only random VDM statement, in the manuscript's exact clump
model and unnormalized Vandermonde convention. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open LeanNumDetect.FiniteMatrixSampling LeanNumDetect.RandSamp
open LeanNumDetect.QuantitativeClumpSectionBounds
open scoped BigOperators

namespace LeanNumDetect.NumDetect
noncomputable section

/-- The coefficient in the full-cube lower estimate. Its dependencies are
exactly dimension and maximal clump size, followed by bandwidth and spacing. -/
def positiveCubeClumpLower (d nStar L : ℕ) (Δ : ℝ) : ℝ :=
  multidimensionalClumpOptimizedLowerConstant d nStar * ((L : ℝ) * Δ) ^ (nStar - 1)

theorem positiveCubeClumpLower_pos {d nStar L : ℕ}
    (hd : 1 ≤ d) (hStar : 0 < nStar) (hL : 0 < L) {Δ : ℝ} (hΔ : 0 < Δ) :
    0 < positiveCubeClumpLower d nStar L Δ := by
  exact mul_pos (multidimensionalClumpOptimizedLowerConstant_pos hd hStar)
    (pow_pos (mul_pos (Nat.cast_pos.mpr hL) hΔ) _)

/-- The squared lower coefficient has exactly the exponent displayed in
    the manuscript's signal and MUSIC noise conditions. -/
theorem positiveCubeClumpLower_sq {d nStar L : ℕ} (hStar : 1 ≤ nStar) (Δ : ℝ) :
    (positiveCubeClumpLower d nStar L Δ) ^ 2 =
      (multidimensionalClumpOptimizedLowerConstant d nStar) ^ 2 *
        ((L : ℝ) * Δ) ^ (2 * nStar - 2) := by
  have hexponent : (nStar - 1) * 2 = 2 * nStar - 2 := by omega
  simp only [positiveCubeClumpLower, mul_pow, ← pow_mul, hexponent]

/-- The normalized internal result follows from precisely the manuscript's
`(A,∞,τ,η,nStar)` clump predicate. Here `η` is separation and `ε` is failure. -/
theorem positiveCubeClumpVandermonde_normalized_lower_probability
    {d n nStar L A m : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n)
    {c0 C0 Csep : ℝ}
    (hsampling : QuantitativeMultiClumpLowerSamplingConclusion d n nStar c0 C0 Csep)
    (μ : AtomicMeasure d n) {τ η ρ ε : ℝ}
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hL : C0 ≤ (L : ℝ)) (hτ : τ ≤ c0 / (L : ℝ)) (hη : Csep / (L : ℝ) ≤ η)
    (hm : 1 ≤ m) (hmN : m ≤ (L + 1) ^ d)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hsample : (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log ((n : ℝ) / ε) ≤ (m : ℝ)) :
    1 - ε ≤ probability (fun W : FiniteSample (CubeFrequency d L) m =>
      Real.sqrt (1 - ρ) * positiveCubeClumpLower d nStar L
        (periodicMinimumL1Separation μ.node hn) ≤
      matrixSingularValue (cubeSampledVandermonde m μ.node W.val) (n - 1)) := by
  let P := angularClumpPartition hclumps
  have hgeom := angularClumpPartition_geometry μ hd hclumps hτ hη
  have hΔ := periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
  have hspacing := angularClumpPartition_l1SpacingLowerBound μ hn hclumps
  have h := hsampling L A m hL P μ.node
    (angularClumpPartition_hasMaxClumpSize hclumps) hgeom
    (periodicMinimumL1Separation μ.node hn) ρ ε hΔ hspacing hm hmN
    hρ0 hρ1 hε0 hε1 hsample
  simpa only [positiveCubeClumpLower, mul_assoc] using h

/-- Exact lower-only manuscript statement: the Vandermonde matrix is
unnormalized and the retained row count occurs only on the right. -/
def PositiveCubeClumpVandermondeConclusion (d n nStar : ℕ) (hn : 2 ≤ n)
    (c0 C0 Csep : ℝ) : Prop :=
  ∀ (L A m : ℕ) (x : Fin n → Point d) (hx : Function.Injective x) (τ η ρ ε : ℝ)
    (hclumps : IsAngularClumpStructure x A nStar τ η),
    C0 ≤ (L : ℝ) → τ ≤ c0 / (L : ℝ) → Csep / (L : ℝ) ≤ η →
    1 ≤ m → m ≤ (L + 1) ^ d → 0 < ρ → ρ < 1 → 0 < ε → ε < 1 →
    (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log ((n : ℝ) / ε) ≤ (m : ℝ) →
    1 - ε ≤ probability (fun W : FiniteSample (CubeFrequency d L) m =>
      Real.sqrt ((m : ℝ) * (1 - ρ)) * multidimensionalClumpOptimizedLowerConstant d nStar *
        ((L : ℝ) * periodicMinimumL1Separation x hn) ^ (nStar - 1) ≤
      matrixSingularValue (generalizedVandermonde (positiveCubeFrequency W) x) (n - 1))

/-- The node-only manuscript statement uses the same chosen thresholds as
    the normalized sampling theorem. Unit amplitudes are internal witnesses. -/
theorem positiveCubeClumpVandermonde_lower_of_sampling
    {d n nStar : ℕ} (hd : 1 ≤ d) (hStar : 2 ≤ nStar) (hsize : nStar ≤ n)
    {c0 C0 Csep : ℝ} (hC0 : (n : ℝ) ≤ C0)
    (hsampling : QuantitativeMultiClumpLowerSamplingConclusion d n nStar c0 C0 Csep) :
    PositiveCubeClumpVandermondeConclusion d n nStar (by omega) c0 C0 Csep := by
  intro L A m x hx τ η ρ ε hclumps hL hτ hη hm hmN hρ0 hρ1 hε0 hε1 hsample
  let μ : AtomicMeasure d n :=
    { amplitude := fun _ => 1
      node := x
      amplitude_ne_zero := fun _ => one_ne_zero
      node_injective := hx }
  have hn : 2 ≤ n := by omega
  have hL0 : 0 < L := by
    exact_mod_cast (Nat.cast_pos.mpr (show 0 < n by omega)).trans_le (hC0.trans hL)
  have hΔ := periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
  have hb := positiveCubeClumpLower_pos (nStar := nStar) hd (by omega) hL0 hΔ
  have hp := positiveCubeClumpVandermonde_normalized_lower_probability hd hn hsampling
    μ hclumps hL hτ hη hm hmN hρ0 hρ1 hε0 hε1 hsample
  apply hp.trans
  apply probability_mono
  intro W hW
  have h := unnormalizedCubeVandermonde_singular_lower (by omega) (by omega) W μ.node
    (mul_nonneg (Real.sqrt_nonneg _) hb.le) hW
  simpa only [Real.sqrt_mul (Nat.cast_nonneg m), positiveCubeClumpLower, mul_assoc] using h

/-- Exact unnormalized lower-only random VDM statement with geometry constants
    chosen before all fixed nodes and sampling parameters. -/
theorem positiveCubeClumpVandermonde_lower_highProbability
    (d : ℕ) (hd : 1 ≤ d) (n nStar : ℕ) (hStar : 2 ≤ nStar) (hsize : nStar ≤ n) :
    let hnStar0 : 0 < nStar := by omega
    let c0 := quantitativeClumpRadius d (n-nStar) nStar hnStar0
    let C0 := quantitativeClumpBandwidth d n nStar hnStar0
    let Csep := quantitativeClumpSeparation d n nStar hnStar0
    0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      PositiveCubeClumpVandermondeConclusion d n nStar (by omega) c0 C0 Csep := by
  dsimp only
  obtain ⟨hc0,hc01,hC0,_,hsampling⟩ :=
    multidimensionalMultiClump_lower_sampling_explicit d hd n nStar hStar hsize
  exact ⟨hc0,hc01,hC0,
    positiveCubeClumpVandermonde_lower_of_sampling hd hStar hsize hC0 hsampling⟩

end
end LeanNumDetect.NumDetect
