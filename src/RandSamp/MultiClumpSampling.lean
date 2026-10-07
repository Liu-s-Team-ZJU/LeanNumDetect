import RandSamp.MultidimensionalMultiClumpSampling
import RandSamp.FullVandermondeRank

/-!
# Exact multiclump sampling statement and deterministic-to-random transfer

The proposition `MultiClumpSamplingStatement` is manuscript
`thm:multi-clump-random-sampling`, with exactly its outer quantifier order.
The statements are unchanged; the sampling transfer and the complete theorem
are exact dimension-one corollaries of the frequency-cube theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The manuscript's absolute sampling constant from radius `1024 Σ n_a²`. -/
def multiClumpSamplingConstant : ℝ := 3072

theorem multiClumpSamplingConstant_pos : 0 < multiClumpSamplingConstant := by
  unfold multiClumpSamplingConstant
  positivity

/-- The same sample event includes the Gram order, every singular value,
and the smallest-singular-value bounds for all admissible spacing parameters. -/
def MultiClumpSuccess {M n A m : ℕ} (Y : Fin n → ℝ) (P : ClumpPartition n A)
    (nstar : ℕ) (lower upper : ℝ → ℝ) (ρ : ℝ)
    (Ω : Sample (M + 1) m) : Prop :=
  RelativeGramEvent Y ρ Ω ∧ AllSingularValueEvent Y ρ Ω ∧
    ∀ K : ℝ, 1 ≤ K → ∀ Δ : ℝ, 0 < Δ → ComparableClumpSpacing P Y Δ K →
      lower K * Real.sqrt (1 - ρ) * ((M : ℝ) * Δ) ^ (nstar - 1) ≤
        matrixSingularValue (sampledVandermonde m Y Ω.val) (n - 1) ∧
      matrixSingularValue (sampledVandermonde m Y Ω.val) (n - 1) ≤
        upper K * Real.sqrt (1 + ρ) * ((M : ℝ) * Δ) ^ (nstar - 1)

/-- Sampling conclusion for specified constants. `Y` is fixed outside the
probability event; `K` and `Δ` vary inside the same event. The functions of
`K` are chosen before `M`, the partition, nodes, and sampling parameters. -/
def MultiClumpSamplingConclusion (C : ℝ) (n nstar : ℕ) (c0 C0 : ℝ) : Prop :=
  ∃ lower upper : ℝ → ℝ,
    (∀ K : ℝ, 1 ≤ K → 0 < lower K ∧ 0 < upper K) ∧
    ∀ (M : ℕ), C0 ≤ (M : ℝ) →
      ∀ (A : ℕ) (P : ClumpPartition n A) (Y : Fin n → ℝ),
        HasMaxClumpSize P nstar → MultiClumpGeometry M c0 C0 Y P →
        ∀ (m : ℕ) (ρ δ : ℝ), 1 ≤ m → m ≤ M + 1 →
          0 < ρ → ρ < 1 → 0 < δ → δ < 1 →
          C / ρ ^ 2 * (P.sizeSquareSum : ℝ) * Real.log (2 * (n : ℝ) / δ) ≤ (m : ℝ) →
          1 - δ ≤ probability (fun Ω : Sample (M + 1) m =>
            MultiClumpSuccess Y P nstar lower upper ρ Ω)

/-- Exact proposed main theorem as a proposition, including the absolute
constant before both source cardinalities and geometry thresholds. Its proof
is `multiClump_sampling_statement` in `RandSamp.MultiClumpTheorem`. -/
def MultiClumpSamplingStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n nstar : ℕ), 2 ≤ nstar → nstar ≤ n →
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      MultiClumpSamplingConclusion C n nstar c0 C0

/-- The two deterministic estimates needed to close the proposed main
theorem. They have no dependence on sampling cardinality or probabilities. -/
def MultiClumpDeterministicControl (n nstar : ℕ) (c0 C0 : ℝ) : Prop :=
  ∃ lower upper : ℝ → ℝ,
    (∀ K : ℝ, 1 ≤ K → 0 < lower K ∧ 0 < upper K) ∧
    ∀ (M : ℕ), C0 ≤ (M : ℝ) →
      ∀ (A : ℕ) (P : ClumpPartition n A) (Y : Fin n → ℝ),
        HasMaxClumpSize P nstar → MultiClumpGeometry M c0 C0 Y P →
        (∀ (k : Fin (M + 1)) (z : EuclideanSpace ℂ (Fin n)),
          fourierRowEnergy Y k.val (ofLp z) ≤
            (1024 * (P.sizeSquareSum : ℝ)) *
              FiniteMatrixSampling.quadratic (fullGram M Y) z) ∧
        (∀ K : ℝ, 1 ≤ K → ∀ Δ : ℝ, 0 < Δ → ComparableClumpSpacing P Y Δ K →
          lower K * ((M : ℝ) * Δ) ^ (nstar - 1) ≤
            matrixSingularValue (fullVandermonde M Y) (n - 1) ∧
          matrixSingularValue (fullVandermonde M Y) (n - 1) ≤
            upper K * ((M : ℝ) * Δ) ^ (nstar - 1))

/-- Once the deterministic spectral bounds hold, the complete success event
is exactly the relative Gram event. In particular it does not acquire any
additional dependence on the partition or the spacing parameters. -/
theorem multiClumpSuccess_iff_relativeGram {M n A m nstar : ℕ}
    (hn : 0 < n) (P : ClumpPartition n A) (Y : Fin n → ℝ)
    (lower upper : ℝ → ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hfull : ∀ K : ℝ, 1 ≤ K → ∀ Δ : ℝ, 0 < Δ → ComparableClumpSpacing P Y Δ K →
      lower K * ((M : ℝ) * Δ) ^ (nstar - 1) ≤
        matrixSingularValue (fullVandermonde M Y) (n - 1) ∧
      matrixSingularValue (fullVandermonde M Y) (n - 1) ≤
        upper K * ((M : ℝ) * Δ) ^ (nstar - 1))
    (Ω : Sample (M + 1) m) :
    MultiClumpSuccess Y P nstar lower upper ρ Ω ↔ RelativeGramEvent Y ρ Ω := by
  constructor
  · exact fun h => h.1
  · intro hrelative
    have hall := allSingularValueEvent_of_relativeGramEvent Y hρ0 hρ1 Ω hrelative
    refine ⟨hrelative, hall, ?_⟩
    intro K hK Δ hΔ hspacing
    have hf := hfull K hK Δ hΔ hspacing
    have hs := hall (⟨n - 1, by omega⟩ : Fin n)
    constructor
    · calc
        lower K * Real.sqrt (1 - ρ) * ((M : ℝ) * Δ) ^ (nstar - 1) =
            Real.sqrt (1 - ρ) * (lower K * ((M : ℝ) * Δ) ^ (nstar - 1)) := by ring
        _ ≤ Real.sqrt (1 - ρ) * matrixSingularValue (fullVandermonde M Y) (n - 1) :=
          mul_le_mul_of_nonneg_left hf.1 (Real.sqrt_nonneg _)
        _ ≤ _ := hs.1
    · calc
        _ ≤ Real.sqrt (1 + ρ) * matrixSingularValue (fullVandermonde M Y) (n - 1) := hs.2
        _ ≤ Real.sqrt (1 + ρ) * (upper K * ((M : ℝ) * Δ) ^ (nstar - 1)) :=
          mul_le_mul_of_nonneg_left hf.2 (Real.sqrt_nonneg _)
        _ = _ := by ring

/-- The dimension-one cube event is exactly the original event, including
all spacing parameters and both spectral exponents. -/
@[simp] theorem multidimensionalMultiClumpSuccess_one {M n A m nstar : ℕ}
    (Y : Fin n → ℝ) (P : ClumpPartition n A) (lower upper : ℝ → ℝ) (ρ : ℝ)
    (Ω : Sample (M + 1) m) :
    MultidimensionalMultiClumpSuccess (fun j (_ : Fin 1) => Y j) P nstar lower upper ρ
      (finiteSampleEquiv (Equiv.funUnique (Fin 1) (Fin (M + 1))).symm m Ω) ↔
        MultiClumpSuccess Y P nstar lower upper ρ Ω := by
  simp only [MultidimensionalMultiClumpSuccess, MultiClumpSuccess,
    cubeRelativeGramEvent_one, cubeAllSingularValueEvent_one,
    comparableMultidimensionalClumpSpacing_one, multidimensionalClumpUpperExponent_one,
    cubeSampledVandermonde_one_singularValue]

/-- Dimension-one deterministic control specializes to the original row and
spectral estimates, with exactly the original constants. -/
theorem multiClumpDeterministicControl_of_multidimensional_one {n nstar : ℕ}
    {c0 C0 : ℝ}
    (h : MultidimensionalMultiClumpDeterministicControl 1 n nstar c0 C0) :
    MultiClumpDeterministicControl n nstar c0 C0 := by
  obtain ⟨lower, upper, hpos, hdet⟩ := h
  refine ⟨lower, upper, hpos, ?_⟩
  intro M hM A P Y hmax hgeom
  obtain ⟨_, hrow, hfull⟩ := hdet M hM A P (fun j (_ : Fin 1) => Y j) hmax
    ((multidimensionalMultiClumpGeometry_one c0 C0 Y P).2 hgeom)
  constructor
  · intro k z
    simpa [cubeFourierRowEnergy, fourierRowEnergy,
      multidimensionalMultiClumpLeverageConstant, ClumpPartition.sizePowerSum_one] using
      hrow (fun _ : Fin 1 => k) z
  · simpa only [comparableMultidimensionalClumpSpacing_one,
      cubeFullVandermonde_one_singularValue, multidimensionalClumpUpperExponent_one] using hfull

/-- The original sampling conclusion is the dimension-one cube conclusion
under the exact bijection between actual frequency subsets. -/
theorem multiClumpSamplingConclusion_of_multidimensional_one {C : ℝ} {n nstar : ℕ}
    {c0 C0 : ℝ}
    (h : MultidimensionalMultiClumpSamplingConclusion C 1 n nstar c0 C0) :
    MultiClumpSamplingConclusion C n nstar c0 C0 := by
  obtain ⟨lower, upper, hpos, hsample⟩ := h
  refine ⟨lower, upper, hpos, ?_⟩
  intro M hM A P Y hmax hgeom m ρ δ hm hmM hρ0 hρ1 hδ0 hδ1 hrate
  have hcube := hsample M hM A P (fun j (_ : Fin 1) => Y j) hmax
    ((multidimensionalMultiClumpGeometry_one c0 C0 Y P).2 hgeom) m ρ δ hm
    (by simpa using hmM) hρ0 hρ1 hδ0 hδ1
    (by simpa only [ClumpPartition.sizePowerSum_one] using hrate)
  rw [← probability_comp_equiv
    (finiteSampleEquiv (Equiv.funUnique (Fin 1) (Fin (M + 1))).symm m)
    (MultidimensionalMultiClumpSuccess (fun j (_ : Fin 1) => Y j) P nstar lower upper ρ)]
    at hcube
  simpa only [multidimensionalMultiClumpSuccess_one] using hcube

/-- Original deterministic data can be viewed as dimension-one cube data.
The positive-definiteness field follows from the unchanged angular distinctness
and bandwidth assumptions. -/
theorem multidimensionalMultiClumpDeterministicControl_one_of_original {n nstar : ℕ}
    {c0 C0 : ℝ} (hC0 : (n : ℝ) ≤ C0)
    (h : MultiClumpDeterministicControl n nstar c0 C0) :
    MultidimensionalMultiClumpDeterministicControl 1 n nstar c0 C0 := by
  obtain ⟨lower, upper, hpos, hdet⟩ := h
  refine ⟨lower, upper, hpos, ?_⟩
  intro M hM A P Y hmax hgeom
  let y : Fin n → ℝ := fun j => Y j 0
  have hY : Y = (fun j (_ : Fin 1) => y j) := by
    funext j r
    exact congrArg (Y j) (Subsingleton.elim r 0)
  rw [hY] at hgeom ⊢
  have hg := (multidimensionalMultiClumpGeometry_one c0 C0 y P).1 hgeom
  obtain ⟨hrow, hfull⟩ := hdet M hM A P y hmax hg
  have hnM : n ≤ M + 1 := by
    have : (n : ℝ) ≤ M := hC0.trans hM
    have : n ≤ M := by exact_mod_cast this
    omega
  refine ⟨?_, ?_, ?_⟩
  · simpa only [cubeFullGram_one] using angularDistinct_fullGram_posDef hnM y hg.distinct
  · intro k z
    simpa [cubeFourierRowEnergy, fourierRowEnergy,
      multidimensionalMultiClumpLeverageConstant, ClumpPartition.sizePowerSum_one] using
      hrow (k 0) z
  · simpa only [comparableMultidimensionalClumpSpacing_one,
      cubeFullVandermonde_one_singularValue, multidimensionalClumpUpperExponent_one] using hfull

/-- The original transfer is a corollary of cube sampling at dimension one;
no separate one-dimensional concentration proof is used. -/
theorem multiClump_sampling_of_deterministicControl {n nstar : ℕ}
    (hn : 0 < n) {c0 C0 : ℝ} (hC0 : (n : ℝ) ≤ C0)
    (hcontrol : MultiClumpDeterministicControl n nstar c0 C0) :
    MultiClumpSamplingConclusion multiClumpSamplingConstant n nstar c0 C0 := by
  have hcube := multidimensionalMultiClump_sampling_of_deterministicControl
    (by norm_num : 1 ≤ 1) hn
    (multidimensionalMultiClumpDeterministicControl_one_of_original hC0 hcontrol)
  simpa only [multidimensionalMultiClumpSamplingConstant_one, multiClumpSamplingConstant] using
    multiClumpSamplingConclusion_of_multidimensional_one hcube

/-- Closing the deterministic geometry theorem suffices to prove the whole
outer-quantifier statement. There is no unproved probability premise. -/
theorem multiClump_statement_of_deterministicControl
    (hdet : ∀ (n nstar : ℕ), 2 ≤ nstar → nstar ≤ n →
      ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
        MultiClumpDeterministicControl n nstar c0 C0) :
    MultiClumpSamplingStatement := by
  refine ⟨multiClumpSamplingConstant, multiClumpSamplingConstant_pos, ?_⟩
  intro n nstar hstar hnstar
  obtain ⟨c0, C0, hc0, hc1, hC0, hcontrol⟩ := hdet n nstar hstar hnstar
  exact ⟨c0, C0, hc0, hc1, hC0,
    multiClump_sampling_of_deterministicControl (by omega) hC0 hcontrol⟩

end
end LeanNumDetect.RandSamp
