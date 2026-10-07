import RandSamp.MultiClumpAssembly
import RandSamp.FullVandermondeRank

/-!
# Exact multiclump sampling statement and deterministic-to-random transfer

The proposition `MultiClumpSamplingStatement` is manuscript
`thm:multi-clump-random-sampling`, with exactly its outer quantifier order.
The transfer theorem below is fully proved. Its deterministic input is
discharged in `RandSamp.MultiClumpTheorem`, which proves the complete
geometric statement with no extra hypotheses.
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

/-- Fully proved transfer from the deterministic clump estimates to the
exact sampling conclusion, with the absolute constant `3072`. -/
theorem multiClump_sampling_of_deterministicControl {n nstar : ℕ}
    (hn : 0 < n) {c0 C0 : ℝ} (hC0 : (n : ℝ) ≤ C0)
    (hcontrol : MultiClumpDeterministicControl n nstar c0 C0) :
    MultiClumpSamplingConclusion multiClumpSamplingConstant n nstar c0 C0 := by
  obtain ⟨lower, upper, hpos, hdet⟩ := hcontrol
  refine ⟨lower, upper, hpos, ?_⟩
  intro M hM A P Y hmax hgeom m ρ δ hm hmM hρ0 hρ1 hδ0 hδ1 hsample
  obtain ⟨hleverage, hfull⟩ := hdet M hM A P Y hmax hgeom
  have hnM : n ≤ M + 1 := by
    have : (n : ℝ) ≤ M := hC0.trans hM
    have : n ≤ M := by exact_mod_cast this
    omega
  have hS : (0 : ℝ) < P.sizeSquareSum := by
    exact_mod_cast (lt_of_lt_of_le hn P.n_le_sizeSquareSum)
  have hR : 0 < 1024 * (P.sizeSquareSum : ℝ) := by positivity
  have hrate : 3 * (1024 * (P.sizeSquareSum : ℝ)) / ρ ^ 2 *
      Real.log (2 * (n : ℝ) / δ) ≤ (m : ℝ) := by
    convert hsample using 1
    unfold multiClumpSamplingConstant
    ring
  have hp := fixedSupport_relativeGram_allSingularValues_of_leverage hn hm hmM Y
    hR hρ0 hρ1 hδ0 hδ1 (angularDistinct_fullGram_posDef hnM Y hgeom.distinct)
    hleverage hrate
  apply hp.trans
  apply probability_mono
  intro Ω hΩ
  exact (multiClumpSuccess_iff_relativeGram hn P Y lower upper hρ0.le hρ1.le hfull Ω).2 hΩ.1

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
