import NumDetect.RandomClumpVandermonde
import NumDetect.RandomCubeNumberDetection

/-! High-probability correlation stability and number detection for the
manuscript's fixed `(A,∞,τ,η,nStar)` source model. Both results use the
same two independent uniform frequency subsets and lower-only factor event. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open LeanNumDetect.FiniteMatrixSampling LeanNumDetect.RandSamp
open LeanNumDetect.QuantitativeClumpSectionBounds
open scoped BigOperators

namespace LeanNumDetect.NumDetect
noncomputable section

/-- The common factor event for MUSIC and number detection. The failure
probability is `ε`, while the clump separation remains the manuscript's `η`. -/
theorem positiveCubeClumpFactorPair_lower_probability
    {d n nStar L A M₁ M₂ : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n)
    {c0 C0 Csep : ℝ}
    (hsampling : QuantitativeMultiClumpLowerSamplingConclusion d n nStar c0 C0 Csep)
    (μ : AtomicMeasure d n) {τ η ρ ε : ℝ}
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hL : C0 ≤ (L : ℝ)) (hτ : τ ≤ c0 / (L : ℝ)) (hη : Csep / (L : ℝ) ≤ η)
    (hM₁ : n < M₁) (hM₂ : n ≤ M₂)
    (hM₁N : M₁ ≤ (L + 1) ^ d) (hM₂N : M₂ ≤ (L + 1) ^ d)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hsample₁ : (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log (2 * (n : ℝ) / ε) ≤ (M₁ : ℝ))
    (hsample₂ : (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log (2 * (n : ℝ) / ε) ≤ (M₂ : ℝ)) :
    1 - ε ≤ probability (fun pair :
        FiniteSample (CubeFrequency d L) M₁ × FiniteSample (CubeFrequency d L) M₂ =>
      (Real.sqrt (1 - ρ) * positiveCubeClumpLower d nStar L
          (periodicMinimumL1Separation μ.node hn) ≤
        matrixSingularValue (cubeSampledVandermonde M₁ μ.node pair.1.val) (n - 1)) ∧
      (Real.sqrt (1 - ρ) * positiveCubeClumpLower d nStar L
          (periodicMinimumL1Separation μ.node hn) ≤
        matrixSingularValue (cubeSampledVandermonde M₂ μ.node pair.2.val) (n - 1))) := by
  classical
  have hεhalf0 : 0 < ε / 2 := by positivity
  have hεhalf1 : ε / 2 < 1 := by linarith
  have hlog : (n : ℝ) / (ε / 2) = 2 * (n : ℝ) / ε := by
    have hεne : ε ≠ 0 := ne_of_gt hε0
    field_simp
  have hs₁ : (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log ((n : ℝ) / (ε / 2)) ≤ (M₁ : ℝ) := by
    rw [hlog]; exact hsample₁
  have hs₂ : (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log ((n : ℝ) / (ε / 2)) ≤ (M₂ : ℝ) := by
    rw [hlog]; exact hsample₂
  let RowGood : FiniteSample (CubeFrequency d L) M₁ → Prop := fun W =>
    Real.sqrt (1 - ρ) * positiveCubeClumpLower d nStar L
      (periodicMinimumL1Separation μ.node hn) ≤
      matrixSingularValue (cubeSampledVandermonde M₁ μ.node W.val) (n - 1)
  let ColumnGood : FiniteSample (CubeFrequency d L) M₂ → Prop := fun Z =>
    Real.sqrt (1 - ρ) * positiveCubeClumpLower d nStar L
      (periodicMinimumL1Separation μ.node hn) ≤
      matrixSingularValue (cubeSampledVandermonde M₂ μ.node Z.val) (n - 1)
  have hp₁ : 1 - ε / 2 ≤ probability RowGood := by
    exact positiveCubeClumpVandermonde_normalized_lower_probability (m := M₁) hd hn hsampling
      μ hclumps hL hτ hη (by omega) hM₁N hρ0 hρ1 hεhalf0 hεhalf1 hs₁
  have hp₂ : 1 - ε / 2 ≤ probability ColumnGood := by
    exact positiveCubeClumpVandermonde_normalized_lower_probability (m := M₂) hd hn hsampling
      μ hclumps hL hτ hη (by omega) hM₂N hρ0 hρ1 hεhalf0 hεhalf1 hs₂
  letI : Nonempty (FiniteSample (CubeFrequency d L) M₁) :=
    finiteSample_nonempty (by simpa only [card_cubeFrequency] using hM₁N)
  letI : Nonempty (FiniteSample (CubeFrequency d L) M₂) :=
    finiteSample_nonempty (by simpa only [card_cubeFrequency] using hM₂N)
  exact FiniteMatrixSampling.probability_product_lower_bound RowGood ColumnGood ε hp₁ hp₂

/-- The exact correlation-only conclusion of the manuscript corollary. -/
def PositiveCubeClumpMUSICConclusion (d n nStar : ℕ) (hn : 2 ≤ n)
    (c0 C0 Csep : ℝ) : Prop :=
  ∀ (L A M₁ M₂ : ℕ) (μ : AtomicMeasure d n) (measurement : Point d → ℂ)
    (τ η Ω σ ρ ε : ℝ)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η),
    C0 ≤ (L : ℝ) → τ ≤ c0 / (L : ℝ) → Csep / (L : ℝ) ≤ η →
    n < M₁ → n ≤ M₂ → M₁ ≤ (L + 1) ^ d → M₂ ≤ (L + 1) ^ d →
    (2 * L : ℝ) ≤ Ω → IsBandMeasurement μ Ω σ measurement →
    0 < ρ → ρ < 1 → 0 < ε → ε < 1 →
    (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log (2 * (n : ℝ) / ε) ≤ (M₁ : ℝ) →
    (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log (2 * (n : ℝ) / ε) ≤ (M₂ : ℝ) →
    2 * σ < minAmplitude μ (Nat.zero_lt_of_lt hn) * ((1 - ρ) *
      (multidimensionalClumpOptimizedLowerConstant d nStar) ^ 2 *
        ((L : ℝ) * periodicMinimumL1Separation μ.node hn) ^ (2 * nStar - 2)) →
    1 - ε ≤ probability (fun pair :
        FiniteSample (CubeFrequency d L) M₁ × FiniteSample (CubeFrequency d L) M₂ =>
      correlationUniformDistance
        (rankNoiseSpaceCorrelation (positiveCubeFrequency pair.1)
          (generalizedHankel (positiveCubeFrequency pair.1)
            (positiveCubeFrequency pair.2) measurement) n)
        (rankNoiseSpaceCorrelation (positiveCubeFrequency pair.1)
          (generalizedHankel (positiveCubeFrequency pair.1)
            (positiveCubeFrequency pair.2) (fourier μ)) n) ≤
        2 * σ / (minAmplitude μ (Nat.zero_lt_of_lt hn) * ((1 - ρ) *
          (multidimensionalClumpOptimizedLowerConstant d nStar) ^ 2 *
            ((L : ℝ) * periodicMinimumL1Separation μ.node hn) ^ (2 * nStar - 2))))

/-- The singular-value and algorithm-count conclusion in the manuscript's
number-detection consequence; Lean indices begin at zero. -/
def PositiveCubeClumpNumberDetectionConclusion (d n nStar : ℕ) (hn : 2 ≤ n)
    (c0 C0 Csep : ℝ) : Prop :=
  ∀ (L A M₁ M₂ : ℕ) (μ : AtomicMeasure d n) (measurement : Point d → ℂ)
    (τ η Ω σ ρ ε : ℝ)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η),
    C0 ≤ (L : ℝ) → τ ≤ c0 / (L : ℝ) → Csep / (L : ℝ) ≤ η →
    n < M₁ → n ≤ M₂ → M₁ ≤ (L + 1) ^ d → M₂ ≤ (L + 1) ^ d →
    (2 * L : ℝ) ≤ Ω → IsBandMeasurement μ Ω σ measurement →
    0 < ρ → ρ < 1 → 0 < ε → ε < 1 →
    (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log (2 * (n : ℝ) / ε) ≤ (M₁ : ℝ) →
    (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log (2 * (n : ℝ) / ε) ≤ (M₂ : ℝ) →
    2 * σ < minAmplitude μ (Nat.zero_lt_of_lt hn) * ((1 - ρ) *
      (multidimensionalClumpOptimizedLowerConstant d nStar) ^ 2 *
        ((L : ℝ) * periodicMinimumL1Separation μ.node hn) ^ (2 * nStar - 2)) →
    1 - ε ≤ probability (fun pair :
        FiniteSample (CubeFrequency d L) M₁ × FiniteSample (CubeFrequency d L) M₂ =>
      σ * Real.sqrt (M₁ * M₂) <
        matrixSingularValue (generalizedHankel (positiveCubeFrequency pair.1)
          (positiveCubeFrequency pair.2) measurement) (n - 1) ∧
      (∀ j, n ≤ j → j < min M₁ M₂ →
        matrixSingularValue (generalizedHankel (positiveCubeFrequency pair.1)
          (positiveCubeFrequency pair.2) measurement) j < σ * Real.sqrt (M₁ * M₂)) ∧
      ((Finset.range (min M₁ M₂)).filter fun j =>
        σ * Real.sqrt (M₁ * M₂) <
          matrixSingularValue (generalizedHankel (positiveCubeFrequency pair.1)
            (positiveCubeFrequency pair.2) measurement) j).card = n)

/-- MUSIC and number detection share one choice of geometry thresholds
and the same lower-only factor event. -/
theorem positiveCubeClumpMUSIC_and_numberDetection_highProbability
    (d : ℕ) (hd : 1 ≤ d) (n nStar : ℕ) (hStar : 2 ≤ nStar) (hsize : nStar ≤ n) :
    let hnStar0 : 0 < nStar := by omega
    let c0 := quantitativeClumpRadius d (n-nStar) nStar hnStar0
    let C0 := quantitativeClumpBandwidth d n nStar hnStar0
    let Csep := quantitativeClumpSeparation d n nStar hnStar0
    0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      PositiveCubeClumpVandermondeConclusion d n nStar (by omega) c0 C0 Csep ∧
      PositiveCubeClumpMUSICConclusion d n nStar (by omega) c0 C0 Csep ∧
      PositiveCubeClumpNumberDetectionConclusion d n nStar (by omega) c0 C0 Csep := by
  classical
  dsimp only
  obtain ⟨hc0,hc01,hC0,_,hsampling⟩ :=
    multidimensionalMultiClump_lower_sampling_explicit d hd n nStar hStar hsize
  refine ⟨hc0,hc01,hC0,
    positiveCubeClumpVandermonde_lower_of_sampling hd hStar hsize hC0 hsampling, ?_, ?_⟩
  ·
    intro L A M₁ M₂ μ measurement τ η Ω σ ρ ε hclumps hL hτ hη
      hM₁ hM₂ hM₁N hM₂N hband hmeasurement hρ0 hρ1 hε0 hε1 hsample₁ hsample₂ hsmall
    have hn : 2 ≤ n := by omega
    have hn0 : 0 < n := by omega
    have hL0 : 0 < L := by
      exact_mod_cast (Nat.cast_pos.mpr hn0).trans_le (hC0.trans hL)
    let Δ := periodicMinimumL1Separation μ.node hn
    have hΔ : 0 < Δ := periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
    let b := positiveCubeClumpLower d nStar L Δ
    have hb : 0 < b := positiveCubeClumpLower_pos (nStar := nStar) hd (by omega) hL0 hΔ
    let a := b ^ 2
    have ha : 0 < a := pow_pos hb _
    have hsmall' : 2 * σ < minAmplitude μ hn0 * ((1 - ρ) * a) := by
      simpa only [a, b, Δ, positiveCubeClumpLower_sq (nStar := nStar) (by omega), mul_assoc] using hsmall
    have hsqrt : Real.sqrt ((1 - ρ) * a) = Real.sqrt (1 - ρ) * b := by
      dsimp [a]
      rw [Real.sqrt_mul (sub_nonneg.mpr hρ1.le), Real.sqrt_sq hb.le]
    have hpair := positiveCubeClumpFactorPair_lower_probability hd hn hsampling μ
      hclumps hL hτ hη hM₁ hM₂ hM₁N hM₂N hρ0 hρ1 hε0 hε1 hsample₁ hsample₂
    apply hpair.trans
    apply probability_mono
    intro ⟨W, Z⟩ hgood
    have hrow : Real.sqrt ((1 - ρ) * a) ≤
        matrixSingularValue (cubeSampledVandermonde M₁ μ.node W.val) (n - 1) := by
      rw [hsqrt]; exact hgood.1
    have hcolumn : Real.sqrt ((1 - ρ) * a) ≤
        matrixSingularValue (cubeSampledVandermonde M₂ μ.node Z.val) (n - 1) := by
      rw [hsqrt]; exact hgood.2
    have hE : matrixSpectralNorm
        (generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) measurement -
          generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) (fourier μ)) ≤
        σ * Real.sqrt (M₁ * M₂) :=
      (positiveCubeGHM_noise_spectralNorm_lt W Z μ measurement hmeasurement hband
        (by omega) (by omega)).le
    have hdet := positiveCubeMUSIC_correlation_stability_of_singularValues
      μ W Z
      (generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) measurement -
        generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) (fourier μ))
      hn0 hM₁ hM₂ ha hρ1 hrow hcolumn hE hsmall'
    have hfactor :
        generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) (fourier μ) =
          generalizedVandermonde (positiveCubeFrequency W) μ.node *
            Matrix.diagonal μ.amplitude *
            Matrix.transpose (generalizedVandermonde (positiveCubeFrequency Z) μ.node) :=
      generalizedHankel_fourier_eq_hankelVandermondeFactor
        (positiveCubeFrequency W) (positiveCubeFrequency Z) μ
    rw [← hfactor] at hdet
    have hcancel :
        generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) (fourier μ) +
          (generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) measurement -
            generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) (fourier μ)) =
          generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) measurement := by
      abel
    rw [hcancel] at hdet
    simpa only [a, b, Δ, positiveCubeClumpLower_sq (nStar := nStar) (by omega), mul_assoc] using hdet
  ·
    intro L A M₁ M₂ μ measurement τ η Ω σ ρ ε hclumps hL hτ hη
      hM₁ hM₂ hM₁N hM₂N hband hmeasurement hρ0 hρ1 hε0 hε1 hsample₁ hsample₂ hsmall
    have hn : 2 ≤ n := by omega
    have hn0 : 0 < n := by omega
    have hL0 : 0 < L := by
      exact_mod_cast (Nat.cast_pos.mpr hn0).trans_le (hC0.trans hL)
    let Δ := periodicMinimumL1Separation μ.node hn
    have hΔ : 0 < Δ := periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
    let b := positiveCubeClumpLower d nStar L Δ
    have hb : 0 < b := positiveCubeClumpLower_pos (nStar := nStar) hd (by omega) hL0 hΔ
    let a := b ^ 2
    have ha : 0 < a := pow_pos hb _
    have hsmall' : 2 * σ < minAmplitude μ hn0 * ((1 - ρ) * a) := by
      simpa only [a, b, Δ, positiveCubeClumpLower_sq (nStar := nStar) (by omega), mul_assoc] using hsmall
    have hsqrt : Real.sqrt ((1 - ρ) * a) = Real.sqrt (1 - ρ) * b := by
      dsimp [a]
      rw [Real.sqrt_mul (sub_nonneg.mpr hρ1.le), Real.sqrt_sq hb.le]
    have hpair := positiveCubeClumpFactorPair_lower_probability hd hn hsampling μ
      hclumps hL hτ hη hM₁ hM₂ hM₁N hM₂N hρ0 hρ1 hε0 hε1 hsample₁ hsample₂
    apply hpair.trans
    apply probability_mono
    intro ⟨W, Z⟩ hgood
    have hrow : Real.sqrt ((1 - ρ) * a) ≤
        matrixSingularValue (cubeSampledVandermonde M₁ μ.node W.val) (n - 1) := by
      rw [hsqrt]; exact hgood.1
    have hcolumn : Real.sqrt ((1 - ρ) * a) ≤
        matrixSingularValue (cubeSampledVandermonde M₂ μ.node Z.val) (n - 1) := by
      rw [hsqrt]; exact hgood.2
    exact positiveCubeGHM_numberDetection_of_singularValues μ W Z measurement hn0 hM₁ hM₂
      ha hρ1 hband hmeasurement hrow hcolumn hsmall'

/-- Fixed-source multiclump random-GHM MUSIC correlation stability. -/
theorem positiveCubeClumpMUSIC_correlation_stability_highProbability
    (d : ℕ) (hd : 1 ≤ d) (n nStar : ℕ) (hStar : 2 ≤ nStar) (hsize : nStar ≤ n) :
    let hnStar0 : 0 < nStar := by omega
    let c0 := quantitativeClumpRadius d (n-nStar) nStar hnStar0
    let C0 := quantitativeClumpBandwidth d n nStar hnStar0
    let Csep := quantitativeClumpSeparation d n nStar hnStar0
    0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      PositiveCubeClumpMUSICConclusion d n nStar (by omega) c0 C0 Csep := by
  dsimp only
  obtain ⟨hc0,hc01,hC0,_,hmusic,_⟩ :=
    positiveCubeClumpMUSIC_and_numberDetection_highProbability d hd n nStar hStar hsize
  exact ⟨hc0,hc01,hC0,hmusic⟩

/-- Fixed-source multiclump random-GHM number detection with the exact
singular-value threshold and count from the manuscript algorithm. -/
theorem positiveCubeClumpGHM_numberDetection_highProbability
    (d : ℕ) (hd : 1 ≤ d) (n nStar : ℕ) (hStar : 2 ≤ nStar) (hsize : nStar ≤ n) :
    let hnStar0 : 0 < nStar := by omega
    let c0 := quantitativeClumpRadius d (n-nStar) nStar hnStar0
    let C0 := quantitativeClumpBandwidth d n nStar hnStar0
    let Csep := quantitativeClumpSeparation d n nStar hnStar0
    0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      PositiveCubeClumpNumberDetectionConclusion d n nStar (by omega) c0 C0 Csep := by
  dsimp only
  obtain ⟨hc0,hc01,hC0,_,_,hnumber⟩ :=
    positiveCubeClumpMUSIC_and_numberDetection_highProbability d hd n nStar hStar hsize
  exact ⟨hc0,hc01,hC0,hnumber⟩

end
end LeanNumDetect.NumDetect
