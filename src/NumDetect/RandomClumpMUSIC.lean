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
open scoped BigOperators

namespace LeanNumDetect.NumDetect
noncomputable section

/-- The existing pair-sampling rate already provides a nonzero noise space. -/
theorem positiveCubeClump_sampleCount_gt
    {d n nStar A m : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n)
    (μ : AtomicMeasure d n) {τ η ρ ε : ℝ}
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hsample : (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log (2 * (n : ℝ) / ε) ≤ (m : ℝ)) : n < m := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnS : (n : ℝ) ≤ ((angularClumpPartition hclumps).sizePowerSum d : ℝ) := by
    exact_mod_cast (angularClumpPartition hclumps).n_le_sizePowerSum hd
  have hρsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ0
  have hcoef : (3 : ℝ) ≤ 3 / ρ ^ 2 := by
    apply (le_div_iff₀ hρsq).mpr
    nlinarith
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)
    rw [Real.log_inv] at h
    linarith
  have hratio : (2 : ℝ) ≤ 2 * (n : ℝ) / ε := by
    apply (le_div_iff₀ hε0).mpr
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 * (n : ℝ) / ε) :=
    hhalf.trans (Real.log_le_log (by norm_num) hratio)
  have hproduct : 3 * (n : ℝ) ≤ 3 / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) :=
    mul_le_mul hcoef hnS hn0.le (by positivity)
  have hlt : (n : ℝ) < (m : ℝ) := calc
    (n : ℝ) < 3 * (n : ℝ) * (1 / 2) := by nlinarith
    _ ≤ (3 : ℝ) / ρ ^ 2 *
        ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
          Real.log (2 * (n : ℝ) / ε) :=
      mul_le_mul hproduct hlog (by norm_num) (by positivity)
    _ ≤ (m : ℝ) := hsample
  exact_mod_cast hlt

/-- The common factor event for MUSIC and number detection. The failure
probability is `ε`, while the clump separation remains the manuscript's `η`. -/
theorem positiveCubeClumpFactorPair_lower_probability
    {d n nStar L A M₁ M₂ : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n)
    (μ : AtomicMeasure d n) {τ η β ρ ε : ℝ}
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hgeom : LiCubeClumpGeometry μ A nStar L τ η β hn)
    (hM₁ : n ≤ M₁) (hM₂ : n ≤ M₂)
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
      (Real.sqrt (1 - ρ) * positiveCubeClumpLower d n nStar L β
          (periodicMinimumL1Separation μ.node hn) ≤
        matrixSingularValue (cubeSampledVandermonde M₁ μ.node pair.1.val) (n - 1)) ∧
      (Real.sqrt (1 - ρ) * positiveCubeClumpLower d n nStar L β
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
    Real.sqrt (1 - ρ) * positiveCubeClumpLower d n nStar L β
      (periodicMinimumL1Separation μ.node hn) ≤
      matrixSingularValue (cubeSampledVandermonde M₁ μ.node W.val) (n - 1)
  let ColumnGood : FiniteSample (CubeFrequency d L) M₂ → Prop := fun Z =>
    Real.sqrt (1 - ρ) * positiveCubeClumpLower d n nStar L β
      (periodicMinimumL1Separation μ.node hn) ≤
      matrixSingularValue (cubeSampledVandermonde M₂ μ.node Z.val) (n - 1)
  have hp₁ : 1 - ε / 2 ≤ probability RowGood := by
    exact positiveCubeClumpVandermonde_normalized_lower_probability (m := M₁) hd hn
      μ hclumps hgeom (by omega) hM₁N hρ0 hρ1 hεhalf0 hεhalf1 hs₁
  have hp₂ : 1 - ε / 2 ≤ probability ColumnGood := by
    exact positiveCubeClumpVandermonde_normalized_lower_probability (m := M₂) hd hn
      μ hclumps hgeom (by omega) hM₂N hρ0 hρ1 hεhalf0 hεhalf1 hs₂
  letI : Nonempty (FiniteSample (CubeFrequency d L) M₁) :=
    finiteSample_nonempty (by simpa only [card_cubeFrequency] using hM₁N)
  letI : Nonempty (FiniteSample (CubeFrequency d L) M₂) :=
    finiteSample_nonempty (by simpa only [card_cubeFrequency] using hM₂N)
  exact FiniteMatrixSampling.probability_product_lower_bound RowGood ColumnGood ε hp₁ hp₂

/-- The noiseless random GHM lower bound on the common factor event. -/
theorem positiveCubeClumpGHM_signalSingularValue_lower_highProbability
    {d n nStar L A M₁ M₂ : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n)
    (μ : AtomicMeasure d n) {τ η β ρ ε : ℝ}
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hgeom : LiCubeClumpGeometry μ A nStar L τ η β hn)
    (hM₁ : n ≤ M₁) (hM₂ : n ≤ M₂)
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
      minAmplitude μ (Nat.zero_lt_of_lt hn) * Real.sqrt (M₁ * M₂) *
          ((1 - ρ) * (positiveCubeClumpCoefficient d n nStar β) ^ 2 *
            ((L : ℝ) * periodicMinimumL1Separation μ.node hn) ^ (2 * nStar - 2)) ≤
        matrixSingularValue (generalizedHankel (positiveCubeFrequency pair.1)
          (positiveCubeFrequency pair.2) (fourier μ)) (n - 1)) := by
  classical
  have hn0 : 0 < n := by omega
  have hM₁0 : 0 < M₁ := by omega
  have hM₂0 : 0 < M₂ := by omega
  have hL0 : 0 < L := by have h := hgeom.2.1; omega
  have hStar : 0 < nStar := by have h := hclumps.1; omega
  let Δ := periodicMinimumL1Separation μ.node hn
  have hΔ : 0 < Δ := periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
  let b₀ := positiveCubeClumpLower d n nStar L β Δ
  have hb₀ : 0 < b₀ := positiveCubeClumpLower_pos hd hn0 hStar hL0 hgeom.2.2.2.1 hΔ
  let a := b₀ ^ 2
  have ha : 0 < a := pow_pos hb₀ _
  have hab : 0 < (1 - ρ) * a := mul_pos (sub_pos.mpr hρ1) ha
  let b := Real.sqrt ((1 - ρ) * a)
  have hb : 0 < b := Real.sqrt_pos.2 hab
  have hsqrt : b = Real.sqrt (1 - ρ) * b₀ := by
    dsimp [b, a]
    rw [Real.sqrt_mul (sub_nonneg.mpr hρ1.le), Real.sqrt_sq hb₀.le]
  have hpair := positiveCubeClumpFactorPair_lower_probability hd hn μ
    hclumps hgeom hM₁ hM₂ hM₁N hM₂N hρ0 hρ1 hε0 hε1 hsample₁ hsample₂
  apply hpair.trans
  apply probability_mono
  intro pair hgood
  let V₁ := generalizedVandermonde (positiveCubeFrequency pair.1) μ.node
  let V₂ := generalizedVandermonde (positiveCubeFrequency pair.2) μ.node
  let G₀ := generalizedHankel (positiveCubeFrequency pair.1)
    (positiveCubeFrequency pair.2) (fourier μ)
  have hrow : b ≤ matrixSingularValue
      (cubeSampledVandermonde M₁ μ.node pair.1.val) (n - 1) := by
    rw [hsqrt]
    exact hgood.1
  have hcolumn : b ≤ matrixSingularValue
      (cubeSampledVandermonde M₂ μ.node pair.2.val) (n - 1) := by
    rw [hsqrt]
    exact hgood.2
  have hrow' : Real.sqrt (M₁ : ℝ) * b ≤ matrixSingularValue V₁ (n - 1) :=
    unnormalizedCubeVandermonde_minimumSingularValue hn0 hM₁0 pair.1 μ.node hab.le hrow
  have hcolumn' : Real.sqrt (M₂ : ℝ) * b ≤ matrixSingularValue V₂ (n - 1) :=
    unnormalizedCubeVandermonde_minimumSingularValue hn0 hM₂0 pair.2 μ.node hab.le hcolumn
  have hfull₂ : HasFullColumnRank V₂ := fullColumnRank_of_lastSingularValue_pos V₂ hn0
    ((mul_pos (Real.sqrt_pos.2 (Nat.cast_pos.mpr hM₂0)) hb).trans_le hcolumn')
  have hfactor : G₀ = V₁ * Matrix.diagonal μ.amplitude * V₂ᵀ :=
    generalizedHankel_fourier_eq_hankelVandermondeFactor
      (positiveCubeFrequency pair.1) (positiveCubeFrequency pair.2) μ
  have hsignal : minAmplitude μ hn0 * Real.sqrt (M₁ * M₂ : ℝ) * ((1 - ρ) * a) ≤
      matrixSingularValue G₀ (n - 1) := by
    have hproduct := mul_le_mul hrow' hcolumn'
      (mul_nonneg (Real.sqrt_nonneg (M₂ : ℝ)) hb.le) (matrixSingularValue_nonneg _ _)
    have hscaled := mul_le_mul_of_nonneg_left hproduct (minAmplitude_pos μ hn0).le
    have hbase := vandermondeFactor_signalSingularValue_lower
      (positiveCubeFrequency pair.1) (positiveCubeFrequency pair.2) μ.node μ.amplitude
      (minAmplitude μ hn0) hn0 (minAmplitude_pos μ hn0) (minAmplitude_le μ hn0) hfull₂
    rw [← hfactor] at hbase
    apply le_trans _ hbase
    have heq : minAmplitude μ hn0 * Real.sqrt (M₁ * M₂ : ℝ) * ((1 - ρ) * a) =
        minAmplitude μ hn0 * ((Real.sqrt (M₁ : ℝ) * b) * (Real.sqrt (M₂ : ℝ) * b)) := by
      dsimp [b]
      rw [Real.sqrt_mul (Nat.cast_nonneg M₁)]
      calc
        _ = minAmplitude μ hn0 * (Real.sqrt (M₁ : ℝ) * Real.sqrt (M₂ : ℝ)) *
            Real.sqrt ((1 - ρ) * a) ^ 2 := by rw [Real.sq_sqrt hab.le]
        _ = _ := by ring
    rw [heq]
    simpa only [V₁, V₂, mul_assoc] using hscaled
  simpa only [G₀, a, b₀, Δ, positiveCubeClumpLower_sq (nStar := nStar) (by omega),
    mul_assoc] using hsignal

/-- The exact correlation-only conclusion of the manuscript corollary. -/
def PositiveCubeClumpMUSICConclusion (d n nStar : ℕ) (hn : 2 ≤ n)
    (β : ℝ) : Prop :=
  ∀ (L A M₁ M₂ : ℕ) (μ : AtomicMeasure d n) (measurement : Point d → ℂ)
    (τ η Ω σ ρ ε : ℝ)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η),
    LiCubeClumpGeometry μ A nStar L τ η β hn →
    n ≤ M₁ → n ≤ M₂ → M₁ ≤ (L + 1) ^ d → M₂ ≤ (L + 1) ^ d →
    (2 * L : ℝ) ≤ Ω → IsBandMeasurement μ Ω σ measurement →
    0 < ρ → ρ < 1 → 0 < ε → ε < 1 →
    (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log (2 * (n : ℝ) / ε) ≤ (M₁ : ℝ) →
    (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log (2 * (n : ℝ) / ε) ≤ (M₂ : ℝ) →
    2 * σ < minAmplitude μ (Nat.zero_lt_of_lt hn) * ((1 - ρ) *
      (positiveCubeClumpCoefficient d n nStar β) ^ 2 *
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
          (positiveCubeClumpCoefficient d n nStar β) ^ 2 *
            ((L : ℝ) * periodicMinimumL1Separation μ.node hn) ^ (2 * nStar - 2))))

/-- The singular-value and algorithm-count conclusion in the manuscript's
number-detection consequence; Lean indices begin at zero. -/
def PositiveCubeClumpNumberDetectionConclusion (d n nStar : ℕ) (hn : 2 ≤ n)
    (β : ℝ) : Prop :=
  ∀ (L A M₁ M₂ : ℕ) (μ : AtomicMeasure d n) (measurement : Point d → ℂ)
    (τ η Ω σ ρ ε : ℝ)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η),
    LiCubeClumpGeometry μ A nStar L τ η β hn →
    n ≤ M₁ → n ≤ M₂ → M₁ ≤ (L + 1) ^ d → M₂ ≤ (L + 1) ^ d →
    (2 * L : ℝ) ≤ Ω → IsBandMeasurement μ Ω σ measurement →
    0 < ρ → ρ < 1 → 0 < ε → ε < 1 →
    (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log (2 * (n : ℝ) / ε) ≤ (M₁ : ℝ) →
    (3 : ℝ) / ρ ^ 2 *
      ((angularClumpPartition hclumps).sizePowerSum d : ℝ) *
        Real.log (2 * (n : ℝ) / ε) ≤ (M₂ : ℝ) →
    2 * σ < minAmplitude μ (Nat.zero_lt_of_lt hn) * ((1 - ρ) *
      (positiveCubeClumpCoefficient d n nStar β) ^ 2 *
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

/-- MUSIC and number detection use Li's geometry and the same unconditional
lower sampling event. No leverage hypothesis is exposed to the application. -/
theorem positiveCubeClumpMUSIC_and_numberDetection_highProbability
    (d : ℕ) (hd : 1 ≤ d) (n nStar : ℕ) (hStar : 2 ≤ nStar)
    (hsize : nStar ≤ n) (β : ℝ) :
    PositiveCubeClumpMUSICConclusion d n nStar (by omega) β ∧
      PositiveCubeClumpNumberDetectionConclusion d n nStar (by omega) β := by
  classical
  constructor
  ·
    intro L A M₁ M₂ μ measurement τ η Ω σ ρ ε hclumps hgeom
      hM₁ hM₂ hM₁N hM₂N hband hmeasurement hρ0 hρ1 hε0 hε1 hsample₁ hsample₂ hsmall
    have hn : 2 ≤ n := by omega
    have hn0 : 0 < n := by omega
    have hM₁lt : n < M₁ := positiveCubeClump_sampleCount_gt hd hn μ hclumps
      hρ0 hρ1 hε0 hε1 hsample₁
    have hL0 : 0 < L := by
      have h := hgeom.2.1
      omega
    let Δ := periodicMinimumL1Separation μ.node hn
    have hΔ : 0 < Δ := periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
    let b := positiveCubeClumpLower d n nStar L β Δ
    have hb : 0 < b := positiveCubeClumpLower_pos (nStar := nStar) hd hn0 (by omega) hL0 hgeom.2.2.2.1 hΔ
    let a := b ^ 2
    have ha : 0 < a := pow_pos hb _
    have hsmall' : 2 * σ < minAmplitude μ hn0 * ((1 - ρ) * a) := by
      simpa only [a, b, Δ, positiveCubeClumpLower_sq (nStar := nStar) (by omega), mul_assoc] using hsmall
    have hsqrt : Real.sqrt ((1 - ρ) * a) = Real.sqrt (1 - ρ) * b := by
      dsimp [a]
      rw [Real.sqrt_mul (sub_nonneg.mpr hρ1.le), Real.sqrt_sq hb.le]
    have hpair := positiveCubeClumpFactorPair_lower_probability hd hn μ
      hclumps hgeom hM₁ hM₂ hM₁N hM₂N hρ0 hρ1 hε0 hε1 hsample₁ hsample₂
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
      hn0 hM₁lt hM₂ ha hρ1 hrow hcolumn hE hsmall'
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
    intro L A M₁ M₂ μ measurement τ η Ω σ ρ ε hclumps hgeom
      hM₁ hM₂ hM₁N hM₂N hband hmeasurement hρ0 hρ1 hε0 hε1 hsample₁ hsample₂ hsmall
    have hn : 2 ≤ n := by omega
    have hn0 : 0 < n := by omega
    have hM₁lt : n < M₁ := positiveCubeClump_sampleCount_gt hd hn μ hclumps
      hρ0 hρ1 hε0 hε1 hsample₁
    have hL0 : 0 < L := by
      have h := hgeom.2.1
      omega
    let Δ := periodicMinimumL1Separation μ.node hn
    have hΔ : 0 < Δ := periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
    let b := positiveCubeClumpLower d n nStar L β Δ
    have hb : 0 < b := positiveCubeClumpLower_pos (nStar := nStar) hd hn0 (by omega) hL0 hgeom.2.2.2.1 hΔ
    let a := b ^ 2
    have ha : 0 < a := pow_pos hb _
    have hsmall' : 2 * σ < minAmplitude μ hn0 * ((1 - ρ) * a) := by
      simpa only [a, b, Δ, positiveCubeClumpLower_sq (nStar := nStar) (by omega), mul_assoc] using hsmall
    have hsqrt : Real.sqrt ((1 - ρ) * a) = Real.sqrt (1 - ρ) * b := by
      dsimp [a]
      rw [Real.sqrt_mul (sub_nonneg.mpr hρ1.le), Real.sqrt_sq hb.le]
    have hpair := positiveCubeClumpFactorPair_lower_probability hd hn μ
      hclumps hgeom hM₁ hM₂ hM₁N hM₂N hρ0 hρ1 hε0 hε1 hsample₁ hsample₂
    apply hpair.trans
    apply probability_mono
    intro ⟨W, Z⟩ hgood
    have hrow : Real.sqrt ((1 - ρ) * a) ≤
        matrixSingularValue (cubeSampledVandermonde M₁ μ.node W.val) (n - 1) := by
      rw [hsqrt]; exact hgood.1
    have hcolumn : Real.sqrt ((1 - ρ) * a) ≤
        matrixSingularValue (cubeSampledVandermonde M₂ μ.node Z.val) (n - 1) := by
      rw [hsqrt]; exact hgood.2
    exact positiveCubeGHM_numberDetection_of_singularValues μ W Z measurement hn0 hM₁lt hM₂
      ha hρ1 hband hmeasurement hrow hcolumn hsmall'

/-- Fixed-source multiclump random-GHM MUSIC correlation stability. -/
theorem positiveCubeClumpMUSIC_correlation_stability_highProbability
    (d : ℕ) (hd : 1 ≤ d) (n nStar : ℕ) (hStar : 2 ≤ nStar)
    (hsize : nStar ≤ n) (β : ℝ) :
    PositiveCubeClumpMUSICConclusion d n nStar (by omega) β :=
  (positiveCubeClumpMUSIC_and_numberDetection_highProbability d hd n nStar hStar hsize β).1

/-- Fixed-source multiclump random-GHM number detection with the exact
singular-value threshold and count from the manuscript algorithm. -/
theorem positiveCubeClumpGHM_numberDetection_highProbability
    (d : ℕ) (hd : 1 ≤ d) (n nStar : ℕ) (hStar : 2 ≤ nStar)
    (hsize : nStar ≤ n) (β : ℝ) :
    PositiveCubeClumpNumberDetectionConclusion d n nStar (by omega) β :=
  (positiveCubeClumpMUSIC_and_numberDetection_highProbability d hd n nStar hStar hsize β).2

end
end LeanNumDetect.NumDetect
