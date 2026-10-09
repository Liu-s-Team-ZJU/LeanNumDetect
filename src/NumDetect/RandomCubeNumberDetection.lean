import NumDetect.RandomCubeMUSIC

/-! The singular-value threshold used by random-GHM number detection. The
conclusion counts the singular values of the actual measurement matrix, with
the same strict threshold as the manuscript algorithm. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open LeanNumDetect.FiniteMatrixSampling LeanNumDetect.RandSamp
open scoped BigOperators Matrix.Norms.L2Operator

namespace LeanNumDetect.NumDetect
noncomputable section

/-- The two normalized factor lower bounds imply exactly `n` measured singular
values above the noise threshold. No upper factor estimate is used. -/
theorem positiveCubeGHM_numberDetection_of_singularValues
    {d L n M₁ M₂ : ℕ} (μ : AtomicMeasure d n)
    (W : FiniteSample (CubeFrequency d L) M₁)
    (Z : FiniteSample (CubeFrequency d L) M₂)
    (measurement : Point d → ℂ)
    (hn : 0 < n) (hrows : n < M₁) (hcolumns : n ≤ M₂)
    {Ω σ a ρ : ℝ} (ha : 0 < a) (hρ : ρ < 1)
    (hband : (2 * L : ℝ) ≤ Ω)
    (hmeasurement : IsBandMeasurement μ Ω σ measurement)
    (hrow : Real.sqrt ((1 - ρ) * a) ≤
      matrixSingularValue (cubeSampledVandermonde M₁ μ.node W.val) (n - 1))
    (hcolumn : Real.sqrt ((1 - ρ) * a) ≤
      matrixSingularValue (cubeSampledVandermonde M₂ μ.node Z.val) (n - 1))
    (hsmall : 2 * σ < minAmplitude μ hn * ((1 - ρ) * a)) :
    σ * Real.sqrt (M₁ * M₂) <
        matrixSingularValue (generalizedHankel (positiveCubeFrequency W)
          (positiveCubeFrequency Z) measurement) (n - 1) ∧
    (∀ j, n ≤ j → j < min M₁ M₂ →
      matrixSingularValue (generalizedHankel (positiveCubeFrequency W)
        (positiveCubeFrequency Z) measurement) j < σ * Real.sqrt (M₁ * M₂)) ∧
    ((Finset.range (min M₁ M₂)).filter fun j =>
      σ * Real.sqrt (M₁ * M₂) <
        matrixSingularValue (generalizedHankel (positiveCubeFrequency W)
          (positiveCubeFrequency Z) measurement) j).card = n := by
  classical
  have hM₁ : 0 < M₁ := by omega
  have hM₂ : 0 < M₂ := by omega
  have hb : 0 < (1 - ρ) * a := mul_pos (sub_pos.mpr hρ) ha
  let b := Real.sqrt ((1 - ρ) * a)
  have hbpos : 0 < b := Real.sqrt_pos.2 hb
  let V₁ := generalizedVandermonde (positiveCubeFrequency W) μ.node
  let V₂ := generalizedVandermonde (positiveCubeFrequency Z) μ.node
  let G := generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) measurement
  let G₀ := generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z) (fourier μ)
  let E := G - G₀
  let t := σ * Real.sqrt (M₁ * M₂ : ℝ)
  have hrow' : Real.sqrt (M₁ : ℝ) * b ≤ matrixSingularValue V₁ (n - 1) :=
    unnormalizedCubeVandermonde_minimumSingularValue hn hM₁ W μ.node hb.le hrow
  have hcolumn' : Real.sqrt (M₂ : ℝ) * b ≤ matrixSingularValue V₂ (n - 1) :=
    unnormalizedCubeVandermonde_minimumSingularValue hn hM₂ Z μ.node hb.le hcolumn
  have hfull₂ : HasFullColumnRank V₂ := fullColumnRank_of_lastSingularValue_pos V₂ hn
    ((mul_pos (Real.sqrt_pos.2 (Nat.cast_pos.mpr hM₂)) hbpos).trans_le hcolumn')
  have hfactor : G₀ = V₁ * Matrix.diagonal μ.amplitude * V₂ᵀ :=
    generalizedHankel_fourier_eq_hankelVandermondeFactor
      (positiveCubeFrequency W) (positiveCubeFrequency Z) μ
  have hsignal : minAmplitude μ hn * Real.sqrt (M₁ * M₂ : ℝ) * ((1 - ρ) * a) ≤
      matrixSingularValue G₀ (n - 1) := by
    have hproduct := mul_le_mul hrow' hcolumn'
      (mul_nonneg (Real.sqrt_nonneg _) hbpos.le) (matrixSingularValue_nonneg _ _)
    have hscaled := mul_le_mul_of_nonneg_left hproduct (minAmplitude_pos μ hn).le
    have hbase := vandermondeFactor_signalSingularValue_lower
      (positiveCubeFrequency W) (positiveCubeFrequency Z) μ.node μ.amplitude
      (minAmplitude μ hn) hn (minAmplitude_pos μ hn) (minAmplitude_le μ hn) hfull₂
    rw [← hfactor] at hbase
    apply le_trans _ hbase
    have heq : minAmplitude μ hn * Real.sqrt (M₁ * M₂ : ℝ) * ((1 - ρ) * a) =
        minAmplitude μ hn * ((Real.sqrt (M₁ : ℝ) * b) * (Real.sqrt (M₂ : ℝ) * b)) := by
      dsimp [b]
      rw [Real.sqrt_mul (Nat.cast_nonneg M₁)]
      calc
        _ = minAmplitude μ hn * (Real.sqrt (M₁ : ℝ) * Real.sqrt (M₂ : ℝ)) *
            Real.sqrt ((1 - ρ) * a) ^ 2 := by rw [Real.sq_sqrt hb.le]
        _ = _ := by ring
    rw [heq]
    simpa only [V₁, V₂, mul_assoc] using hscaled

  have hnoise : matrixSpectralNorm E < t :=
    positiveCubeGHM_noise_spectralNorm_lt W Z μ measurement hmeasurement hband hM₁ hM₂
  have hreverse : matrixSpectralNorm (G₀ - G) = matrixSpectralNorm E := by
    have heq : G₀ - G = -E := by dsimp [E]; abel
    rw [heq]
    simpa only [matrixSpectralNorm_eq_l2_opNorm] using norm_neg E
  have hperturb := matrixSingularValue_sub_spectralNorm_le G₀ G
    (i := n - 1) (by simpa [Z.property] using (show n - 1 < M₂ by omega))
  rw [hreverse] at hperturb
  have hscaled := mul_lt_mul_of_pos_right hsmall
    (show 0 < Real.sqrt (M₁ * M₂ : ℝ) by positivity)
  have hsignalThreshold : t < matrixSingularValue G (n - 1) := by
    dsimp [t] at *
    nlinarith
  have htail : ∀ j, n ≤ j → j < min M₁ M₂ → matrixSingularValue G j < t := by
    intro j hj hjmin
    have hzero : matrixSingularValue G₀ j = 0 := by
      rw [hfactor]
      exact matrixSingularValue_three_mul_eq_zero_of_card_le V₁ (Matrix.diagonal μ.amplitude)
        V₂ᵀ (by simpa using hj)
    have hperturb := matrixSingularValue_le_add_spectralNorm_sub G G₀
      (i := j) (by simpa [Z.property] using hjmin.trans_le (min_le_right _ _))
    rw [hzero, zero_add] at hperturb
    exact hperturb.trans_lt hnoise
  refine ⟨hsignalThreshold, htail, ?_⟩
  have hset : ((Finset.range (min M₁ M₂)).filter fun j => t < matrixSingularValue G j) =
      Finset.range n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, ht⟩
      by_contra h
      exact (not_lt_of_ge (htail j (by omega) hj).le) ht
    · intro hj
      refine ⟨by omega, ?_⟩
      exact hsignalThreshold.trans_le
        (G.toEuclideanLin.singularValues_antitone (by omega))
  change ((Finset.range (min M₁ M₂)).filter fun j => t < matrixSingularValue G j).card = n
  rw [hset, Finset.card_range]

/-- The well-separated random-GHM number-detection consequence under the
    same sampling and noise conditions as its MUSIC corollary. -/
theorem positiveCubeGHM_numberDetection_highProbability
    {d L n M₁ M₂ : ℕ} (μ : AtomicMeasure d n)
    (measurement : Point d → ℂ)
    (hd : 1 ≤ d) (hL : 1 ≤ L) (hn : 2 ≤ n)
    (hsource : ∀ j, InAngularCube (μ.node j))
    (hM₁ : n < M₁) (hM₂ : n ≤ M₂)
    (hM₁N : M₁ ≤ (L + 1) ^ d) (hM₂N : M₂ ≤ (L + 1) ^ d)
    {Ω σ ρ η : ℝ}
    (hband : (2 * L : ℝ) ≤ Ω)
    (hmeasurement : IsBandMeasurement μ Ω σ measurement)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hqLow :
      2 * Real.pi * (2 * (d : ℝ) - 1) / L <
        periodicMinimumLInfSeparation μ.node hn)
    (hsample₁ :
      3 * (n : ℝ) /
        (cubeSeparatedLower d L (periodicMinimumLInfSeparation μ.node hn) * ρ ^ 2) *
        Real.log (4 * n / η) ≤ M₁)
    (hsample₂ :
      3 * (n : ℝ) /
        (cubeSeparatedLower d L (periodicMinimumLInfSeparation μ.node hn) * ρ ^ 2) *
        Real.log (4 * n / η) ≤ M₂)
    (hsmall : 2 * σ < minAmplitude μ (Nat.zero_lt_of_lt hn) *
      ((1 - ρ) * cubeSeparatedLower d L
        (periodicMinimumLInfSeparation μ.node hn))) :
    1 - η ≤ probability (fun pair :
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
            (positiveCubeFrequency pair.2) measurement) j).card = n) := by
  classical
  have hqHigh := periodicMinimumLInfSeparation_le_pi μ.node hn hsource
  let q := periodicMinimumLInfSeparation μ.node hn
  let a := cubeSeparatedLower d L q
  have hqpos : 0 < q := cube_separation_pos hd hL hqLow
  have ha : 0 < a := cubeSeparatedLower_pos hd hL hqLow
  have hsep : CubeAngularSeparated q μ.node :=
    periodicMinimumLInfSeparation_cubeAngularSeparated μ.node hn hsource hqpos
  have hn0 : 0 < n := by omega
  have hm₁ : 1 ≤ M₁ := by omega
  have hm₂ : 1 ≤ M₂ := by omega
  letI : Nonempty (FiniteSample (CubeFrequency d L) M₁) :=
    finiteSample_nonempty (by simpa only [card_cubeFrequency] using hM₁N)
  letI : Nonempty (FiniteSample (CubeFrequency d L) M₂) :=
    finiteSample_nonempty (by simpa only [card_cubeFrequency] using hM₂N)
  have hηhalf0 : 0 < η / 2 := by positivity
  have hηhalf1 : η / 2 < 1 := by linarith
  have hlog : 2 * (n : ℝ) / (η / 2) = 4 * (n : ℝ) / η := by
    have hηne : η ≠ 0 := ne_of_gt hη0
    field_simp
    ring
  have hsample₁' :
      3 * (n : ℝ) / (a * ρ ^ 2) * Real.log (2 * n / (η / 2)) ≤ M₁ := by
    rw [hlog]
    exact hsample₁
  have hsample₂' :
      3 * (n : ℝ) / (a * ρ ^ 2) * Real.log (2 * n / (η / 2)) ≤ M₂ := by
    rw [hlog]
    exact hsample₂
  let P : FiniteSample (CubeFrequency d L) M₁ → Prop := fun W =>
    Real.sqrt ((1 - ρ) * a) ≤
      matrixSingularValue (cubeSampledVandermonde M₁ μ.node W.val) (n - 1)
  let Q : FiniteSample (CubeFrequency d L) M₂ → Prop := fun Z =>
    Real.sqrt ((1 - ρ) * a) ≤
      matrixSingularValue (cubeSampledVandermonde M₂ μ.node Z.val) (n - 1)
  have hprob₁ : 1 - η / 2 ≤ probability P := by
    have h := fixedSeparatedCube_singularValues hd hL hn hm₁ hM₁N
      hρ0 hρ1 hηhalf0 hηhalf1 hqLow hqHigh μ.node hsep hsample₁'
    exact h.trans (probability_mono (fun W hW => hW.1))
  have hprob₂ : 1 - η / 2 ≤ probability Q := by
    have h := fixedSeparatedCube_singularValues hd hL hn hm₂ hM₂N
      hρ0 hρ1 hηhalf0 hηhalf1 hqLow hqHigh μ.node hsep hsample₂'
    exact h.trans (probability_mono (fun Z hZ => hZ.1))
  have hpair : 1 - η ≤ probability (fun pair :
      FiniteSample (CubeFrequency d L) M₁ ×
        FiniteSample (CubeFrequency d L) M₂ => P pair.1 ∧ Q pair.2) :=
    FiniteMatrixSampling.probability_product_lower_bound P Q η hprob₁ hprob₂
  apply hpair.trans
  apply probability_mono
  intro ⟨W, Z⟩ hgood
  exact positiveCubeGHM_numberDetection_of_singularValues μ W Z measurement hn0 hM₁ hM₂
    ha hρ1 hband hmeasurement hgood.1 hgood.2 hsmall

end
end LeanNumDetect.NumDetect
