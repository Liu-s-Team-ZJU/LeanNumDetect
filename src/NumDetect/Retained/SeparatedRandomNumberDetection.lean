import NumDetect.Random.CubeNumberDetection
import NumDetect.Retained.SeparatedRandomMUSIC

/-! Retained well-separated random-GHM number-detection result. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open LeanNumDetect.FiniteMatrixSampling LeanNumDetect.RandSamp
open scoped BigOperators Matrix.Norms.L2Operator

namespace LeanNumDetect.NumDetect
noncomputable section

/-- The well-separated random-GHM number-detection consequence under the
    same sampling and noise conditions as its MUSIC corollary. -/
theorem positiveCubeGHM_numberDetection_highProbability
    {d L n M₁ M₂ : ℕ} (μ : AtomicMeasure d n)
    (measurement : Point d → ℂ)
    (hd : 1 ≤ d) (hL : 1 ≤ L) (hn : 2 ≤ n)
    (hsource : ∀ j, InAngularCube (μ.node j))
    (hM₁ : n < M₁) (hM₂ : n ≤ M₂)
    (hM₁N : M₁ ≤ (L + 1) ^ d) (hM₂N : M₂ ≤ (L + 1) ^ d)
    {Ω σ ρ ε : ℝ}
    (hband : (2 * L : ℝ) ≤ Ω)
    (hmeasurement : IsBandMeasurement μ Ω σ measurement)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hqLow :
      2 * Real.pi * (2 * (d : ℝ) - 1) / L <
        periodicMinimumLInfSeparation μ.node hn)
    (hsample₁ :
      3 * (n : ℝ) /
        (cubeSeparatedLower d L (periodicMinimumLInfSeparation μ.node hn) * ρ ^ 2) *
        Real.log (4 * n / ε) ≤ M₁)
    (hsample₂ :
      3 * (n : ℝ) /
        (cubeSeparatedLower d L (periodicMinimumLInfSeparation μ.node hn) * ρ ^ 2) *
        Real.log (4 * n / ε) ≤ M₂)
    (hsmall : 2 * σ < minAmplitude μ (Nat.zero_lt_of_lt hn) *
      ((1 - ρ) * cubeSeparatedLower d L
        (periodicMinimumLInfSeparation μ.node hn))) :
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
  have hεhalf0 : 0 < ε / 2 := by positivity
  have hεhalf1 : ε / 2 < 1 := by linarith
  have hlog : 2 * (n : ℝ) / (ε / 2) = 4 * (n : ℝ) / ε := by
    have hεne : ε ≠ 0 := ne_of_gt hε0
    field_simp
    ring
  have hsample₁' :
      3 * (n : ℝ) / (a * ρ ^ 2) * Real.log (2 * n / (ε / 2)) ≤ M₁ := by
    rw [hlog]
    exact hsample₁
  have hsample₂' :
      3 * (n : ℝ) / (a * ρ ^ 2) * Real.log (2 * n / (ε / 2)) ≤ M₂ := by
    rw [hlog]
    exact hsample₂
  let P : FiniteSample (CubeFrequency d L) M₁ → Prop := fun W =>
    Real.sqrt ((1 - ρ) * a) ≤
      matrixSingularValue (cubeSampledVandermonde M₁ μ.node W.val) (n - 1)
  let Q : FiniteSample (CubeFrequency d L) M₂ → Prop := fun Z =>
    Real.sqrt ((1 - ρ) * a) ≤
      matrixSingularValue (cubeSampledVandermonde M₂ μ.node Z.val) (n - 1)
  have hprob₁ : 1 - ε / 2 ≤ probability P := by
    have h := fixedSeparatedCube_singularValues hd hL hn hm₁ hM₁N
      hρ0 hρ1 hεhalf0 hεhalf1 hqLow hqHigh μ.node hsep hsample₁'
    exact h.trans (probability_mono (fun W hW => hW.1))
  have hprob₂ : 1 - ε / 2 ≤ probability Q := by
    have h := fixedSeparatedCube_singularValues hd hL hn hm₂ hM₂N
      hρ0 hρ1 hεhalf0 hεhalf1 hqLow hqHigh μ.node hsep hsample₂'
    exact h.trans (probability_mono (fun Z hZ => hZ.1))
  have hpair : 1 - ε ≤ probability (fun pair :
      FiniteSample (CubeFrequency d L) M₁ ×
        FiniteSample (CubeFrequency d L) M₂ => P pair.1 ∧ Q pair.2) :=
    FiniteMatrixSampling.probability_product_lower_bound P Q ε hprob₁ hprob₂
  apply hpair.trans
  apply probability_mono
  intro ⟨W, Z⟩ hgood
  exact positiveCubeGHM_numberDetection_of_singularValues μ W Z measurement hn0 hM₁ hM₂
    ha hρ1 hband hmeasurement hgood.1 hgood.2 hsmall

end
end LeanNumDetect.NumDetect
