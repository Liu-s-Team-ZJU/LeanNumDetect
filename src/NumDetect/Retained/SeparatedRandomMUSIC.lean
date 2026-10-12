import NumDetect.Random.CubeMUSIC
import NumDetect.Preliminaries.PeriodicGeometry
import NumDetect.Segmented.WellSeparated
import RandSamp.FixedSeparatedCube

/-! Retained well-separated random-cube Vandermonde and MUSIC results. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open LeanNumDetect.FiniteMatrixSampling
open LeanNumDetect.RandSamp
open scoped BigOperators

namespace LeanNumDetect.NumDetect

noncomputable section

/-- The manuscript's periodic minimum separation implies the separation
hypothesis used by the random cube theorem. -/
theorem periodicMinimumLInfSeparation_cubeAngularSeparated
    {d s : ℕ} (Y : Fin s → Fin d → ℝ) (hs : 2 ≤ s)
    (hY : ∀ j, InAngularCube (Y j))
    (hqpos : 0 < periodicMinimumLInfSeparation Y hs) :
    CubeAngularSeparated (periodicMinimumLInfSeparation Y hs) Y := by
  intro i j hij
  let q := periodicMinimumLInfSeparation Y hs
  have hqle : q ≤ periodicLInfDistance (Y i) (Y j) :=
    periodicMinimumLInfSeparation_le Y hs hij
  by_contra hnot
  have hcomponent : ∀ k : Fin d,
      periodicCoordinateDistance (Y i k) (Y j k) < q := by
    intro k
    by_contra hnotk
    have hqk : q ≤ periodicCoordinateDistance (Y i k) (Y j k) :=
      le_of_not_gt hnotk
    apply hnot
    refine ⟨k, ?_⟩
    intro p
    have htranslate := periodicCoordinateDistance_le_integerTranslate
      (hY i k) (hY j k) (-p)
    have htranslate' : periodicCoordinateDistance (Y i k) (Y j k) ≤
        |Y i k - Y j k + 2 * Real.pi * p| := by
      simpa only [Int.cast_neg, mul_neg, sub_neg_eq_add] using htranslate
    exact hqk.trans htranslate'
  have hnorm : periodicLInfDistance (Y i) (Y j) < q := by
    unfold periodicLInfDistance
    apply (pi_norm_lt_iff hqpos).2
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg
      (periodicCoordinateDistance_nonneg (hY i k) (hY j k))]
    exact hcomponent k
  exact (not_lt_of_ge hqle) hnorm

/-- The angular periodic infinity separation never exceeds π; this fact is
    derived from the manuscript model rather than added as a theorem premise. -/
theorem periodicMinimumLInfSeparation_le_pi
    {d n : ℕ} (Y : Fin n → Point d) (hn : 2 ≤ n)
    (hY : ∀ j, InAngularCube (Y j)) :
    periodicMinimumLInfSeparation Y hn ≤ Real.pi := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  apply (periodicMinimumLInfSeparation_le Y hn hij).trans
  unfold periodicLInfDistance
  apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).2
  intro r
  rw [Real.norm_eq_abs, abs_of_nonneg
    (periodicCoordinateDistance_nonneg (hY i r) (hY j r))]
  unfold periodicCoordinateDistance
  by_cases h : |Y i r - Y j r| ≤ Real.pi
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

/-- The lower-only random cube Vandermonde statement in the manuscript.
    The periodic upper spacing bound is derived from angular representatives. -/
theorem positiveCubeVandermonde_lower_highProbability
    {d L n m : ℕ} (Y : Fin n → Point d)
    (hd : 1 ≤ d) (hL : 1 ≤ L) (hn : 2 ≤ n)
    (hsource : ∀ j, InAngularCube (Y j))
    (hm : 1 ≤ m) (hmN : m ≤ (L + 1) ^ d)
    {ρ ε : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hqLow : 2 * Real.pi * (2 * (d : ℝ) - 1) / L <
      periodicMinimumLInfSeparation Y hn)
    (hsample : 3 * (n : ℝ) /
      (cubeSeparatedLower d L (periodicMinimumLInfSeparation Y hn) * ρ ^ 2) *
      Real.log (2 * n / ε) ≤ m) :
    1 - ε ≤ probability (fun W : FiniteSample (CubeFrequency d L) m =>
      Real.sqrt ((1 - ρ) * cubeSeparatedLower d L
        (periodicMinimumLInfSeparation Y hn)) ≤
      matrixSingularValue (cubeSampledVandermonde m Y W.val) (n - 1)) := by
  have hqpos := cube_separation_pos hd hL hqLow
  have hsep := periodicMinimumLInfSeparation_cubeAngularSeparated Y hn hsource hqpos
  have h := fixedSeparatedCube_singularValues hd hL hn hm hmN
    hρ0 hρ1 hε0 hε1 hqLow (periodicMinimumLInfSeparation_le_pi Y hn hsource)
    Y hsep hsample
  exact h.trans (probability_mono fun W hW => hW.1)

/-- High-probability MUSIC correlation stability for two independent positive
    cube samples. The source set is fixed before drawing either sample. -/
theorem positiveCubeMUSIC_correlation_stability_highProbability
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
        FiniteSample (CubeFrequency d L) M₁ ×
          FiniteSample (CubeFrequency d L) M₂ =>
      correlationUniformDistance
        (rankNoiseSpaceCorrelation (positiveCubeFrequency pair.1)
          (generalizedHankel (positiveCubeFrequency pair.1)
            (positiveCubeFrequency pair.2) measurement) n)
        (rankNoiseSpaceCorrelation (positiveCubeFrequency pair.1)
          (generalizedHankel (positiveCubeFrequency pair.1)
            (positiveCubeFrequency pair.2) (fourier μ)) n) ≤
        2 * σ /
          (minAmplitude μ (Nat.zero_lt_of_lt hn) *
            ((1 - ρ) * cubeSeparatedLower d L
              (periodicMinimumLInfSeparation μ.node hn)))) := by
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
  have hE : matrixSpectralNorm
      (generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z)
          measurement -
        generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z)
          (fourier μ)) ≤ σ * Real.sqrt (M₁ * M₂) :=
    (positiveCubeGHM_noise_spectralNorm_lt W Z μ measurement hmeasurement
      hband (by omega) (by omega)).le
  have hdet := positiveCubeMUSIC_correlation_stability_of_singularValues
    μ W Z
    (generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z)
        measurement -
      generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z)
        (fourier μ))
    hn0 hM₁ hM₂ ha hρ1 hgood.1 hgood.2 hE hsmall
  have hfactor :
      generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z)
          (fourier μ) =
        generalizedVandermonde (positiveCubeFrequency W) μ.node *
          Matrix.diagonal μ.amplitude *
          Matrix.transpose
            (generalizedVandermonde (positiveCubeFrequency Z) μ.node) :=
    generalizedHankel_fourier_eq_hankelVandermondeFactor
      (positiveCubeFrequency W) (positiveCubeFrequency Z) μ
  rw [← hfactor] at hdet
  have hcancel :
      generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z)
          (fourier μ) +
        (generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z)
            measurement -
          generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z)
            (fourier μ)) =
        generalizedHankel (positiveCubeFrequency W) (positiveCubeFrequency Z)
          measurement := by abel
  rw [hcancel] at hdet
  exact hdet

end
end LeanNumDetect.NumDetect
