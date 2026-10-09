import RandSamp.CubeClumpLeverage
import General.Fourier.SharpPolynomialEvaluation
import RandSamp.MultidimensionalClumpOptimizedSingularBounds
import RandSamp.MultidimensionalClumpQuantitativeSingularBounds
import RandSamp.MultidimensionalMultiClumpSampling

/-! Lower-only random Vandermonde sampling for the manuscript multiclump
model. Its constants are chosen before the bandwidth and fixed source set;
no upper spectral estimate or comparable-spacing assumption is exposed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open LeanNumDetect.FiniteMatrixSampling
open scoped BigOperators

namespace LeanNumDetect.RandSamp
noncomputable section

/-- The normalized internal interface underlying the unnormalized manuscript
statement. The separation is periodic one-norm spacing within each clump. -/
def MultidimensionalMultiClumpLowerSamplingConclusionWithConstant (d n nStar : ℕ)
    (c0 C0 samplingConstant : ℝ) : Prop :=
  ∀ (L A m : ℕ), C0 ≤ (L : ℝ) →
    ∀ (P : ClumpPartition n A) (Y : Fin n → Fin d → ℝ),
      HasMaxClumpSize P nStar → MultidimensionalMultiClumpGeometry L c0 C0 Y P →
      ∀ (Δ ρ ε : ℝ), 0 < Δ → MultidimensionalClumpL1SpacingLowerBound P Y Δ →
        1 ≤ m → m ≤ (L + 1) ^ d → 0 < ρ → ρ < 1 → 0 < ε → ε < 1 →
        samplingConstant / ρ ^ 2 *
          (P.sizePowerSum d : ℝ) * Real.log ((n : ℝ) / ε) ≤ (m : ℝ) →
        1 - ε ≤ probability (fun W : FiniteSample (CubeFrequency d L) m =>
          Real.sqrt (1 - ρ) * multidimensionalClumpOptimizedLowerConstant d nStar *
            ((L : ℝ) * Δ) ^ (nStar - 1) ≤
          matrixSingularValue (cubeSampledVandermonde m Y W.val) (n - 1))

def MultidimensionalMultiClumpLowerSamplingConclusion (d n nStar : ℕ)
    (c0 C0 : ℝ) : Prop :=
  ∀ (L A m : ℕ), C0 ≤ (L : ℝ) →
    ∀ (P : ClumpPartition n A) (Y : Fin n → Fin d → ℝ),
      HasMaxClumpSize P nStar → MultidimensionalMultiClumpGeometry L c0 C0 Y P →
      ∀ (Δ ρ ε : ℝ), 0 < Δ → MultidimensionalClumpL1SpacingLowerBound P Y Δ →
        1 ≤ m → m ≤ (L + 1) ^ d → 0 < ρ → ρ < 1 → 0 < ε → ε < 1 →
        multidimensionalMultiClumpLowerSamplingConstant d / ρ ^ 2 *
          (P.sizePowerSum d : ℝ) * Real.log ((n : ℝ) / ε) ≤ (m : ℝ) →
        1 - ε ≤ probability (fun W : FiniteSample (CubeFrequency d L) m =>
          Real.sqrt (1 - ρ) * multidimensionalClumpOptimizedLowerConstant d nStar *
            ((L : ℝ) * Δ) ^ (nStar - 1) ≤
          matrixSingularValue (cubeSampledVandermonde m Y W.val) (n - 1))

theorem multidimensionalMultiClump_lower_sampling_with_polynomial_bound
    (d : ℕ) (hd : 1 ≤ d) (n nStar : ℕ)
    (hStar : 2 ≤ nStar) (hsize : nStar ≤ n)
    {K : ℝ} (hK : 1 ≤ K)
    (hpoly : ∀ (s : ℕ), 0 < s → s ≤ nStar → ∀ (a : Fin s → ℂ) (x : ℝ),
      x ∈ Set.Icc (0 : ℝ) 1 →
      ‖PolynomialEvaluationBounds.jetPolynomialSignal a x‖^2 ≤ K * (s : ℝ)^2 *
        (∫ t in (0 : ℝ)..1, ‖PolynomialEvaluationBounds.jetPolynomialSignal a t‖^2)) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      MultidimensionalMultiClumpLowerSamplingConclusionWithConstant d n nStar c0 C0 (3 * K^d) := by
  classical
  let q : ℝ := K * multidimensionalClumpEvaluationLoss d
  have hK0 : 0 < K := by linarith
  have hq : K < q := by
    have h := mul_lt_mul_of_pos_left (multidimensionalClumpEvaluationLoss_gt_one hd) hK0
    simpa only [mul_one] using h
  obtain ⟨c0, C0, hc0, hc01, hC0, hlocal, hcontrol⟩ :=
    cubeClump_leverage_energy_thresholds_with_row_bound d n nStar hd hStar hsize
      hK hq (γ := 9/10) (by norm_num) (by norm_num) hpoly
      (fun _ => (8 * nStar : ℕ)) (fun _ => 1) (by intros; norm_num)
  have hthreshold : ((8 * nStar : ℕ) : ℝ) ≤ C0 := (hlocal 1 (by omega) (by omega)).1
  have hn : 0 < n := by omega
  refine ⟨c0, C0, hc0, hc01, hC0, ?_⟩
  intro L A m hL P Y hmax hgeom Δ ρ ε hΔ hgap hm hmN hρ0 hρ1 hε0 _hε1 hsample
  have hnL : n ≤ L := by exact_mod_cast hC0.trans hL
  have hLthreshold : 8 * nStar ≤ L := by exact_mod_cast hthreshold.trans hL
  obtain ⟨hraw, henergy⟩ := hcontrol L A hL Y P hmax hgeom
  let R := multidimensionalMultiClumpLowerLeverageConstant d * K^d * (P.sizePowerSum d : ℝ)
  have hR : 0 < R := by
    dsimp [R, multidimensionalMultiClumpLowerLeverageConstant]
    have hS : (0 : ℝ) < P.sizePowerSum d := by
      exact_mod_cast hn.trans_le (P.n_le_sizePowerSum hd)
    positivity
  have hrow (k : CubeFrequency d L) (z : EuclideanSpace ℂ (Fin n)) :
      cubeFourierRowEnergy Y k (ofLp z) ≤ R * FiniteMatrixSampling.quadratic (cubeFullGram L Y) z := by
    have hQ : 0 ≤ FiniteMatrixSampling.quadratic (cubeFullGram L Y) z := by
      rw [← cubeFourierSignal_average_energy]
      positivity
    have hS : 0 ≤ (P.sizePowerSum d : ℝ) := Nat.cast_nonneg _
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (multidimensionalClumpEvaluationLeverage_le hd hK0.le) hS) hQ
    exact (hraw k z).trans hc
  have hrate : 2 * R / ρ ^ 2 * Real.log ((n : ℝ) / ε) ≤ (m : ℝ) := by
    convert hsample using 1 <;>
      dsimp [R, multidimensionalMultiClumpLowerLeverageConstant] <;> ring
  have hprob := cubeFixedSupport_lowerGram_of_leverage hn hm hmN Y hR hρ0 hρ1 hε0
    (cube_fullGram_posDef_of_distinct hd hnL Y hgeom.distinct) hrow hrate
  have hfull := cube_multiclump_singular_lower_optimized hd hn hStar Y P hmax
    hLthreshold hc01.le hgeom hΔ hgap henergy
  apply hprob.trans
  apply probability_mono
  intro W hW
  have hs := cubeLowerGramEvent_singularValue Y hρ1.le W hW (show n - 1 < n by omega)
  calc
    _ = Real.sqrt (1 - ρ) *
        (multidimensionalClumpOptimizedLowerConstant d nStar *
          ((L : ℝ) * Δ) ^ (nStar - 1)) := by ring
    _ ≤ Real.sqrt (1 - ρ) * matrixSingularValue (cubeFullVandermonde L Y) (n - 1) :=
      mul_le_mul_of_nonneg_left hfull (Real.sqrt_nonneg _)
    _ ≤ _ := hs


/-- Sharp polynomial evaluation and adjustable geometric losses give the
absolute sampling coefficient three in every positive dimension. -/
theorem multidimensionalMultiClump_lower_sampling
    (d : ℕ) (hd : 1 ≤ d) (n nStar : ℕ)
    (hStar : 2 ≤ nStar) (hsize : nStar ≤ n) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      MultidimensionalMultiClumpLowerSamplingConclusion d n nStar c0 C0 := by
  have h := multidimensionalMultiClump_lower_sampling_with_polynomial_bound
    d hd n nStar hStar hsize (K := 1) (by norm_num)
    (fun s hs _ a x hx => by
      simpa only [one_mul] using
        PolynomialEvaluationBounds.jetPolynomial_unit_row_bound_sharp hs a hx)
  simpa only [MultidimensionalMultiClumpLowerSamplingConclusion,
    MultidimensionalMultiClumpLowerSamplingConclusionWithConstant,
    multidimensionalMultiClumpLowerSamplingConstant, one_pow, mul_one] using h

open QuantitativeClumpSectionBounds

/-- The bandwidth and interclump separation thresholds are independent. -/
def QuantitativeMultiClumpLowerSamplingConclusion (d n nStar : ℕ)
    (c0 C0 Csep : ℝ) : Prop :=
  ∀ (L A m : ℕ), C0 ≤ (L : ℝ) →
    ∀ (P : ClumpPartition n A) (Y : Fin n → Fin d → ℝ),
      HasMaxClumpSize P nStar → MultidimensionalMultiClumpGeometry L c0 Csep Y P →
      ∀ (Δ ρ ε : ℝ), 0 < Δ → MultidimensionalClumpL1SpacingLowerBound P Y Δ →
        1 ≤ m → m ≤ (L + 1)^d → 0 < ρ → ρ < 1 → 0 < ε → ε < 1 →
        3 / ρ^2 * (P.sizePowerSum d : ℝ) * Real.log ((n : ℝ) / ε) ≤ (m : ℝ) →
        1 - ε ≤ probability (fun W : FiniteSample (CubeFrequency d L) m =>
          Real.sqrt (1 - ρ) * multidimensionalClumpOptimizedLowerConstant d nStar *
            ((L : ℝ) * Δ)^(nStar - 1) ≤
          matrixSingularValue (cubeSampledVandermonde m Y W.val) (n - 1))

theorem multidimensionalMultiClump_lowerGram_sampling_explicit
    (d : ℕ) (hd : 1 ≤ d) (n nStar : ℕ) (hStar : 2 ≤ nStar) (hsize : nStar ≤ n) :
    let hnStar0 : 0 < nStar := by omega
    let c0 := quantitativeClumpRadius d (n - nStar) nStar hnStar0
    let C0 := quantitativeClumpBandwidth d n nStar hnStar0
    let Csep := quantitativeClumpSeparation d n nStar hnStar0
    ∀ (L A m : ℕ), C0 ≤ (L : ℝ) →
      ∀ (P : ClumpPartition n A) (Y : Fin n → Fin d → ℝ),
        HasMaxClumpSize P nStar → MultidimensionalMultiClumpGeometry L c0 Csep Y P →
        ∀ (ρ ε : ℝ), 1 ≤ m → m ≤ (L + 1)^d → 0 < ρ → ρ < 1 → 0 < ε →
          3 / ρ^2 * (P.sizePowerSum d : ℝ) * Real.log ((n : ℝ) / ε) ≤ (m : ℝ) →
          1 - ε ≤ probability (fun W : FiniteSample (CubeFrequency d L) m => CubeLowerGramEvent Y ρ W) := by
  classical
  dsimp only
  obtain ⟨_, _, hC0, _, hcontrol⟩ := cubeClump_quantitative_leverage_energy d n nStar hd hStar hsize
  intro L A m hL P Y hmax hgeom ρ ε hm hmN hρ0 hρ1 hε0 hsample
  have hn : 0 < n := by omega
  have hnL : n ≤ L := by exact_mod_cast hC0.trans hL
  obtain ⟨hrow, _⟩ := hcontrol L A hL Y P hmax hgeom
  let R : ℝ := (3 / 2 : ℝ) * (P.sizePowerSum d : ℝ)
  have hR : 0 < R := by
    have hS : (0 : ℝ) < P.sizePowerSum d := by exact_mod_cast hn.trans_le (P.n_le_sizePowerSum hd)
    dsimp [R]
    positivity
  have hrate : 2 * R / ρ^2 * Real.log ((n : ℝ) / ε) ≤ (m : ℝ) := by
    convert hsample using 1
    dsimp [R]
    ring
  exact cubeFixedSupport_lowerGram_of_leverage hn hm hmN Y hR hρ0 hρ1 hε0
    (cube_fullGram_posDef_of_distinct hd hnL Y hgeom.distinct) hrow hrate

/-- Explicit finite formulas provide the same spectral lower coefficient and
absolute sampling coefficient three, with separate geometry thresholds. -/
theorem multidimensionalMultiClump_lower_sampling_explicit
    (d : ℕ) (hd : 1 ≤ d) (n nStar : ℕ) (hStar : 2 ≤ nStar) (hsize : nStar ≤ n) :
    let hnStar0 : 0 < nStar := by omega
    let c0 := quantitativeClumpRadius d (n - nStar) nStar hnStar0
    let C0 := quantitativeClumpBandwidth d n nStar hnStar0
    let Csep := quantitativeClumpSeparation d n nStar hnStar0
    0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧ 16 * (nStar : ℝ) ≤ C0 ∧
      QuantitativeMultiClumpLowerSamplingConclusion d n nStar c0 C0 Csep := by
  classical
  dsimp only
  obtain ⟨hc0, hc01, hC0, hC016, hcontrol⟩ := cubeClump_quantitative_leverage_energy d n nStar hd hStar hsize
  refine ⟨hc0, hc01, hC0, hC016, ?_⟩
  intro L A m hL P Y hmax hgeom Δ ρ ε hΔ hgap hm hmN hρ0 hρ1 hε0 _hε1 hsample
  have hn : 0 < n := by omega
  have hL16 : 16*nStar ≤ L := by exact_mod_cast hC016.trans hL
  obtain ⟨_, henergy⟩ := hcontrol L A hL Y P hmax hgeom
  have hprob := multidimensionalMultiClump_lowerGram_sampling_explicit d hd n nStar hStar hsize
    L A m hL P Y hmax hgeom ρ ε hm hmN hρ0 hρ1 hε0 hsample
  have hfull := cube_multiclump_singular_lower_quantitative_originalConstant hd hn hStar Y P hmax
    hL16 hc01.le hgeom hΔ hgap henergy
  apply hprob.trans
  apply probability_mono
  intro W hW
  have hs := cubeLowerGramEvent_singularValue Y hρ1.le W hW (show n - 1 < n by omega)
  calc
    _ = Real.sqrt (1 - ρ) * (multidimensionalClumpOptimizedLowerConstant d nStar *
        ((L : ℝ) * Δ)^(nStar - 1)) := by ring
    _ ≤ Real.sqrt (1 - ρ) * matrixSingularValue (cubeFullVandermonde L Y) (n - 1) :=
      mul_le_mul_of_nonneg_left hfull (Real.sqrt_nonneg _)
    _ ≤ _ := hs

end
end LeanNumDetect.RandSamp
