import RandSamp.CubeClumpLeverage
import RandSamp.MultidimensionalClumpSingularBounds
import RandSamp.MultidimensionalClumpUpper
import RandSamp.MultidimensionalClumpSharpnessBounds

/-! The complete multidimensional random-retained-row multiclump theorem.
The model is NumDetect's periodic infinity-metric model with arbitrary
internal arrangement. All deterministic geometry and probability inputs
are discharged; dimension one is recovered only afterward by reindexing. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect.RandSamp
noncomputable section

/-- One common choice of geometry thresholds proves positive definiteness,
the gap-free row radius, and the full-cube spectral estimates. -/
theorem multidimensionalMultiClump_deterministic_control_with_threshold (d : ℕ) (hd : 1 ≤ d)
    (n nstar : ℕ) (hnstar : 2 ≤ nstar) (hn : nstar ≤ n) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      multidimensionalClumpLowerThreshold n ≤ C0 ∧
      MultidimensionalMultiClumpDeterministicControl d n nstar c0 C0 := by
  obtain ⟨c0, C0, hc0, hc01, hC0, hlocal, hrow⟩ :=
    cubeClump_leverage_thresholds d n nstar hd hnstar hn
      (fun _ => multidimensionalClumpLowerThreshold n) (fun _ => 1)
      (by intros; norm_num)
  have hthreshold : multidimensionalClumpLowerThreshold n ≤ C0 :=
    (hlocal 1 (by norm_num) (by omega)).1
  have hn0 : 0 < n := by omega
  let lower : ℝ → ℝ := fun _ => multidimensionalClumpLowerConstant d n nstar
  let upper : ℝ → ℝ := multidimensionalClumpUpperConstant d nstar
  refine ⟨c0, C0, hc0, hc01, hC0, hthreshold, lower, upper, ?_, ?_⟩
  · intro K hK
    exact ⟨multidimensionalClumpLowerConstant_pos hd hn0,
      multidimensionalClumpUpperConstant_pos hd hnstar hK⟩
  · intro M hM A P Y hmax hgeom
    have hnM : n ≤ M := by exact_mod_cast (hC0.trans hM)
    have hM0 : 0 < M := lt_of_lt_of_le hn0 hnM
    refine ⟨cube_fullGram_posDef_of_distinct hd hnM Y hgeom.distinct, ?_, ?_⟩
    · simpa only [multidimensionalMultiClumpLeverageConstant] using
        hrow M A hM Y P hmax hgeom
    · intro K hK Δ hΔ hspacing
      constructor
      · apply cube_multiclump_singular_lower hd hn0 hnstar Y P hmax
          (hthreshold.trans hM) hthreshold hc01.le hgeom hΔ
        intro i j hij hlabel
        exact ((hspacing i j hij hlabel).1).trans
          (multidimensionalAngularTorusDistance_le_l1 hd (Y i) (Y j))
      · exact cube_multiclump_singular_upper hd hn0 hnstar hM0 Y P hmax
          hc01.le hgeom hΔ hK hspacing

/-- The concrete thresholds discharge every deterministic premise of the
sampling theorem. -/
theorem multidimensionalMultiClump_deterministic_control (d : ℕ) (hd : 1 ≤ d)
    (n nstar : ℕ) (hnstar : 2 ≤ nstar) (hn : nstar ≤ n) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      MultidimensionalMultiClumpDeterministicControl d n nstar c0 C0 := by
  obtain ⟨c0, C0, hc0, hc01, hC0, _, hcontrol⟩ :=
    multidimensionalMultiClump_deterministic_control_with_threshold d hd n nstar hnstar hn
  exact ⟨c0, C0, hc0, hc01, hC0, hcontrol⟩

/-- Main manuscript theorem, with `3072*512^(d-1)` fixed before every node
configuration and no analytic or probabilistic premise in the conclusion. -/
theorem multidimensionalMultiClump_random_row_sampling :
    MultidimensionalMultiClumpSamplingStatement := by
  apply multidimensionalMultiClump_statement_of_deterministicControl
  exact multidimensionalMultiClump_deterministic_control

/-- On a relative Gram event the sharp lower estimate needs only lower
within-clump spacing in NumDetect's periodic one-norm. No comparable-spacing
or internal-arrangement condition enters this result. -/
theorem cube_multiclump_sampled_singular_lower {d n A M m nstar : ℕ}
    (hd : 1 ≤ d) (hn : 0 < n) (hnstar : 2 ≤ nstar)
    (Y : Fin n → Fin d → ℝ) (P : ClumpPartition n A) (hmax : HasMaxClumpSize P nstar)
    {c0 C0 Δ ρ : ℝ}
    (hM : multidimensionalClumpLowerThreshold n ≤ (M : ℝ))
    (hC0 : multidimensionalClumpLowerThreshold n ≤ C0) (hc0 : c0 ≤ 1)
    (hgeom : MultidimensionalMultiClumpGeometry M c0 C0 Y P)
    (hΔ : 0 < Δ) (hgap : MultidimensionalClumpL1SpacingLowerBound P Y Δ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (Ω : FiniteMatrixSampling.FiniteSample (CubeFrequency d M) m)
    (hrelative : CubeRelativeGramEvent Y ρ Ω) :
    multidimensionalClumpLowerConstant d n nstar * Real.sqrt (1 - ρ) *
        ((M : ℝ) * Δ) ^ (nstar - 1) ≤
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (n - 1) := by
  have hfull := cube_multiclump_singular_lower hd hn hnstar Y P hmax hM hC0 hc0 hgeom hΔ hgap
  have hs := cubeAllSingularValueEvent_of_relativeGramEvent Y hρ0 hρ1 Ω hrelative
    (⟨n - 1, by omega⟩ : Fin n)
  calc
    _ = Real.sqrt (1 - ρ) *
        (multidimensionalClumpLowerConstant d n nstar * ((M : ℝ) * Δ) ^ (nstar - 1)) := by ring
    _ ≤ Real.sqrt (1 - ρ) * matrixSingularValue (cubeFullVandermonde M Y) (n - 1) :=
      mul_le_mul_of_nonneg_left hfull (Real.sqrt_nonneg _)
    _ ≤ _ := hs.1

/-- The main sampling conclusion and the sharp lower estimate without
comparable spacings share one choice of geometry constants and one Gram
event. This jointly formalizes the manuscript theorem and its lower-order
proposition, with no additional premise on the source arrangement. -/
theorem multidimensionalMultiClump_sampling_with_sharp_lower (d : ℕ) (hd : 1 ≤ d)
    (n nstar : ℕ) (hnstar : 2 ≤ nstar) (hn : nstar ≤ n) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      MultidimensionalMultiClumpSamplingConclusion
        (multidimensionalMultiClumpSamplingConstant d) d n nstar c0 C0 ∧
      ∀ (M A m : ℕ), C0 ≤ (M : ℝ) → ∀ (P : ClumpPartition n A)
        (Y : Fin n → Fin d → ℝ), HasMaxClumpSize P nstar →
          MultidimensionalMultiClumpGeometry M c0 C0 Y P →
          ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
            ∀ Ω : FiniteMatrixSampling.FiniteSample (CubeFrequency d M) m,
              CubeRelativeGramEvent Y ρ Ω → ∀ Δ : ℝ, 0 < Δ →
                MultidimensionalClumpL1SpacingLowerBound P Y Δ →
                multidimensionalClumpLowerConstant d n nstar * Real.sqrt (1 - ρ) *
                    ((M : ℝ) * Δ) ^ (nstar - 1) ≤
                  matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (n - 1) := by
  obtain ⟨c0, C0, hc0, hc01, hC0, hthreshold, hcontrol⟩ :=
    multidimensionalMultiClump_deterministic_control_with_threshold d hd n nstar hnstar hn
  refine ⟨c0, C0, hc0, hc01, hC0,
    multidimensionalMultiClump_sampling_of_deterministicControl hd (by omega) hcontrol, ?_⟩
  intro M A m hM P Y hmax hgeom ρ hρ0 hρ1 Ω hrelative Δ hΔ hgap
  exact cube_multiclump_sampled_singular_lower hd (by omega) hnstar Y P hmax
    (hthreshold.trans hM) hthreshold hc01.le hgeom hΔ hgap hρ0 hρ1 Ω hrelative

end
end LeanNumDetect.RandSamp
