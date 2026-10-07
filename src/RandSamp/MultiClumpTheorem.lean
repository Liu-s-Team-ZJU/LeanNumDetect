import RandSamp.MultiClumpSampling
import RandSamp.MultiClumpLeverage
import RandSamp.ClumpSingularLower
import RandSamp.ClumpSingularUpper

/-!
# Random row retention for fixed one-dimensional multiclump Vandermonde matrices

Manuscript `thm:multi-clump-random-sampling`. The absolute sampling constant
is `3072`; all geometry thresholds are chosen before `K`, `Δ`, bandwidth,
nodes, sampling cardinality, distortion, and failure probability.

Every analytic estimate, project conversion, random sampling step, and the
final assembly are proved. `RandSamp.MultiClumpAudit` checks that the
complete theorem has no transitive admissions or project axioms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect.RandSamp
noncomputable section

/-- Geometry alone supplies both the absolute leverage radius and the
full-matrix singular-value scaling, with the same geometry constants. -/
theorem multiClump_deterministic_control (n nstar : ℕ)
    (hnstar : 2 ≤ nstar) (hn : nstar ≤ n) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      MultiClumpDeterministicControl n nstar c0 C0 := by
  classical
  obtain ⟨d, hd, hSingle⟩ := singleClump_lower_thresholds nstar
  let B : ℕ → ℝ := fun s => if hs : 0 < s ∧ s ≤ nstar then
    Classical.choose (hSingle s hs.1 hs.2) else 1
  have hSingle' (s : ℕ) (hs : 0 < s) (hsstar : s ≤ nstar) :
      1 ≤ B s ∧
        ∀ (M : ℕ), B s ≤ (M : ℝ) →
          ∀ (Y : Fin s → ℝ), DistinctAngularNodes Y →
            ∀ c Δ : ℝ, 0 < c → c ≤ 1 / (s : ℝ) → 0 < Δ →
              (∀ i j, angularTorusDistance (Y i) (Y j) ≤ c / M) →
              (∀ i j, i ≠ j → Δ ≤ angularTorusDistance (Y i) (Y j)) →
              d * Real.sqrt (M : ℝ) *
                ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (s - 1) ≤
                  matrixSingularValue (ClusteredVandermonde.vandermonde M Y) (s - 1) := by
    have hboth : 0 < s ∧ s ≤ nstar := ⟨hs, hsstar⟩
    simpa only [B, dif_pos hboth] using Classical.choose_spec (hSingle s hs hsstar)
  obtain ⟨c0, C0, hc0, hc0one, hC0, hthreshold, hcross⟩ :=
    multiClump_subspace_thresholds n nstar hnstar hn
      (fun s => max (singleClumpGridThreshold s) (B s))
      (fun s => min (singleClumpRadius s) (1 / (s : ℝ)))
      (fun s hs _ => by
        have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
        exact lt_min (singleClumpRadius_pos s) (one_div_pos.mpr hsR))
  refine ⟨c0, C0, hc0, hc0one, hC0, ?_⟩
  let lower : ℝ → ℝ := fun _ =>
    d / (4 * (32 * Real.pi * Real.exp 1) ^ (nstar - 1))
  let upper : ℝ → ℝ := fun K =>
    2 * Real.sqrt (nstar : ℝ) * K ^ (nstar - 1) / ((nstar - 1).factorial : ℝ)
  refine ⟨lower, upper, ?_, ?_⟩
  · intro K hK
    have hstarR : (0 : ℝ) < nstar := by exact_mod_cast (show 0 < nstar by omega)
    dsimp [lower, upper]
    constructor <;> positivity
  · intro M hM A P Y hmax hgeometry
    have hn0 : 0 < n := by omega
    have hMR : (0 : ℝ) < M :=
      (by exact_mod_cast hn0 : (0 : ℝ) < n).trans_le (hC0.trans hM)
    have hM0 : 0 < M := by exact_mod_cast hMR
    have hM1 : 1 ≤ M := by omega
    have hpair := hcross M A hM Y P hmax hgeometry
    refine ⟨?_, ?_⟩
    · apply multiClump_leverage_of_geometry hn0 hM0 P Y hc0.le hc0one.le hgeometry
      · intro a
        exact (le_max_left _ _).trans
          ((hthreshold (P.size a) (P.size_pos a) (hmax.1 a)).1.trans hM)
      · intro a
        exact (hthreshold (P.size a) (P.size_pos a) (hmax.1 a)).2.trans
          (min_le_left _ _)
      · exact hpair
    · intro K hK Δ hΔ hspacing
      have hscaled : (M : ℝ) * Δ ≤ 1 :=
        (multiClump_scaledGap_le hnstar hMR Y P hmax hgeometry
          (fun i j hij hlabel => (hspacing i j hij hlabel).1)).trans hc0one.le
      have hclump (a : Fin A) :
          d * Real.sqrt (M : ℝ) *
            ((M : ℝ) * Δ / (32 * Real.pi * Real.exp 1)) ^ (P.size a - 1) ≤
              matrixSingularValue (ClusteredVandermonde.vandermonde M (P.nodes Y a))
                (P.size a - 1) := by
        have ht := hthreshold (P.size a) (P.size_pos a) (hmax.1 a)
        have hBMa : B (P.size a) ≤ (M : ℝ) :=
          (le_max_right _ _).trans (ht.1.trans hM)
        apply (hSingle' (P.size a) (P.size_pos a) (hmax.1 a)).2 M hBMa (P.nodes Y a)
          ?_ c0 Δ hc0 (ht.2.trans (min_le_right _ _)) hΔ ?_ ?_
        · intro i j hij p hp
          have hval : (P.enumeration a i).val ≠ (P.enumeration a j).val := by
            intro he
            exact hij ((P.enumeration a).injective (Subtype.ext he))
          exact hgeometry.distinct _ _ hval p hp
        · intro i j
          apply hgeometry.within
          rw [P.enumeration_label, P.enumeration_label]
        · intro i j hij
          have hval : (P.enumeration a i).val ≠ (P.enumeration a j).val := by
            intro he
            exact hij ((P.enumeration a).injective (Subtype.ext he))
          exact (hspacing _ _ hval (by rw [P.enumeration_label, P.enumeration_label])).1
      have hlo := multiClump_minimumSingularValue_lower_of_clump_singular_lower
        hn0 hM1 Y P hmax hd.le hΔ.le hscaled hpair hclump
      constructor
      · convert hlo using 1
        dsimp [lower]
        rw [div_pow]
        ring
      · exact multiclump_fullVandermonde_minSingularValue_upper
          hn0 hnstar hM1 Y P hmax hc0one hgeometry hΔ hK hspacing

/-- The full manuscript theorem, with an explicit absolute sampling constant
and no extra geometric, analytic, or probabilistic premises. -/
theorem multiClump_random_row_sampling :
    ∀ (n nstar : ℕ), 2 ≤ nstar → nstar ≤ n →
      ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
        MultiClumpSamplingConclusion multiClumpSamplingConstant n nstar c0 C0 := by
  intro n nstar hnstar hn
  obtain ⟨c0, C0, hc0, hc0one, hC0, hcontrol⟩ :=
    multiClump_deterministic_control n nstar hnstar hn
  exact ⟨c0, C0, hc0, hc0one, hC0,
    multiClump_sampling_of_deterministicControl (by omega) hC0 hcontrol⟩

/-- The existential-constant form of the proposed theorem. -/
theorem multiClump_sampling_statement : MultiClumpSamplingStatement :=
  ⟨multiClumpSamplingConstant, multiClumpSamplingConstant_pos, multiClump_random_row_sampling⟩

end
end LeanNumDetect.RandSamp
