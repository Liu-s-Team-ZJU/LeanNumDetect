import NumDetect.Uniform
import NumDetect.CRLLowerBound
import NumDetect.CRLFeasible
import NumDetect.CRLAttainment

/-! Computational resolution limit bounds from the NumDetect manuscript. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

private theorem numberDetectionSeparationThreshold_nonneg
    {d n : ℕ} {Ω σ mMin : ℝ}
    (hn : 2 ≤ n) (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin) :
    0 ≤ numberDetectionSeparationThreshold d n Ω σ mMin := by
  have hmMin : 0 < mMin := hσ.trans hnoise
  unfold numberDetectionSeparationThreshold
  positivity

/-- Every separation strictly above the explicit threshold guarantees number detection. -/
private theorem numberDetectionGuarantee_of_threshold_lt
    {d n : ℕ} {Ω σ mMin D : ℝ}
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin)
    (hD : numberDetectionSeparationThreshold d n Ω σ mMin < D) :
    NumberDetectionGuarantee d n (.finite 1 le_rfl) Ω σ mMin D
      (Nat.zero_lt_of_lt hn) := by
  intro μ hmMin hcluster hseparation Y hmeasurement k ν hadmissible
  have hDmin : D ≤ minimumL1Separation μ.node hn := by
    rw [minimumL1Separation, minimumOverDistinctPairs]
    apply Finset.le_inf' (distinctPairs_nonempty hn)
    intro ij hij
    have hne : ij.1 ≠ ij.2 := by
      simpa [distinctPairs] using hij
    simpa [normAt, lpNorm, l1Norm] using
      hseparation ij.1 ij.2 hne
  have hstrict :
      numberDetectionSeparationThreshold d n Ω σ mMin <
        minimumL1Separation μ.node hn :=
    hD.trans_le hDmin
  by_contra hk
  apply noAdmissibleMeasureWithFewerSupports
    μ Y hd hn hΩ hσ hmMin hcluster hnoise hstrict hmeasurement
  exact ⟨k, ν, Nat.lt_of_not_ge hk, hadmissible⟩

/-- The infimum of nonnegative feasible values is at most an open feasibility threshold. -/
private theorem sInf_nonnegative_predicate_le
    {P : ℝ → Prop} {T : ℝ}
    (hT : 0 ≤ T) (hP : ∀ D, T < D → P D) :
    sInf {D : ℝ | 0 ≤ D ∧ P D} ≤ T := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro D hTD
  apply csInf_le
  · exact ⟨0, by
      intro E hE
      exact hE.1⟩
  · exact ⟨hT.trans hTD.le, hP D hTD⟩

/-- A nonempty upward-closed feasible set contains its infimum when failure
persists at some strictly larger threshold. -/
private theorem sInf_nonnegative_predicate_attained
    {P : ℝ → Prop}
    (hne : ∃ D : ℝ, 0 ≤ D ∧ P D)
    (hmono : ∀ {D E : ℝ}, D ≤ E → P D → P E)
    (hfailure : ∀ D : ℝ, ¬P D → ∃ E : ℝ, D < E ∧ ¬P E) :
    0 ≤ sInf {D : ℝ | 0 ≤ D ∧ P D} ∧
      P (sInf {D : ℝ | 0 ≤ D ∧ P D}) := by
  have hset : ({D : ℝ | 0 ≤ D ∧ P D} : Set ℝ).Nonempty := hne
  constructor
  · exact le_csInf hset (fun D hD => hD.1)
  · by_contra hnot
    obtain ⟨E, hlt, hnotE⟩ := hfailure _ hnot
    have hE : E ≤ sInf {D : ℝ | 0 ≤ D ∧ P D} := by
      apply le_csInf hset
      intro D hD
      by_contra hED
      exact hnotE (hmono (le_of_lt (lt_of_not_ge hED)) hD.2)
    exact (not_lt_of_ge hE) hlt

/-- Increasing the required separation preserves a number-detection guarantee. -/
private theorem numberDetectionGuarantee_mono
    {d n : ℕ} {p : LpIndex} {Ω σ mMin D E : ℝ} {hn : 0 < n}
    (hDE : D ≤ E)
    (hD : NumberDetectionGuarantee d n p Ω σ mMin D hn) :
    NumberDetectionGuarantee d n p Ω σ mMin E hn := by
  intro μ hmMin hcluster hseparation Y hmeasurement k ν hadmissible
  apply hD μ hmMin hcluster
  · intro i j hij
    exact hDE.trans (hseparation i j hij)
  · exact hmeasurement
  · exact hadmissible

/-- Increasing the required separation preserves a positive-amplitude guarantee. -/
private theorem positiveNumberDetectionGuarantee_mono
    {d n : ℕ} {p : LpIndex} {Ω σ mMin D E : ℝ} {hn : 0 < n}
    (hDE : D ≤ E)
    (hD : PositiveNumberDetectionGuarantee d n p Ω σ mMin D hn) :
    PositiveNumberDetectionGuarantee d n p Ω σ mMin E hn := by
  intro μ hpositive hmMin hcluster hseparation Y hmeasurement k ν hadmissible
  apply hD μ hpositive hmMin hcluster
  · intro i j hij
    exact hDE.trans (hseparation i j hij)
  · exact hmeasurement
  · exact hadmissible

private theorem numberDetectionCRL_isSmallest_of_failure_extension
    {d n : ℕ} (p : LpIndex) {Ω σ mMin : ℝ}
    (hn : 2 ≤ n) (hΩ : 0 < Ω)
    (hfailure : ∀ D : ℝ,
      ¬NumberDetectionGuarantee d n p Ω σ mMin D (Nat.zero_lt_of_lt hn) →
      ∃ E : ℝ, D < E ∧
        ¬NumberDetectionGuarantee d n p Ω σ mMin E (Nat.zero_lt_of_lt hn)) :
    0 ≤ numberDetectionCRL d n p Ω σ mMin (Nat.zero_lt_of_lt hn) ∧
      NumberDetectionGuarantee d n p Ω σ mMin
        (numberDetectionCRL d n p Ω σ mMin (Nat.zero_lt_of_lt hn))
        (Nat.zero_lt_of_lt hn) ∧
      ∀ D : ℝ, 0 ≤ D →
        NumberDetectionGuarantee d n p Ω σ mMin D (Nat.zero_lt_of_lt hn) →
        numberDetectionCRL d n p Ω σ mMin (Nat.zero_lt_of_lt hn) ≤ D := by
  unfold numberDetectionCRL
  have hne : ∃ D : ℝ, 0 ≤ D ∧
      NumberDetectionGuarantee d n p Ω σ mMin D (Nat.zero_lt_of_lt hn) :=
    exists_numberDetectionGuarantee p hΩ (Nat.zero_lt_of_lt hn) hn
  have hatt := sInf_nonnegative_predicate_attained hne
    (fun hDE hD => numberDetectionGuarantee_mono hDE hD) hfailure
  refine ⟨hatt.1, hatt.2, ?_⟩
  intro D hD hguarantee
  exact csInf_le ⟨0, fun E hE => hE.1⟩ ⟨hD, hguarantee⟩

private theorem positiveNumberDetectionCRL_isSmallest_of_failure_extension
    {d n : ℕ} (p : LpIndex) {Ω σ mMin : ℝ}
    (hn : 2 ≤ n) (hΩ : 0 < Ω)
    (hfailure : ∀ D : ℝ,
      ¬PositiveNumberDetectionGuarantee d n p Ω σ mMin D
        (Nat.zero_lt_of_lt hn) →
      ∃ E : ℝ, D < E ∧
        ¬PositiveNumberDetectionGuarantee d n p Ω σ mMin E
          (Nat.zero_lt_of_lt hn)) :
    0 ≤ positiveNumberDetectionCRL d n p Ω σ mMin (Nat.zero_lt_of_lt hn) ∧
      PositiveNumberDetectionGuarantee d n p Ω σ mMin
        (positiveNumberDetectionCRL d n p Ω σ mMin (Nat.zero_lt_of_lt hn))
        (Nat.zero_lt_of_lt hn) ∧
      ∀ D : ℝ, 0 ≤ D →
        PositiveNumberDetectionGuarantee d n p Ω σ mMin D
          (Nat.zero_lt_of_lt hn) →
        positiveNumberDetectionCRL d n p Ω σ mMin (Nat.zero_lt_of_lt hn) ≤ D := by
  unfold positiveNumberDetectionCRL
  have hne : ∃ D : ℝ, 0 ≤ D ∧
      PositiveNumberDetectionGuarantee d n p Ω σ mMin D (Nat.zero_lt_of_lt hn) :=
    exists_positiveNumberDetectionGuarantee p hΩ (Nat.zero_lt_of_lt hn) hn
  have hatt := sInf_nonnegative_predicate_attained hne
    (fun hDE hD => positiveNumberDetectionGuarantee_mono hDE hD) hfailure
  refine ⟨hatt.1, hatt.2, ?_⟩
  intro D hD hguarantee
  exact csInf_le ⟨0, fun E hE => hE.1⟩ ⟨hD, hguarantee⟩

/-- The general number-detection CRL attains the manuscript's smallest
nonnegative feasible separation, for every finite `p ≥ 1` and `p = ∞`. -/
theorem numberDetectionCRL_isSmallest
    {d n : ℕ} (p : LpIndex) {Ω σ mMin : ℝ}
    (hn : 2 ≤ n) (hΩ : 0 < Ω) (hσ : 0 < σ) :
    0 ≤ numberDetectionCRL d n p Ω σ mMin (Nat.zero_lt_of_lt hn) ∧
      NumberDetectionGuarantee d n p Ω σ mMin
        (numberDetectionCRL d n p Ω σ mMin (Nat.zero_lt_of_lt hn))
        (Nat.zero_lt_of_lt hn) ∧
      ∀ D : ℝ, 0 ≤ D →
        NumberDetectionGuarantee d n p Ω σ mMin D (Nat.zero_lt_of_lt hn) →
        numberDetectionCRL d n p Ω σ mMin (Nat.zero_lt_of_lt hn) ≤ D := by
  apply numberDetectionCRL_isSmallest_of_failure_extension p hn hΩ
  intro D hfail
  exact exists_larger_not_numberDetectionGuarantee hn hΩ hσ p hfail

/-- The positive-amplitude number-detection CRL also attains the smallest
nonnegative feasible separation for every allowed norm index. -/
theorem positiveNumberDetectionCRL_isSmallest
    {d n : ℕ} (p : LpIndex) {Ω σ mMin : ℝ}
    (hn : 2 ≤ n) (hΩ : 0 < Ω) (hσ : 0 < σ) :
    0 ≤ positiveNumberDetectionCRL d n p Ω σ mMin (Nat.zero_lt_of_lt hn) ∧
      PositiveNumberDetectionGuarantee d n p Ω σ mMin
        (positiveNumberDetectionCRL d n p Ω σ mMin (Nat.zero_lt_of_lt hn))
        (Nat.zero_lt_of_lt hn) ∧
      ∀ D : ℝ, 0 ≤ D →
        PositiveNumberDetectionGuarantee d n p Ω σ mMin D
          (Nat.zero_lt_of_lt hn) →
        positiveNumberDetectionCRL d n p Ω σ mMin (Nat.zero_lt_of_lt hn) ≤ D := by
  apply positiveNumberDetectionCRL_isSmallest_of_failure_extension p hn hΩ
  intro D hfail
  exact exists_larger_not_positiveNumberDetectionGuarantee hn hΩ hσ p hfail

/-- Manuscript equation `eq:crl-number-upper`: the number-detection CRL for
`p = 1` is bounded by the explicit separation threshold. -/
theorem numberDetectionCRL_le_numberDetectionSeparationThreshold
    {d n : ℕ} {Ω σ mMin : ℝ}
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin) :
    numberDetectionCRL d n (.finite 1 le_rfl) Ω σ mMin
        (Nat.zero_lt_of_lt hn) ≤
      numberDetectionSeparationThreshold d n Ω σ mMin := by
  unfold numberDetectionCRL
  apply sInf_nonnegative_predicate_le
    (numberDetectionSeparationThreshold_nonneg hn hΩ hσ hnoise)
  intro D hD
  exact numberDetectionGuarantee_of_threshold_lt
    hd hn hΩ hσ hnoise hD

/-- Positive-amplitude counterpart of manuscript equation `eq:crl-number-upper`. -/
theorem positiveNumberDetectionCRL_le_numberDetectionSeparationThreshold
    {d n : ℕ} {Ω σ mMin : ℝ}
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin) :
    positiveNumberDetectionCRL d n (.finite 1 le_rfl) Ω σ mMin
        (Nat.zero_lt_of_lt hn) ≤
      numberDetectionSeparationThreshold d n Ω σ mMin := by
  unfold positiveNumberDetectionCRL
  apply sInf_nonnegative_predicate_le
    (numberDetectionSeparationThreshold_nonneg hn hΩ hσ hnoise)
  intro D hD
  have hgeneral := numberDetectionGuarantee_of_threshold_lt
    hd hn hΩ hσ hnoise hD
  intro μ _hpositive hmMin hcluster hseparation Y hmeasurement k ν hadmissible
  exact hgeneral μ hmMin hcluster hseparation Y hmeasurement k ν hadmissible.2

/-- The finite-difference construction gives the constant-`2` lower bound in
manuscript equation `eq:crl-number-twosided`. -/
theorem numberDetectionCRLLowerBound_le_numberDetectionCRL
    {d n : ℕ} {Ω σ mMin : ℝ}
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin) :
    numberDetectionCRLLowerBound n Ω σ mMin ≤
      numberDetectionCRL d n (.finite 1 le_rfl) Ω σ mMin
        (Nat.zero_lt_of_lt hn) := by
  unfold numberDetectionCRL
  apply le_csInf
  · let T := numberDetectionSeparationThreshold d n Ω σ mMin
    have hT : 0 ≤ T :=
      numberDetectionSeparationThreshold_nonneg hn hΩ hσ hnoise
    refine ⟨T + 1, ?_, ?_⟩
    · linarith
    · exact numberDetectionGuarantee_of_threshold_lt
        hd hn hΩ hσ hnoise (by linarith)
  · intro D hD
    exact le_of_not_gt fun hlt =>
      not_numberDetectionGuarantee_of_lt_lowerBound
        hd hn hΩ hσ hnoise hlt hD.2

/-- Positive-amplitude counterpart of the constant-`2` CRL lower bound. -/
theorem numberDetectionCRLLowerBound_le_positiveNumberDetectionCRL
    {d n : ℕ} {Ω σ mMin : ℝ}
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin) :
    numberDetectionCRLLowerBound n Ω σ mMin ≤
      positiveNumberDetectionCRL d n (.finite 1 le_rfl) Ω σ mMin
        (Nat.zero_lt_of_lt hn) := by
  unfold positiveNumberDetectionCRL
  apply le_csInf
  · let T := numberDetectionSeparationThreshold d n Ω σ mMin
    have hT : 0 ≤ T :=
      numberDetectionSeparationThreshold_nonneg hn hΩ hσ hnoise
    refine ⟨T + 1, ?_, ?_⟩
    · linarith
    · have hgeneral := numberDetectionGuarantee_of_threshold_lt
        hd hn hΩ hσ hnoise (by linarith : T < T + 1)
      intro μ _hpositive hmMin hcluster hseparation Y hmeasurement k ν hadmissible
      exact hgeneral μ hmMin hcluster hseparation Y hmeasurement k ν hadmissible.2
  · intro D hD
    exact le_of_not_gt fun hlt =>
      not_positiveNumberDetectionGuarantee_of_lt_lowerBound
        hd hn hΩ hσ hnoise hlt hD.2

/-- Two-sided number-detection CRL estimate from the manuscript. -/
theorem numberDetectionCRL_two_sided
    {d n : ℕ} {Ω σ mMin : ℝ}
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin) :
    numberDetectionCRLLowerBound n Ω σ mMin ≤
        numberDetectionCRL d n (.finite 1 le_rfl) Ω σ mMin
          (Nat.zero_lt_of_lt hn) ∧
      numberDetectionCRL d n (.finite 1 le_rfl) Ω σ mMin
          (Nat.zero_lt_of_lt hn) ≤
        numberDetectionSeparationThreshold d n Ω σ mMin :=
  ⟨numberDetectionCRLLowerBound_le_numberDetectionCRL
      hd hn hΩ hσ hnoise,
    numberDetectionCRL_le_numberDetectionSeparationThreshold
      hd hn hΩ hσ hnoise⟩

/-- Two-sided positive-amplitude number-detection CRL estimate. -/
theorem positiveNumberDetectionCRL_two_sided
    {d n : ℕ} {Ω σ mMin : ℝ}
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin) :
    numberDetectionCRLLowerBound n Ω σ mMin ≤
        positiveNumberDetectionCRL d n (.finite 1 le_rfl) Ω σ mMin
          (Nat.zero_lt_of_lt hn) ∧
      positiveNumberDetectionCRL d n (.finite 1 le_rfl) Ω σ mMin
          (Nat.zero_lt_of_lt hn) ≤
        numberDetectionSeparationThreshold d n Ω σ mMin :=
  ⟨numberDetectionCRLLowerBound_le_positiveNumberDetectionCRL
      hd hn hΩ hσ hnoise,
    positiveNumberDetectionCRL_le_numberDetectionSeparationThreshold
      hd hn hΩ hσ hnoise⟩

end

end NumDetect
end LeanNumDetect
