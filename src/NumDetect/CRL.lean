import NumDetect.Uniform
import NumDetect.CRLLowerBound

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
