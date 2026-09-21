import NumDetect.UniformThreshold

/-! Contiguous-grid source-number detection results from the NumDetect manuscript. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Manuscript Theorem `liuthm5.1v2`. Singular-value indices are zero-based:
paper index `j` is represented by Lean index `j - 1`. -/
theorem uniformGHM_singularValueThreshold
    {d n s : ℕ} {Ω σ mMin : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ)
    (hmMin : minAmplitude μ (Nat.zero_lt_of_lt hn) = mMin)
    (hcluster : ∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ.node j))
    (hs : 4 * n ≤ s) (hseven : Even s)
    (hnoise : σ < mMin)
    (hmeasurement : IsBandMeasurement μ Ω σ Y) :
    (∀ j, n ≤ j → j < (s + 1) ^ d →
      matrixSingularValue (uniformMeasurementMatrix s Ω Y) j ≤
        ((s + 1 : ℕ) : ℝ) ^ d * σ) ∧
    (uniformDetectionSeparationThreshold (d := d) (n := n) s Ω σ mMin <
        minimumL1Separation μ.node hn →
      ((s + 1 : ℕ) : ℝ) ^ d * σ <
        matrixSingularValue (uniformMeasurementMatrix s Ω Y) (n - 1)) := by
  exact uniformGHM_singularValueThreshold_support
    μ Y hd hn hΩ hσ hmMin hcluster hs hseven hnoise hmeasurement

/-- Manuscript Theorem `thm:li-resolution`. -/
theorem noAdmissibleMeasureWithFewerSupports
    {d n : ℕ} {Ω σ mMin : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ)
    (hmMin : minAmplitude μ (Nat.zero_lt_of_lt hn) = mMin)
    (hcluster : ∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ.node j))
    (hnoise : σ < mMin)
    (hseparation :
      numberDetectionSeparationThreshold d n Ω σ mMin <
        minimumL1Separation μ.node hn)
    (hmeasurement : IsBandMeasurement μ Ω σ Y) :
    ¬ ∃ (k : ℕ) (ν : AtomicMeasure d k),
      k < n ∧ IsAdmissible ν Ω σ Y := by
  exact noAdmissibleMeasureWithFewerSupports_support
    μ Y hd hn hΩ hσ hmMin hcluster hnoise hseparation hmeasurement

end

end NumDetect
end LeanNumDetect
