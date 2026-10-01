import NumDetect.SegmentedMUSICPeaks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- The noiseless segmented GHM has exactly the source rank, and its last
signal singular value dominates the explicit Vandermonde lower bound. -/
theorem segmentedMUSIC_noiseless_rank_and_gap_of_vandermonde_bound
    {d n m r D : ℕ} (μ : AtomicMeasure d n)
    (B : ℝ) (hn : 0 < n) (hBpos : 0 < B)
    (hB : B ≤ matrixSingularValue
      (segmentedVandermonde m r D μ.node) (n - 1)) :
    (segmentedNoiselessMatrix m r D μ).rank = n ∧
      minAmplitude μ hn * B ^ 2 ≤
        matrixSingularValue (segmentedNoiselessMatrix m r D μ) (n - 1) := by
  let V := segmentedVandermonde m r D μ.node
  let S := matrixSingularValue V (n - 1)
  have hfull : HasFullColumnRank V :=
    fullColumnRank_of_lastSingularValue_pos V hn (hBpos.trans_le hB)
  have hmpos : 0 < minAmplitude μ hn := minAmplitude_pos μ hn
  have ha : ∀ j, minAmplitude μ hn ≤
      ‖segmentedPhaseAmplitude m r D μ j‖ :=
    minAmplitude_le_norm_segmentedPhaseAmplitude m r D μ hn
  have hrank := vandermondeFactor_rank
    (segmentedFrequency d m r D) (segmentedFrequency d m r D)
    μ.node (segmentedPhaseAmplitude m r D μ)
    (minAmplitude μ hn) hn hmpos ha hfull hfull
  have hsignal := vandermondeFactor_signalSingularValue_lower
    (segmentedFrequency d m r D) (segmentedFrequency d m r D)
    μ.node (segmentedPhaseAmplitude m r D μ)
    (minAmplitude μ hn) hn hmpos ha hfull
  constructor
  · simpa only [segmentedNoiselessMatrix, segmentedVandermonde,
      segmentedColumnVandermonde] using hrank
  · have hfirst : minAmplitude μ hn * B ^ 2 ≤
        minAmplitude μ hn * S ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hBpos.le hB 2) hmpos.le
    calc
      minAmplitude μ hn * B ^ 2 ≤ minAmplitude μ hn * S ^ 2 := hfirst
      _ = minAmplitude μ hn * S * S := by ring
      _ ≤ matrixSingularValue (segmentedNoiselessMatrix m r D μ) (n - 1) := by
        simpa only [S, V, segmentedNoiselessMatrix, segmentedVandermonde,
          segmentedColumnVandermonde] using hsignal

end
end NumDetect
end LeanNumDetect
