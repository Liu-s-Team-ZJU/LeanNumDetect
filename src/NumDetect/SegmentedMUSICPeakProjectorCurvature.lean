import NumDetect.MUSICPeakFourierProjectorCurvature
import NumDetect.MUSICPeakSegmentedFrequency
import NumDetect.SegmentedMUSICPeakSignalGap

set_option autoImplicit false
open WithLp
namespace LeanNumDetect
namespace NumDetect
noncomputable section

/-- The segmented signal-gap bound controls the noisy squared MUSIC curvature. -/
theorem segmentedMUSIC_lineCurvature_lower_of_matrixPerturb
    {d n m r D : ℕ} (μ : AtomicMeasure d n)
    (E : Matrix (SegmentedIndex d m r) (SegmentedIndex d m r) ℂ)
    (B : ℝ) (hd : 0 < d) (hn : 0 < n) (hm : n ≤ m)
    (hBpos : 0 < B)
    (hB : B ≤ matrixSingularValue
      (segmentedVandermonde m r D μ.node) (n - 1))
    (hsmall : 2 * matrixSpectralNorm E < minAmplitude μ hn * B ^ 2)
    (z w : EuclideanSpace ℝ (Fin d)) :
    lineCurvature
        (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
          (segmentedNoiselessMatrix m r D μ) n) z w -
      4 * (Real.sqrt d * (segmentedCutoff m r D : ℝ)) ^ 2 *
        (2 * matrixSpectralNorm E / (minAmplitude μ hn * B ^ 2)) * ‖w‖ ^ 2 ≤
    lineCurvature
      (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
        (segmentedNoiselessMatrix m r D μ + E) n) z w := by
  have hrows : n < Fintype.card (SegmentedIndex d m r) :=
    sourceCount_lt_card_segmentedIndex hd hm
  have hgap := segmentedMUSIC_noiseless_rank_and_gap_of_vandermonde_bound
    μ B hn hBpos hB
  have hG : 0 < minAmplitude μ hn * B ^ 2 :=
    mul_pos (minAmplitude_pos μ hn) (sq_pos_of_pos hBpos)
  have hΩ : 0 ≤ Real.sqrt d * (segmentedCutoff m r D : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  have hphase (i : SegmentedIndex d m r) :
      |dot (segmentedFrequency d m r D i) (ofLp w)| ≤
        (Real.sqrt d * (segmentedCutoff m r D : ℝ)) * ‖w‖ := by
    simpa using segmentedFrequency_phase_le i (ofLp w)
  exact finiteFourier_squaredMUSIC_lineCurvature_lower_of_matrixPerturb
    (segmentedFrequency d m r D) (segmentedNoiselessMatrix m r D μ)
    E n hn hrows hrows.le hgap.1 z w
    (minAmplitude μ hn * B ^ 2)
    (Real.sqrt d * (segmentedCutoff m r D : ℝ))
    hG hgap.2 hsmall hΩ hphase

end
end NumDetect
end LeanNumDetect
