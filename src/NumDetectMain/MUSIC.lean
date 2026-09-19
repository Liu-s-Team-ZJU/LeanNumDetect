import NumDetectMain.MUSICProofSupport

/-! MUSIC noise-space correlation stability for generalized Hankel matrices. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Denominator in the GHM MUSIC perturbation bound. -/
def musicSignalGap {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq (Fin n)]
    (rowFrequency : ι → Point d) (columnFrequency : κ → Point d)
    (μ : AtomicMeasure d n) (hn : 0 < n) : ℝ :=
  minAmplitude μ hn *
    matrixSingularValue
      (generalizedVandermonde rowFrequency μ.node) (n - 1) *
    matrixSingularValue
      (generalizedVandermonde columnFrequency μ.node) (n - 1)

/-- Manuscript Lemma `lem:stability_ghm_music`. -/
theorem ghmMUSIC_correlation_stability
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rowFrequency : ι → Point d)
    (columnFrequency : κ → Point d)
    (μ : AtomicMeasure d n)
    (a : Fin n → ℂ)
    (Δ : Matrix ι κ ℂ)
    (hn : 0 < n) (hM₁ : n < Fintype.card ι)
    (hM₂ : n ≤ Fintype.card κ)
    (ha : ∀ j, minAmplitude μ hn ≤ ‖a j‖)
    (hfull₁ : HasFullColumnRank
      (generalizedVandermonde rowFrequency μ.node))
    (hfull₂ : HasFullColumnRank
      (generalizedVandermonde columnFrequency μ.node))
    (hsmall :
      2 * matrixSpectralNorm Δ <
        musicSignalGap rowFrequency columnFrequency μ hn) :
    correlationUniformDistance
        (rankNoiseSpaceCorrelation rowFrequency
          (generalizedVandermonde rowFrequency μ.node *
            Matrix.diagonal a *
            Matrix.transpose (generalizedVandermonde columnFrequency μ.node) + Δ) n)
        (rankNoiseSpaceCorrelation rowFrequency
          (generalizedVandermonde rowFrequency μ.node *
            Matrix.diagonal a *
            Matrix.transpose (generalizedVandermonde columnFrequency μ.node)) n) ≤
      2 * matrixSpectralNorm Δ /
        musicSignalGap rowFrequency columnFrequency μ hn := by
  let A₀ :=
    generalizedVandermonde rowFrequency μ.node *
      Matrix.diagonal a *
      Matrix.transpose (generalizedVandermonde columnFrequency μ.node)
  have hgapPos : 0 < musicSignalGap rowFrequency columnFrequency μ hn := by
    unfold musicSignalGap
    exact mul_pos
      (mul_pos (minAmplitude_pos μ hn)
        (lastSingularValue_pos_of_fullColumnRank _ hn hfull₁))
      (lastSingularValue_pos_of_fullColumnRank _ hn hfull₂)
  have hgap :
      musicSignalGap rowFrequency columnFrequency μ hn ≤
        matrixSingularValue A₀ (n - 1) := by
    exact vandermondeFactor_signalSingularValue_lower
      rowFrequency columnFrequency μ.node a (minAmplitude μ hn) hn
      (minAmplitude_pos μ hn) ha hfull₂
  have hrank : A₀.rank = n := by
    exact vandermondeFactor_rank
      rowFrequency columnFrequency μ.node a (minAmplitude μ hn) hn
      (minAmplitude_pos μ hn) ha hfull₁ hfull₂
  have hwedin :=
    correlationUniformDistance_le_of_fixedRank
      rowFrequency A₀ Δ hn hM₁ hM₂ hrank (hsmall.trans_le hgap)
  exact hwedin.trans
    (div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) (norm_nonneg _)) hgapPos hgap)

/-- The explicit quantity `B_cl` in `eq:segmented-music-Bcl`. -/
def segmentedMUSICClumpBound
    (d n nStar m r D : ℕ) (β Δ₁ : ℝ) : ℝ :=
  segmentedVandermondeLowerBound d n nStar m r D β Δ₁

/-- Manuscript Corollary `cor:stability_multidim_segmented`. -/
theorem segmentedMUSIC_correlation_stability
    {d n A nStar m r D : ℕ} {τ η β mMin : ℝ}
    (μ : AtomicMeasure d n)
    (Δ : Matrix (SegmentedIndex d m r) (SegmentedIndex d m r) ℂ)
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hm : 1 ≤ m) (hmn : n ≤ m) (hD : m < D)
    (hτ : τ ≤ Real.pi / (2 * D * d))
    (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β * d / (localizationOrder m nStar + 1) ≤ η)
    (hframe :
      HasFineCubeFrame d (localizationOrder m nStar) η
        (2 - Real.exp (1 / (2 * β))))
    (hr : 2 * nStar ≤ r)
    (hlocal :
      periodicMinimumL1Separation μ.node hn ≤
        Real.pi * nStar / ((r * D : ℕ) : ℝ))
    (hmMin : minAmplitude μ (Nat.zero_lt_of_lt hn) = mMin) :
    let Bcl := segmentedMUSICClumpBound d n nStar m r D β
      (periodicMinimumL1Separation μ.node hn)
    matrixSingularValue (segmentedVandermonde m r D μ.node) (n - 1) =
        matrixSingularValue
          (segmentedColumnVandermonde m r D μ.node) (n - 1) ∧
    Bcl ≤ matrixSingularValue (segmentedVandermonde m r D μ.node) (n - 1) ∧
    Bcl ≤ matrixSingularValue
      (segmentedColumnVandermonde m r D μ.node) (n - 1) ∧
    0 < Bcl ∧
    (2 * matrixSpectralNorm Δ < mMin * Bcl ^ 2 →
      correlationUniformDistance
          (rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ + Δ) n)
          (rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ) n) ≤
        2 * matrixSpectralNorm Δ / (mMin * Bcl ^ 2)) := by
  dsimp only
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hBpos :
      0 < segmentedMUSICClumpBound d n nStar m r D β
        (periodicMinimumL1Separation μ.node hn) := by
    exact segmentedVandermondeLowerBound_pos μ hn hclumps hm hD hβ hr
  have hBrow :
      segmentedMUSICClumpBound d n nStar m r D β
          (periodicMinimumL1Separation μ.node hn) ≤
        matrixSingularValue
          (segmentedVandermonde m r D μ.node) (n - 1) := by
    exact segmentedVandermonde_minimumSingularValue_of_fineCubeFrame
      μ hd hn hclumps hm hD hτ hβ hη hframe hr hlocal
  have heq :
      matrixSingularValue (segmentedVandermonde m r D μ.node) (n - 1) =
        matrixSingularValue
          (segmentedColumnVandermonde m r D μ.node) (n - 1) := rfl
  have hBcol :
      segmentedMUSICClumpBound d n nStar m r D β
          (periodicMinimumL1Separation μ.node hn) ≤
        matrixSingularValue
          (segmentedColumnVandermonde m r D μ.node) (n - 1) := by
    rwa [← heq]
  refine ⟨heq, hBrow, hBcol, hBpos, ?_⟩
  intro hsmall
  have hmMinPos : 0 < mMin := by
    rw [← hmMin]
    exact minAmplitude_pos μ hn0
  have hsvNonneg :
      0 ≤ matrixSingularValue
        (segmentedVandermonde m r D μ.node) (n - 1) :=
    matrixSingularValue_nonneg _ _
  have hdenom :
      mMin *
          (segmentedMUSICClumpBound d n nStar m r D β
            (periodicMinimumL1Separation μ.node hn)) ^ 2 ≤
        musicSignalGap
          (segmentedFrequency d m r D)
          (segmentedFrequency d m r D) μ hn0 := by
    rw [musicSignalGap, hmMin]
    change mMin * _ ^ 2 ≤
      mMin *
        matrixSingularValue
          (segmentedVandermonde m r D μ.node) (n - 1) *
        matrixSingularValue
          (segmentedVandermonde m r D μ.node) (n - 1)
    calc
      mMin * _ ^ 2 ≤
          mMin *
            matrixSingularValue
              (segmentedVandermonde m r D μ.node) (n - 1) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hBpos.le hBrow 2) hmMinPos.le
      _ = _ := by ring
  have hcard :
      n < Fintype.card (SegmentedIndex d m r) :=
    sourceCount_lt_card_segmentedIndex hd hmn
  have hgeneral := ghmMUSIC_correlation_stability
    (segmentedFrequency d m r D) (segmentedFrequency d m r D) μ
    (segmentedPhaseAmplitude m r D μ) Δ hn0 hcard hcard.le
    (fun j => minAmplitude_le_norm_segmentedPhaseAmplitude m r D μ hn0 j)
    (fullColumnRank_of_lastSingularValue_pos _ hn0 (hBpos.trans_le hBrow))
    (fullColumnRank_of_lastSingularValue_pos _ hn0 (hBpos.trans_le hBcol))
    (hsmall.trans_le hdenom)
  have hfrac :
      2 * matrixSpectralNorm Δ /
          musicSignalGap
            (segmentedFrequency d m r D)
            (segmentedFrequency d m r D) μ hn0 ≤
        2 * matrixSpectralNorm Δ /
          (mMin *
            segmentedMUSICClumpBound d n nStar m r D β
              (periodicMinimumL1Separation μ.node hn) ^ 2) :=
    div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) (norm_nonneg _))
      (mul_pos hmMinPos (sq_pos_of_pos hBpos)) hdenom
  simpa only [segmentedNoiselessMatrix, segmentedVandermonde,
    segmentedColumnVandermonde] using hgeneral.trans hfrac

end

end NumDetect
end LeanNumDetect
