import NumDetect.MUSIC.Perturbation

/-! MUSIC noise-space correlation stability for generalized Hankel matrices. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open WithLp

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- The manuscript's MUSIC identifiability condition: normalized steering
vectors lie in the exact signal space precisely at source locations. -/
def IsMUSICIdentifiable
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rowFrequency : ι → Point d) (A : Matrix ι κ ℂ)
    (node : Fin n → Point d) : Prop :=
  ∀ y, toLp 2 (normalizedSteering rowFrequency y) ∈ A.toEuclideanLin.range ↔
    ∃ j, y = node j

/-- For an exact rank-`n` matrix, the fixed-rank MUSIC correlation vanishes
exactly when the normalized steering vector belongs to the signal space. -/
theorem rankNoiseSpaceCorrelation_eq_zero_iff_mem_signalSpace
    {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rowFrequency : ι → Point d) (A : Matrix ι κ ℂ)
    (n : ℕ) (hrows : n < Fintype.card ι) (hrank : A.rank = n)
    (y : Point d) :
    rankNoiseSpaceCorrelation rowFrequency A n y = 0 ↔
      toLp 2 (normalizedSteering rowFrequency y) ∈ A.toEuclideanLin.range := by
  unfold rankNoiseSpaceCorrelation
  rw [norm_eq_zero, Submodule.starProjection_apply_eq_zero_iff]
  rw [trailingLeftSingularSubspace_eq_range_orthogonal A n hrows hrank]
  simp

/-- Under the manuscript's identifiability condition, the zero set of the
noise-space correlation is exactly the set of source locations.  Equivalently,
the reciprocal MUSIC imaging function has poles exactly at those locations. -/
theorem noiselessMUSIC_correlation_eq_zero_iff_source
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rowFrequency : ι → Point d) (A : Matrix ι κ ℂ)
    (node : Fin n → Point d)
    (hrows : n < Fintype.card ι) (hrank : A.rank = n)
    (hidentifiable : IsMUSICIdentifiable rowFrequency A node)
    (y : Point d) :
    rankNoiseSpaceCorrelation rowFrequency A n y = 0 ↔ ∃ j, y = node j := by
  exact (rankNoiseSpaceCorrelation_eq_zero_iff_mem_signalSpace
    rowFrequency A n hrows hrank y).trans (hidentifiable y)

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

end

end NumDetect
end LeanNumDetect
