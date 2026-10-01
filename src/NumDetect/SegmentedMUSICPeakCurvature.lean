import NumDetect.MUSICPeakStrictConvex
import NumDetect.SegmentedMUSICPeaks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WithLp Filter
open scoped Topology
namespace LeanNumDetect
namespace NumDetect
noncomputable section

/-- Explicit curvature inequalities imply the local strict-convexity input to the segmented top-peak theorem. -/
theorem segmentedMUSIC_strictConvexOn_sourceBalls_of_curvatureBounds
    {d n m r D : ℕ} (μ : AtomicMeasure d n)
    (E : Matrix (SegmentedIndex d m r) (SegmentedIndex d m r) ℂ)
    (K : Set (Point d)) (Δ w ρ Ω ε : ℝ)
    (hd : 0 < d) (hn : 0 < n) (hm : n ≤ m) (hmD : m < D)
    (hΔ : 0 < Δ) (hw : w < 2 * Real.pi) (hρ : 0 < ρ)
    (hnodeK : ∀ j, μ.node j ∈ K)
    (hwidth : ∀ u ∈ K, ∀ v ∈ K, ∀ k, |u k - v k| ≤ w)
    (hsep : ∀ i j, i ≠ j →
      Δ ≤ pointEuclideanDistance (μ.node i) (μ.node j))
    (hballK : ∀ i,
      Metric.closedBall (toLp 2 (μ.node i)) ρ ⊆ (toLp 2) '' K)
    (hradiusVariation : ∀ i,
      ∀ z ∈ Metric.closedBall (toLp 2 (μ.node i)) ρ,
      ∀ v : EuclideanSpace ℝ (Fin d),
        lineCurvature
            (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
              (segmentedNoiselessMatrix m r D μ) n)
            (toLp 2 (μ.node i)) v -
          8 * Ω ^ 3 * ρ * ‖v‖ ^ 2 ≤
        lineCurvature
          (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ) n) z v)
    (hprojectorVariation : ∀ i,
      ∀ z ∈ Metric.closedBall (toLp 2 (μ.node i)) ρ,
      ∀ v : EuclideanSpace ℝ (Fin d),
        lineCurvature
            (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
              (segmentedNoiselessMatrix m r D μ) n) z v -
          4 * Ω ^ 2 * ε * ‖v‖ ^ 2 ≤
        lineCurvature
          (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ + E) n) z v)
    (hradius : 8 * Ω ^ 3 * ρ ≤
      segmentedMUSICGrowthConstant d n m r Δ w ^ 2)
    (hnoise : 4 * Ω ^ 2 * ε <
      segmentedMUSICGrowthConstant d n m r Δ w ^ 2 / 2) :
    ∀ i,
      StrictConvexOn ℝ
        ((toLp 2) '' K ∩ Metric.closedBall (toLp 2 (μ.node i)) ρ)
        (fun z : EuclideanSpace ℝ (Fin d) =>
          rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ + E) n (ofLp z) ^ 2) := by
  obtain ⟨hfull, _, hgrowth⟩ :=
    segmentedMUSIC_growth μ K Δ w hd hn hm hmD hΔ hw hnodeK hwidth hsep
  have hfull₂ : HasFullColumnRank
      (generalizedVandermonde (segmentedFrequency d m r D) μ.node) := by
    simpa only [segmentedVandermonde] using hfull
  have hcard : n < Fintype.card (SegmentedIndex d m r) :=
    sourceCount_lt_card_segmentedIndex hd hm
  let nodeE : Fin n → EuclideanSpace ℝ (Fin d) := fun j => toLp 2 (μ.node j)
  let KE : Set (EuclideanSpace ℝ (Fin d)) := (toLp 2) '' K
  let R : EuclideanSpace ℝ (Fin d) → ℝ := fun z =>
    rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
      (segmentedNoiselessMatrix m r D μ) n (ofLp z)
  have hsepE : ∀ i k, i ≠ k → Δ ≤ dist (nodeE i) (nodeE k) := hsep
  have hgrowthE : ∀ z ∈ KE,
      segmentedMUSICGrowthConstant d n m r Δ w *
        min (Δ / 4) (finiteSourceDistance hn nodeE z) ≤ R z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    simpa [nodeE, KE, R, finiteSourceDistance,
      finiteEuclideanSourceDistance, pointEuclideanDistance] using hgrowth y hy
  intro i
  have hzero : R (nodeE i) = 0 := by
    exact ghm_source_correlation_eq_zero
      (segmentedFrequency d m r D) (segmentedFrequency d m r D)
      μ (segmentedPhaseAmplitude m r D μ)
      hn hcard
      (fun k => minAmplitude_le_norm_segmentedPhaseAmplitude m r D μ hn k)
      hfull₂ hfull₂ i
  have hKn : KE ∈ 𝓝 (nodeE i) := by
    apply mem_of_superset (Metric.ball_mem_nhds (nodeE i) hρ)
    intro z hz
    exact hballK i (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hz)))
  have hstrict : StrictConvexOn ℝ
      (Metric.closedBall (nodeE i) ρ)
      (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
        (segmentedNoiselessMatrix m r D μ + E) n) := by
    exact finiteFourierMUSIC_strictConvexOn_sourceBall_of_bounds
      (segmentedFrequency d m r D)
      (segmentedNoiselessMatrix m r D μ)
      (segmentedNoiselessMatrix m r D μ + E)
      nodeE KE hn Δ (segmentedMUSICGrowthConstant d n m r Δ w)
      ρ Ω ε hΔ (segmentedMUSICGrowthConstant_pos hd hn hΔ hw).le
      hsepE i hKn hzero hgrowthE
      (hradiusVariation i) (hprojectorVariation i) hradius hnoise
  have hEq : KE ∩ Metric.closedBall (nodeE i) ρ =
      Metric.closedBall (nodeE i) ρ :=
    Set.inter_eq_right.mpr (hballK i)
  change StrictConvexOn ℝ (KE ∩ Metric.closedBall (nodeE i) ρ)
    (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
      (segmentedNoiselessMatrix m r D μ + E) n)
  rw [hEq]
  exact hstrict


/-- The segmented top-peak theorem with local strict convexity discharged by curvature bounds. -/
theorem exists_segmentedMUSIC_highestPeaks_of_curvatureBounds
    {d n m r D : ℕ} (μ : AtomicMeasure d n)
    (E : Matrix (SegmentedIndex d m r) (SegmentedIndex d m r) ℂ)
    (K : Set (Point d)) (Δ w ρ B Ω ε : ℝ)
    (hd : 0 < d) (hn : 0 < n) (hm : n ≤ m) (hmD : m < D)
    (hΔ : 0 < Δ) (hw : w < 2 * Real.pi)
    (hρ : 0 < ρ) (hfour : 4 * ρ ≤ Δ)
    (hK : IsCompact K) (hnodeK : ∀ j, μ.node j ∈ K)
    (hwidth : ∀ u ∈ K, ∀ v ∈ K, ∀ k, |u k - v k| ≤ w)
    (hsep : ∀ i j, i ≠ j →
      Δ ≤ pointEuclideanDistance (μ.node i) (μ.node j))
    (hballK : ∀ i,
      Metric.closedBall (toLp 2 (μ.node i)) ρ ⊆ (toLp 2) '' K)
    (hBpos : 0 < B)
    (hB : B ≤ matrixSingularValue
      (segmentedVandermonde m r D μ.node) (n - 1))
    (hsmallMatrix : 2 * matrixSpectralNorm E < minAmplitude μ hn * B ^ 2)
    (hsmallPeak : 2 * matrixSpectralNorm E /
        (minAmplitude μ hn * B ^ 2) <
      segmentedMUSICGrowthConstant d n m r Δ w * ρ / 2)
    (hradiusVariation : ∀ i,
      ∀ z ∈ Metric.closedBall (toLp 2 (μ.node i)) ρ,
      ∀ v : EuclideanSpace ℝ (Fin d),
        lineCurvature
            (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
              (segmentedNoiselessMatrix m r D μ) n)
            (toLp 2 (μ.node i)) v -
          8 * Ω ^ 3 * ρ * ‖v‖ ^ 2 ≤
        lineCurvature
          (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ) n) z v)
    (hprojectorVariation : ∀ i,
      ∀ z ∈ Metric.closedBall (toLp 2 (μ.node i)) ρ,
      ∀ v : EuclideanSpace ℝ (Fin d),
        lineCurvature
            (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
              (segmentedNoiselessMatrix m r D μ) n) z v -
          4 * Ω ^ 2 * ε * ‖v‖ ^ 2 ≤
        lineCurvature
          (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ + E) n) z v)
    (hradius : 8 * Ω ^ 3 * ρ ≤
      segmentedMUSICGrowthConstant d n m r Δ w ^ 2)
    (hnoise : 4 * Ω ^ 2 * ε <
      segmentedMUSICGrowthConstant d n m r Δ w ^ 2 / 2) :
    ∃ estimate : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, estimate i ∈ (toLp 2) '' K ∧
        IsLocalMinOn
          (fun z : EuclideanSpace ℝ (Fin d) =>
            rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
              (segmentedNoiselessMatrix m r D μ + E) n (ofLp z) ^ 2)
          ((toLp 2) '' K) (estimate i) ∧
        dist (estimate i) (toLp 2 (μ.node i)) ≤
          4 * matrixSpectralNorm E /
            (segmentedMUSICGrowthConstant d n m r Δ w *
              (minAmplitude μ hn * B ^ 2))) ∧
      Function.Injective estimate ∧
      (∀ y, y ∈ (toLp 2) '' K →
        IsLocalMinOn
          (fun z : EuclideanSpace ℝ (Fin d) =>
            rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
              (segmentedNoiselessMatrix m r D μ + E) n (ofLp z) ^ 2)
          ((toLp 2) '' K) y →
        y ∉ Set.range estimate →
          ∀ i,
            rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
              (segmentedNoiselessMatrix m r D μ + E) n (ofLp (estimate i)) ^ 2 <
            rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
              (segmentedNoiselessMatrix m r D μ + E) n (ofLp y) ^ 2) := by
  have hstrict := segmentedMUSIC_strictConvexOn_sourceBalls_of_curvatureBounds
    μ E K Δ w ρ Ω ε hd hn hm hmD hΔ hw hρ hnodeK hwidth hsep
    hballK hradiusVariation hprojectorVariation hradius hnoise
  exact exists_segmentedMUSIC_highestPeaks_of_lowerBound
    μ E K Δ w ρ B hd hn hm hmD hΔ hw hρ hfour hK hnodeK
    hwidth hsep hBpos hB hsmallMatrix hsmallPeak hstrict

end
end NumDetect
end LeanNumDetect
