import NumDetect.MUSICPeakSelection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open WithLp

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- The segmented array's continuous peak-selection theorem, conditional only
on strict convexity of the noisy squared correlation on the source balls. -/
theorem exists_segmentedMUSIC_highestPeaks_of_lowerBound
    {d n m r D : ℕ} (μ : AtomicMeasure d n)
    (E : Matrix (SegmentedIndex d m r) (SegmentedIndex d m r) ℂ)
    (K : Set (Point d)) (Δ w ρ B : ℝ)
    (hd : 0 < d) (hn : 0 < n) (hm : n ≤ m) (hmD : m < D)
    (hΔ : 0 < Δ) (hw : w < 2 * Real.pi)
    (hρ : 0 < ρ) (hfour : 4 * ρ ≤ Δ)
    (hK : IsCompact K) (hnodeK : ∀ j, μ.node j ∈ K)
    (hwidth : ∀ u ∈ K, ∀ v ∈ K, ∀ k, |u k - v k| ≤ w)
    (hsep : ∀ i j, i ≠ j →
      Δ ≤ pointEuclideanDistance (μ.node i) (μ.node j))
    (hBpos : 0 < B)
    (hB : B ≤ matrixSingularValue
      (segmentedVandermonde m r D μ.node) (n - 1))
    (hsmallMatrix : 2 * matrixSpectralNorm E < minAmplitude μ hn * B ^ 2)
    (hsmallPeak : 2 * matrixSpectralNorm E /
        (minAmplitude μ hn * B ^ 2) <
      segmentedMUSICGrowthConstant d n m r Δ w * ρ / 2)
    (hstrict : ∀ i,
      StrictConvexOn ℝ
        ((toLp 2) '' K ∩ Metric.closedBall (toLp 2 (μ.node i)) ρ)
        (fun z : EuclideanSpace ℝ (Fin d) =>
          rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ + E) n (ofLp z) ^ 2)) :
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
  let c := segmentedMUSICGrowthConstant d n m r Δ w
  let G := minAmplitude μ hn * B ^ 2
  let S := matrixSingularValue (segmentedVandermonde m r D μ.node) (n - 1)
  let gap := musicSignalGap (segmentedFrequency d m r D)
    (segmentedFrequency d m r D) μ hn
  let nodeE : Fin n → EuclideanSpace ℝ (Fin d) := fun j => toLp 2 (μ.node j)
  let KE : Set (EuclideanSpace ℝ (Fin d)) := (toLp 2) '' K
  let R : EuclideanSpace ℝ (Fin d) → ℝ := fun z =>
    rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
      (segmentedNoiselessMatrix m r D μ) n (ofLp z)
  let Rσ : EuclideanSpace ℝ (Fin d) → ℝ := fun z =>
    rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
      (segmentedNoiselessMatrix m r D μ + E) n (ofLp z)
  have hc : 0 < c := segmentedMUSICGrowthConstant_pos hd hn hΔ hw
  have hG : 0 < G := by
    dsimp [G]
    exact mul_pos (minAmplitude_pos μ hn) (sq_pos_of_pos hBpos)
  have hGS : G ≤ gap := by
    dsimp [G, gap, musicSignalGap, S]
    change minAmplitude μ hn * B ^ 2 ≤
      minAmplitude μ hn * S * S
    calc
      minAmplitude μ hn * B ^ 2 ≤ minAmplitude μ hn * S ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hBpos.le hB 2) (minAmplitude_pos μ hn).le
      _ = minAmplitude μ hn * S * S := by ring
  have hsmallGap : 2 * matrixSpectralNorm E < gap :=
    hsmallMatrix.trans_le hGS
  have hratio : 2 * matrixSpectralNorm E / gap ≤
      2 * matrixSpectralNorm E / G :=
    div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) (norm_nonneg _)) hG hGS
  obtain ⟨hfull, _, hgrowth⟩ :=
    segmentedMUSIC_growth μ K Δ w hd hn hm hmD hΔ hw hnodeK hwidth hsep
  have hfull₂ : HasFullColumnRank
      (generalizedVandermonde (segmentedFrequency d m r D) μ.node) := by
    simpa only [segmentedVandermonde] using hfull
  have hcard : n < Fintype.card (SegmentedIndex d m r) :=
    sourceCount_lt_card_segmentedIndex hd hm
  have hKE : IsCompact KE := hK.image (PiLp.continuous_toLp 2 _)
  have hnodeKE : ∀ j, nodeE j ∈ KE := by
    intro j
    exact ⟨μ.node j, hnodeK j, rfl⟩
  have hsepE : ∀ i j, i ≠ j → Δ ≤ dist (nodeE i) (nodeE j) :=
    hsep
  have hcont : ContinuousOn Rσ KE := by
    exact ((rankNoiseSpaceCorrelation_continuous
      (segmentedFrequency d m r D) _ n).comp
      (PiLp.continuous_ofLp 2 _)).continuousOn
  have hzero : ∀ j, R (nodeE j) = 0 := by
    intro j
    exact ghm_source_correlation_eq_zero
      (segmentedFrequency d m r D) (segmentedFrequency d m r D)
      μ (segmentedPhaseAmplitude m r D μ)
      hn hcard
      (fun k => minAmplitude_le_norm_segmentedPhaseAmplitude m r D μ hn k)
      hfull₂ hfull₂ j
  have hpert : ∀ z ∈ KE, |Rσ z - R z| ≤ 2 * matrixSpectralNorm E / G := by
    intro z _
    have huniform := ghmMUSIC_correlation_stability
      (segmentedFrequency d m r D) (segmentedFrequency d m r D)
      μ (segmentedPhaseAmplitude m r D μ) E hn hcard hcard.le
      (fun k => minAmplitude_le_norm_segmentedPhaseAmplitude m r D μ hn k)
      hfull₂ hfull₂ hsmallGap
    have hpoint := correlationUniformDistance_pointwise_of_unitBounds
      _ _ (2 * matrixSpectralNorm E / gap)
      (rankNoiseSpaceCorrelation_unitBounds
        (segmentedFrequency d m r D)
        (segmentedNoiselessMatrix m r D μ + E) n)
      (rankNoiseSpaceCorrelation_unitBounds
        (segmentedFrequency d m r D)
        (segmentedNoiselessMatrix m r D μ) n)
      (by simpa only [segmentedNoiselessMatrix, segmentedVandermonde,
        segmentedColumnVandermonde] using huniform) (ofLp z)
    exact hpoint.trans hratio
  have hpos : ∀ z ∈ KE, 0 ≤ Rσ z := by
    intro z _
    exact norm_nonneg _
  have hgrowthE : ∀ z ∈ KE,
      c * min (Δ / 4) (finiteSourceDistance hn nodeE z) ≤ R z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    simpa [c, R, nodeE, finiteSourceDistance,
      finiteEuclideanSourceDistance, pointEuclideanDistance] using hgrowth y hy
  obtain ⟨estimate, hest, hinj, htop⟩ :=
    exists_top_MUSIC_peaks_of_globalGrowth_and_strictConvex
      hn nodeE KE R Rσ Δ ρ c (2 * matrixSpectralNorm E / G)
      hρ hfour hc hsmallPeak hKE hnodeKE hsepE hcont hstrict
      hzero hpert hpos hgrowthE
  refine ⟨estimate, ?_, hinj, ?_⟩
  · intro i
    refine ⟨(hest i).1, (hest i).2.1, ?_⟩
    calc
      dist (estimate i) (nodeE i) ≤
          2 * (2 * matrixSpectralNorm E / G) / c := (hest i).2.2
      _ = 4 * matrixSpectralNorm E / (c * G) := by
        field_simp [hc.ne', hG.ne']
        ring
  · exact htop

private theorem segmented_peak_constant_algebra
    (L P Q T Trec σ m B u v : ℝ)
    (hL : 0 < L) (hP : 0 < P) (hQ : 0 < Q) (hT : 0 < T)
    (hm : 0 < m) (hB : 0 < B)
    (hrec : T * Trec = 1) :
    4 * (L ^ u * σ) / ((Q * T / (L ^ v * P)) * (m * B ^ 2)) =
      4 * L ^ (u + v) * P / (m * B ^ 2 * Q) * Trec * σ := by
  have hLu : 0 < L ^ u := Real.rpow_pos_of_pos hL _
  have hLv : 0 < L ^ v := Real.rpow_pos_of_pos hL _
  rw [Real.rpow_add hL]
  field_simp
  calc
    σ = σ * (T * Trec) := by rw [hrec]; ring
    _ = σ * T * Trec := by ring

private theorem segmented_peak_reciprocal
    (n : ℕ) (Δ : ℝ) (hΔ : 0 < Δ) :
    (Δ / 2) ^ (n - 1) * (2 / Δ) ^ (n - 1) = 1 := by
  rw [← mul_pow]
  have hmul : (Δ / 2) * (2 / Δ) = 1 := by
    field_simp
  rw [hmul]
  simp

private theorem segmented_peak_constant_identity
    {d n m r : ℕ} {Δ w σ mMin B : ℝ}
    (hd : 0 < d) (hΔ : 0 < Δ) (hw : w < 2 * Real.pi)
    (hmMin : 0 < mMin) (hB : 0 < B) :
    4 * ((segmentedLength m r : ℝ) ^ d * σ) /
        (segmentedMUSICGrowthConstant d n m r Δ w * (mMin * B ^ 2)) =
      4 * (segmentedLength m r : ℝ) ^ (3 * (d : ℝ) / 2) *
          (Real.pi * Real.sqrt d) ^ n /
          (mMin * B ^ 2 * (1 - w / (2 * Real.pi)) ^ n) *
          (2 / Δ) ^ (n - 1) * σ := by
  have hL : 0 < (segmentedLength m r : ℝ) := by
    exact_mod_cast (show 0 < segmentedLength m r by simp [segmentedLength])
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hP : 0 < (Real.pi * Real.sqrt d) ^ n := by positivity
  have hQ : 0 < (1 - w / (2 * Real.pi)) ^ n := by
    have hw' : 0 < 1 - w / (2 * Real.pi) := by
      apply sub_pos.mpr
      exact (div_lt_one (by positivity)).mpr hw
    positivity
  have hT : 0 < (Δ / 2) ^ (n - 1) := by positivity
  have hrec := segmented_peak_reciprocal n Δ hΔ
  have hbase := segmented_peak_constant_algebra
    (segmentedLength m r : ℝ)
    ((Real.pi * Real.sqrt d) ^ n)
    ((1 - w / (2 * Real.pi)) ^ n)
    ((Δ / 2) ^ (n - 1))
    ((2 / Δ) ^ (n - 1))
    σ mMin B (d : ℝ) ((d : ℝ) / 2)
    hL hP hQ hT hmMin hB hrec
  rw [Real.rpow_natCast] at hbase
  have hexp : (d : ℝ) + (d : ℝ) / 2 = 3 * (d : ℝ) / 2 := by ring
  rw [hexp] at hbase
  simpa only [segmentedMUSICGrowthConstant] using hbase

/-- The segmented multi-clump bound and entrywise measurement noise give a
continuous top-`n` MUSIC peak theorem. Local strict convexity is the sole
remaining analytic hypothesis. -/
theorem exists_segmentedMUSIC_highestPeaks_explicit
    {d n A nStar m r D : ℕ} {τ η β Δ w ρ σ : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (K : Set (Point d))
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hm : n ≤ m) (hD : m < D)
    (hτ : τ ≤ Real.pi / (2 * D * d))
    (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β * d / (localizationOrder m nStar + 1) ≤ η)
    (hr : 2 * nStar ≤ r)
    (hlocal : periodicMinimumL1Separation μ.node (by omega) ≤
      Real.pi * nStar / ((r * D : ℕ) : ℝ))
    (hΔ : 0 < Δ) (hw : w < 2 * Real.pi)
    (hρ : 0 < ρ) (hfour : 4 * ρ ≤ Δ)
    (hK : IsCompact K) (hnodeK : ∀ j, μ.node j ∈ K)
    (hwidth : ∀ u ∈ K, ∀ v ∈ K, ∀ k, |u k - v k| ≤ w)
    (hsep : ∀ i j, i ≠ j →
      Δ ≤ pointEuclideanDistance (μ.node i) (μ.node j))
    (hmeasurement : IsSegmentedMeasurement μ m r D σ Y)
    (hnoise :
      2 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ /
          (minAmplitude μ (by omega) *
            (segmentedMUSICClumpBound d n nStar m r D β
              (periodicMinimumL1Separation μ.node (by omega))) ^ 2) <
        min 1 (segmentedMUSICGrowthConstant d n m r Δ w * ρ / 2))
    (hstrict : ∀ i,
      StrictConvexOn ℝ
        ((toLp 2) '' K ∩ Metric.closedBall (toLp 2 (μ.node i)) ρ)
        (fun z : EuclideanSpace ℝ (Fin d) =>
          rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
            (segmentedMeasurementMatrix m r D Y) n (ofLp z) ^ 2)) :
    ∃ estimate : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, estimate i ∈ (toLp 2) '' K ∧
        IsLocalMinOn
          (fun z : EuclideanSpace ℝ (Fin d) =>
            rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
              (segmentedMeasurementMatrix m r D Y) n (ofLp z) ^ 2)
          ((toLp 2) '' K) (estimate i) ∧
        dist (estimate i) (toLp 2 (μ.node i)) ≤
          4 * (segmentedLength m r : ℝ) ^ (3 * (d : ℝ) / 2) *
            (Real.pi * Real.sqrt d) ^ n *
            (2 / Δ) ^ (n - 1) * σ /
            (minAmplitude μ (by omega) *
              (segmentedMUSICClumpBound d n nStar m r D β
                (periodicMinimumL1Separation μ.node (by omega))) ^ 2 *
              (1 - w / (2 * Real.pi)) ^ n)) ∧
      Function.Injective estimate ∧
      (∀ y, y ∈ (toLp 2) '' K →
        IsLocalMinOn
          (fun z : EuclideanSpace ℝ (Fin d) =>
            rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
              (segmentedMeasurementMatrix m r D Y) n (ofLp z) ^ 2)
          ((toLp 2) '' K) y →
        y ∉ Set.range estimate →
          ∀ i,
            rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
              (segmentedMeasurementMatrix m r D Y) n (ofLp (estimate i)) ^ 2 <
            rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
              (segmentedMeasurementMatrix m r D Y) n (ofLp y) ^ 2) := by
  have hn0 : 0 < n := by omega
  let B := segmentedMUSICClumpBound d n nStar m r D β
    (periodicMinimumL1Separation μ.node hn)
  let E := segmentedMeasurementMatrix m r D Y - segmentedNoiselessMatrix m r D μ
  have hbounds := segmentedMUSIC_correlation_stability μ E hd hn hclumps
    (by omega : 1 ≤ m) hm hD hτ hβ hη hr hlocal rfl
  dsimp only at hbounds
  obtain ⟨_, hB, _, hBpos, _⟩ := hbounds
  have hEbound : matrixSpectralNorm E ≤
      (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ := by
    dsimp [E]
    rw [← segmentedMeasurementMatrix_fourier_eq_noiseless m r D μ]
    exact segmentedThreshold_perturbation_spectralNorm_le μ Y hmeasurement
  have hdenom : 0 < minAmplitude μ hn0 * B ^ 2 :=
    mul_pos (minAmplitude_pos μ hn0) (sq_pos_of_pos hBpos)
  have hratio : 2 * matrixSpectralNorm E / (minAmplitude μ hn0 * B ^ 2) ≤
      2 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ /
        (minAmplitude μ hn0 * B ^ 2) := by
    apply div_le_div_of_nonneg_right _ hdenom.le
    nlinarith [hEbound]
  have hsmallMatrix : 2 * matrixSpectralNorm E <
      minAmplitude μ hn0 * B ^ 2 := by
    apply (div_lt_one hdenom).mp
    exact lt_of_le_of_lt hratio (lt_min_iff.mp hnoise).1
  have hsmallPeak : 2 * matrixSpectralNorm E /
      (minAmplitude μ hn0 * B ^ 2) <
      segmentedMUSICGrowthConstant d n m r Δ w * ρ / 2 :=
    lt_of_le_of_lt hratio (lt_min_iff.mp hnoise).2
  have hobs : segmentedNoiselessMatrix m r D μ + E =
      segmentedMeasurementMatrix m r D Y := by
    dsimp [E]
    abel
  obtain ⟨estimate, hest, hinj, htop⟩ :=
    exists_segmentedMUSIC_highestPeaks_of_lowerBound μ E K Δ w ρ B
      (by omega) hn0 hm hD hΔ hw hρ hfour hK hnodeK hwidth hsep
      hBpos hB hsmallMatrix hsmallPeak (by simpa only [hobs] using hstrict)
  refine ⟨estimate, ?_, hinj, ?_⟩
  · intro i
    refine ⟨(hest i).1, ?_, ?_⟩
    · simpa only [hobs] using (hest i).2.1
    · have hc : 0 < segmentedMUSICGrowthConstant d n m r Δ w :=
        segmentedMUSICGrowthConstant_pos (by omega) hn0 hΔ hw
      have hfinal :
          4 * matrixSpectralNorm E /
              (segmentedMUSICGrowthConstant d n m r Δ w *
                (minAmplitude μ hn0 * B ^ 2)) ≤
            4 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ /
              (segmentedMUSICGrowthConstant d n m r Δ w *
                (minAmplitude μ hn0 * B ^ 2)) := by
        apply div_le_div_of_nonneg_right _ (mul_pos hc hdenom).le
        nlinarith [hEbound]
      calc
        dist (estimate i) (toLp 2 (μ.node i)) ≤
            4 * matrixSpectralNorm E /
              (segmentedMUSICGrowthConstant d n m r Δ w *
                (minAmplitude μ hn0 * B ^ 2)) := (hest i).2.2
        _ ≤ 4 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ /
              (segmentedMUSICGrowthConstant d n m r Δ w *
                (minAmplitude μ hn0 * B ^ 2)) := hfinal
        _ = 4 * (segmentedLength m r : ℝ) ^ (3 * (d : ℝ) / 2) *
              (Real.pi * Real.sqrt d) ^ n * (2 / Δ) ^ (n - 1) * σ /
              (minAmplitude μ hn0 * B ^ 2 *
                (1 - w / (2 * Real.pi)) ^ n) := by
          calc
            _ = 4 * ((segmentedLength m r : ℝ) ^ d * σ) /
                (segmentedMUSICGrowthConstant d n m r Δ w *
                  (minAmplitude μ hn0 * B ^ 2)) := by
              rw [Nat.cast_pow]
              ring
            _ = 4 * (segmentedLength m r : ℝ) ^ (3 * (d : ℝ) / 2) *
                (Real.pi * Real.sqrt d) ^ n /
                (minAmplitude μ hn0 * B ^ 2 *
                  (1 - w / (2 * Real.pi)) ^ n) *
                (2 / Δ) ^ (n - 1) * σ :=
              segmented_peak_constant_identity (by omega) hΔ hw
                (minAmplitude_pos μ hn0) hBpos
            _ = _ := by ring
  · simpa only [hobs] using htop

end
end NumDetect
end LeanNumDetect
