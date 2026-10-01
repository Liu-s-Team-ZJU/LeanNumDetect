import NumDetect.SegmentedMUSICGrowth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Segmented-array MUSIC location error with its explicit growth constant. -/
theorem exists_segmentedMUSIC_location_stability
    {d n m r D : ℕ} (μ : AtomicMeasure d n)
    (E : Matrix (SegmentedIndex d m r) (SegmentedIndex d m r) ℂ)
    (K : Set (Point d)) (Δ w : ℝ)
    (hd : 0 < d) (hn : 0 < n) (hm : n ≤ m) (hmD : m < D)
    (hΔ : 0 < Δ) (hw : w < 2 * Real.pi)
    (hK : IsCompact K) (hnodeK : ∀ j, μ.node j ∈ K)
    (hwidth : ∀ u ∈ K, ∀ v ∈ K, ∀ k, |u k - v k| ≤ w)
    (hsep : ∀ i j, i ≠ j →
      Δ ≤ pointEuclideanDistance (μ.node i) (μ.node j))
    (hsmallMatrix :
      2 * matrixSpectralNorm E <
        musicSignalGap (segmentedFrequency d m r D)
          (segmentedFrequency d m r D) μ hn)
    (hsmallLocation :
      2 * matrixSpectralNorm E /
          musicSignalGap (segmentedFrequency d m r D)
            (segmentedFrequency d m r D) μ hn <
        segmentedMUSICGrowthConstant d n m r Δ w * Δ / 8) :
    ∃ estimate : Fin n → Point d,
      (∀ i, estimate i ∈ K) ∧
      (∀ i j, i ≠ j →
        Δ / 2 ≤ pointEuclideanDistance (estimate i) (estimate j)) ∧
      (∀ z : Fin n → Point d,
        (∀ i, z i ∈ K) →
        (∀ i j, i ≠ j →
          Δ / 2 ≤ pointEuclideanDistance (z i) (z j)) →
        (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
          (fun i => rankNoiseSpaceCorrelation
            (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ + E) n (estimate i)) ≤
        (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
          (fun i => rankNoiseSpaceCorrelation
            (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ + E) n (z i))) ∧
      ∃ e : Equiv.Perm (Fin n), ∀ i,
        pointEuclideanDistance (estimate i) (μ.node (e i)) ≤
          4 * matrixSpectralNorm E /
            (segmentedMUSICGrowthConstant d n m r Δ w *
              musicSignalGap (segmentedFrequency d m r D)
                (segmentedFrequency d m r D) μ hn) := by
  obtain ⟨hfull, hc, hgrowth⟩ :=
    segmentedMUSIC_growth μ K Δ w hd hn hm hmD hΔ hw hnodeK hwidth hsep
  have hcard : n < Fintype.card (SegmentedIndex d m r) :=
    sourceCount_lt_card_segmentedIndex hd hm
  have hfull₂ : HasFullColumnRank
      (generalizedVandermonde (segmentedFrequency d m r D) μ.node) := by
    simpa only [segmentedVandermonde] using hfull
  have hgrowth' : ∀ y ∈ K,
      segmentedMUSICGrowthConstant d n m r Δ w *
          min (Δ / 4) (finiteEuclideanSourceDistance hn μ.node y) ≤
        rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
          (generalizedVandermonde (segmentedFrequency d m r D) μ.node *
            Matrix.diagonal (segmentedPhaseAmplitude m r D μ) *
            Matrix.transpose
              (generalizedVandermonde (segmentedFrequency d m r D) μ.node))
          n y := by
    simpa only [segmentedNoiselessMatrix, segmentedVandermonde,
      segmentedColumnVandermonde] using hgrowth
  simpa only [segmentedNoiselessMatrix, segmentedVandermonde,
    segmentedColumnVandermonde] using
    (exists_ghmMUSIC_location_stability
      (segmentedFrequency d m r D) (segmentedFrequency d m r D)
      μ (segmentedPhaseAmplitude m r D μ) E K Δ
      (segmentedMUSICGrowthConstant d n m r Δ w)
      hn hcard hcard.le
      (fun j => minAmplitude_le_norm_segmentedPhaseAmplitude m r D μ hn j)
      hfull₂ hfull₂ hsmallMatrix hc hΔ hsmallLocation hK hnodeK hsep
      hgrowth')

/-- Any positive lower bound for the segmented Vandermonde singular value
gives an explicit segmented MUSIC location error. -/
theorem exists_segmentedMUSIC_location_stability_of_lowerBound
    {d n m r D : ℕ} (μ : AtomicMeasure d n)
    (E : Matrix (SegmentedIndex d m r) (SegmentedIndex d m r) ℂ)
    (K : Set (Point d)) (Δ w B : ℝ)
    (hd : 0 < d) (hn : 0 < n) (hm : n ≤ m) (hmD : m < D)
    (hΔ : 0 < Δ) (hw : w < 2 * Real.pi)
    (hK : IsCompact K) (hnodeK : ∀ j, μ.node j ∈ K)
    (hwidth : ∀ u ∈ K, ∀ v ∈ K, ∀ k, |u k - v k| ≤ w)
    (hsep : ∀ i j, i ≠ j →
      Δ ≤ pointEuclideanDistance (μ.node i) (μ.node j))
    (hBpos : 0 < B)
    (hB : B ≤ matrixSingularValue
      (segmentedVandermonde m r D μ.node) (n - 1))
    (hsmallMatrix :
      2 * matrixSpectralNorm E < minAmplitude μ hn * B ^ 2)
    (hsmallLocation :
      2 * matrixSpectralNorm E / (minAmplitude μ hn * B ^ 2) <
        segmentedMUSICGrowthConstant d n m r Δ w * Δ / 8) :
    ∃ estimate : Fin n → Point d,
      (∀ i, estimate i ∈ K) ∧
      (∀ i j, i ≠ j →
        Δ / 2 ≤ pointEuclideanDistance (estimate i) (estimate j)) ∧
      (∀ z : Fin n → Point d,
        (∀ i, z i ∈ K) →
        (∀ i j, i ≠ j →
          Δ / 2 ≤ pointEuclideanDistance (z i) (z j)) →
        (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
          (fun i => rankNoiseSpaceCorrelation
            (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ + E) n (estimate i)) ≤
        (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
          (fun i => rankNoiseSpaceCorrelation
            (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ + E) n (z i))) ∧
      ∃ e : Equiv.Perm (Fin n), ∀ i,
        pointEuclideanDistance (estimate i) (μ.node (e i)) ≤
          4 * matrixSpectralNorm E /
            (segmentedMUSICGrowthConstant d n m r Δ w *
              (minAmplitude μ hn * B ^ 2)) := by
  let c := segmentedMUSICGrowthConstant d n m r Δ w
  let G := minAmplitude μ hn * B ^ 2
  let S := matrixSingularValue (segmentedVandermonde m r D μ.node) (n - 1)
  let gap := musicSignalGap (segmentedFrequency d m r D)
    (segmentedFrequency d m r D) μ hn
  have hc : 0 < c := segmentedMUSICGrowthConstant_pos hd hn hΔ hw
  have hG : 0 < G := by
    dsimp [G]
    exact mul_pos (minAmplitude_pos μ hn) (sq_pos_of_pos hBpos)
  have hS : 0 ≤ S := matrixSingularValue_nonneg _ _
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
  obtain ⟨estimate, hestK, hsepEst, hmin, e, herr⟩ :=
    exists_segmentedMUSIC_location_stability μ E K Δ w
      hd hn hm hmD hΔ hw hK hnodeK hwidth hsep
      hsmallGap (lt_of_le_of_lt hratio hsmallLocation)
  refine ⟨estimate, hestK, hsepEst, hmin, e, ?_⟩
  intro i
  have hbound : 4 * matrixSpectralNorm E / (c * gap) ≤
      4 * matrixSpectralNorm E / (c * G) := by
    apply div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) (norm_nonneg _))
      (mul_pos hc hG)
    exact mul_le_mul_of_nonneg_left hGS hc.le
  exact (herr i).trans hbound

/-- The segmented multi-clump singular-value bound and entrywise measurement
noise give a completely explicit location estimate. -/
theorem exists_segmentedMUSIC_location_stability_of_measurement
    {d n A nStar m r D : ℕ} {τ η β Δ w σ : ℝ}
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
        min 1 (segmentedMUSICGrowthConstant d n m r Δ w * Δ / 8)) :
    ∃ estimate : Fin n → Point d,
      (∀ i, estimate i ∈ K) ∧
      (∀ i j, i ≠ j →
        Δ / 2 ≤ pointEuclideanDistance (estimate i) (estimate j)) ∧
      (∀ z : Fin n → Point d,
        (∀ i, z i ∈ K) →
        (∀ i j, i ≠ j →
          Δ / 2 ≤ pointEuclideanDistance (z i) (z j)) →
        (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty (by omega))
          (fun i => rankNoiseSpaceCorrelation
            (segmentedFrequency d m r D)
            (segmentedMeasurementMatrix m r D Y) n (estimate i)) ≤
        (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty (by omega))
          (fun i => rankNoiseSpaceCorrelation
            (segmentedFrequency d m r D)
            (segmentedMeasurementMatrix m r D Y) n (z i))) ∧
      ∃ e : Equiv.Perm (Fin n), ∀ i,
        pointEuclideanDistance (estimate i) (μ.node (e i)) ≤
          4 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ /
            (segmentedMUSICGrowthConstant d n m r Δ w *
              (minAmplitude μ (by omega) *
                (segmentedMUSICClumpBound d n nStar m r D β
                  (periodicMinimumL1Separation μ.node (by omega))) ^ 2)) := by
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
  have hsmallLocation : 2 * matrixSpectralNorm E /
        (minAmplitude μ hn0 * B ^ 2) <
      segmentedMUSICGrowthConstant d n m r Δ w * Δ / 8 :=
    lt_of_le_of_lt hratio (lt_min_iff.mp hnoise).2
  obtain ⟨estimate, hestK, hsepEst, hmin, e, herr⟩ :=
    exists_segmentedMUSIC_location_stability_of_lowerBound μ E K Δ w B
      (by omega) hn0 hm hD hΔ hw hK hnodeK hwidth hsep
      hBpos hB hsmallMatrix hsmallLocation
  have hobs : segmentedNoiselessMatrix m r D μ + E =
      segmentedMeasurementMatrix m r D Y := by
    dsimp [E]
    abel
  refine ⟨estimate, hestK, hsepEst, ?_, e, ?_⟩
  · simpa only [hobs] using hmin
  · intro i
    have hc : 0 < segmentedMUSICGrowthConstant d n m r Δ w :=
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
    exact (herr i).trans hfinal

private theorem segmented_location_constant_algebra
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

private theorem segmented_location_reciprocal
    (n : ℕ) (Δ : ℝ) (hΔ : 0 < Δ) :
    (Δ / 2) ^ (n - 1) * (2 / Δ) ^ (n - 1) = 1 := by
  rw [← mul_pow]
  have hmul : (Δ / 2) * (2 / Δ) = 1 := by
    field_simp

  rw [hmul]
  simp

private theorem segmented_location_L_powers
    (L : ℝ) (d : ℕ) (hL : 0 < L) :
    L ^ d * L ^ ((d : ℝ) / 2) = L ^ (3 * (d : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hL]
  congr 1
  ring

private theorem segmented_location_constant_identity
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
  have hP : 0 < (Real.pi * Real.sqrt d) ^ n := by
    positivity
  have hQ : 0 < (1 - w / (2 * Real.pi)) ^ n := by
    have hw' : 0 < 1 - w / (2 * Real.pi) := by
      apply sub_pos.mpr
      exact (div_lt_one (by positivity)).mpr hw
    positivity
  have hT : 0 < (Δ / 2) ^ (n - 1) := by positivity
  have hrec := segmented_location_reciprocal n Δ hΔ
  have hbase := segmented_location_constant_algebra
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

/-- The final location error for a segmented array under multi-clump geometry,
written with the constants displayed in the manuscript. -/
theorem exists_segmentedMUSIC_location_stability_explicit
    {d n A nStar m r D : ℕ} {τ η β Δ w σ : ℝ}
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
        min 1 (segmentedMUSICGrowthConstant d n m r Δ w * Δ / 8)) :
    ∃ estimate : Fin n → Point d,
      (∀ i, estimate i ∈ K) ∧
      (∀ i j, i ≠ j →
        Δ / 2 ≤ pointEuclideanDistance (estimate i) (estimate j)) ∧
      (∀ z : Fin n → Point d,
        (∀ i, z i ∈ K) →
        (∀ i j, i ≠ j →
          Δ / 2 ≤ pointEuclideanDistance (z i) (z j)) →
        (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty (by omega))
          (fun i => rankNoiseSpaceCorrelation
            (segmentedFrequency d m r D)
            (segmentedMeasurementMatrix m r D Y) n (estimate i)) ≤
        (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty (by omega))
          (fun i => rankNoiseSpaceCorrelation
            (segmentedFrequency d m r D)
            (segmentedMeasurementMatrix m r D Y) n (z i))) ∧
      ∃ e : Equiv.Perm (Fin n), ∀ i,
        pointEuclideanDistance (estimate i) (μ.node (e i)) ≤
          4 * (segmentedLength m r : ℝ) ^ (3 * (d : ℝ) / 2) *
            (Real.pi * Real.sqrt d) ^ n *
            (2 / Δ) ^ (n - 1) * σ /
            (minAmplitude μ (by omega) *
              (segmentedMUSICClumpBound d n nStar m r D β
                (periodicMinimumL1Separation μ.node (by omega))) ^ 2 *
              (1 - w / (2 * Real.pi)) ^ n) := by
  have hn0 : 0 < n := by omega
  let B := segmentedMUSICClumpBound d n nStar m r D β
    (periodicMinimumL1Separation μ.node hn)
  obtain ⟨estimate, hestK, hsepEst, hmin, e, herr⟩ :=
    exists_segmentedMUSIC_location_stability_of_measurement μ Y K
      hd hn hclumps hm hD hτ hβ hη hr hlocal hΔ hw
      hK hnodeK hwidth hsep hmeasurement hnoise
  have hBpos : 0 < B := by
    exact segmentedVandermondeLowerBound_pos μ hn hclumps
      (by omega : 1 ≤ m) hD hβ hr
  have hid := segmented_location_constant_identity
    (d := d) (n := n) (m := m) (r := r)
    (Δ := Δ) (w := w) (σ := σ)
    (mMin := minAmplitude μ hn0) (B := B)
    (by omega : 0 < d) hΔ hw (minAmplitude_pos μ hn0) hBpos
  refine ⟨estimate, hestK, hsepEst, hmin, e, ?_⟩
  intro i
  calc
    pointEuclideanDistance (estimate i) (μ.node (e i)) ≤
        4 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ /
          (segmentedMUSICGrowthConstant d n m r Δ w *
            (minAmplitude μ hn0 * B ^ 2)) := herr i
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
            (2 / Δ) ^ (n - 1) * σ := hid
        _ = _ := by ring

end
end NumDetect
end LeanNumDetect
