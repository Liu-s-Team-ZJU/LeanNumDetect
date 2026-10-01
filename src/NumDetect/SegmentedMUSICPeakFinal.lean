import NumDetect.MUSICPeakReciprocal
import NumDetect.MUSICPeakSegmentedRadialLoss
import NumDetect.SegmentedMUSICPeakProjectorCurvature
import NumDetect.SegmentedMUSICPeakCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WithLp Set
open scoped Topology
namespace LeanNumDetect
namespace NumDetect
noncomputable section

/-- Under the explicit segmented-array geometry and noise threshold, the top
continuous peaks of the extended MUSIC image identify one point per source. -/
theorem exists_segmentedMUSIC_highestExtendedPeaks_explicit
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
    (hballInterior : ∀ i,
      Metric.closedBall (toLp 2 (μ.node i)) ρ ⊆ interior ((toLp 2) '' K))
    (hmeasurement : IsSegmentedMeasurement μ m r D σ Y)
    (hradius :
      8 * (d : ℝ) ^ (3 / 2 : ℝ) *
          (segmentedCutoff m r D : ℝ) ^ 3 * ρ ≤
        segmentedMUSICGrowthConstant d n m r Δ w ^ 2)
    (hnoise :
      2 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ /
          (minAmplitude μ (by omega) *
            (segmentedMUSICClumpBound d n nStar m r D β
              (periodicMinimumL1Separation μ.node (by omega))) ^ 2) <
        min 1 (min
          (segmentedMUSICGrowthConstant d n m r Δ w * ρ / 2)
          (segmentedMUSICGrowthConstant d n m r Δ w ^ 2 /
            (8 * (d : ℝ) * (segmentedCutoff m r D : ℝ) ^ 2)))) :
    ∃ estimate : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, estimate i ∈ (toLp 2) '' K ∧
        IsLocalMaxOn
          (extendedMUSICImaging (fun z : EuclideanSpace ℝ (Fin d) =>
            rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
              (segmentedMeasurementMatrix m r D Y) n (ofLp z)))
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
        IsLocalMaxOn
          (extendedMUSICImaging (fun z : EuclideanSpace ℝ (Fin d) =>
            rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
              (segmentedMeasurementMatrix m r D Y) n (ofLp z)))
          ((toLp 2) '' K) y →
        y ∉ Set.range estimate → ∀ i,
          extendedMUSICImaging (fun z : EuclideanSpace ℝ (Fin d) =>
            rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
              (segmentedMeasurementMatrix m r D Y) n (ofLp z)) y <
          extendedMUSICImaging (fun z : EuclideanSpace ℝ (Fin d) =>
            rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
              (segmentedMeasurementMatrix m r D Y) n (ofLp z)) (estimate i)) := by
  have hn0 : 0 < n := by omega
  let B := segmentedMUSICClumpBound d n nStar m r D β
    (periodicMinimumL1Separation μ.node hn)
  let E := segmentedMeasurementMatrix m r D Y - segmentedNoiselessMatrix m r D μ
  let Ω : ℝ := segmentedCutoff m r D
  let ΩA : ℝ := Real.sqrt d * Ω
  let ε : ℝ := 2 * matrixSpectralNorm E / (minAmplitude μ hn0 * B ^ 2)
  let εBudget : ℝ := 2 * (((segmentedLength m r) ^ d : ℕ) : ℝ) * σ /
    (minAmplitude μ hn0 * B ^ 2)
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
  have hε : ε ≤ εBudget := by
    dsimp [ε, εBudget]
    apply div_le_div_of_nonneg_right _ hdenom.le
    nlinarith [hEbound]
  have hnoise' : εBudget <
      min 1 (min
        (segmentedMUSICGrowthConstant d n m r Δ w * ρ / 2)
        (segmentedMUSICGrowthConstant d n m r Δ w ^ 2 /
          (8 * (d : ℝ) * Ω ^ 2))) := by
    simpa only [εBudget, B, Ω] using hnoise
  have hsmallMatrix : 2 * matrixSpectralNorm E <
      minAmplitude μ hn0 * B ^ 2 := by
    apply (div_lt_one hdenom).mp
    exact lt_of_le_of_lt hε (lt_min_iff.mp hnoise').1
  have hsmallPeak : ε < segmentedMUSICGrowthConstant d n m r Δ w * ρ / 2 :=
    lt_of_le_of_lt hε (lt_min_iff.mp (lt_min_iff.mp hnoise').2).1
  have hΩpos : 0 < Ω := by
    have hm0 : 0 < m := by omega
    have hcut : 0 < segmentedCutoff m r D := by
      simp only [segmentedCutoff]
      omega
    change (0 : ℝ) < (segmentedCutoff m r D : ℝ)
    exact_mod_cast hcut
  have hrad : 8 * ΩA ^ 3 * ρ ≤
      segmentedMUSICGrowthConstant d n m r Δ w ^ 2 := by
    exact segmented_peak_radius_condition d Ω ρ
      (segmentedMUSICGrowthConstant d n m r Δ w) hradius
  have hcurvNoise : 4 * ΩA ^ 2 * ε <
      segmentedMUSICGrowthConstant d n m r Δ w ^ 2 / 2 := by
    apply segmented_peak_noise_condition d Ω
      (segmentedMUSICGrowthConstant d n m r Δ w) ε (by omega) hΩpos
    exact lt_of_le_of_lt hε (lt_min_iff.mp (lt_min_iff.mp hnoise').2).2
  have hballK : ∀ i,
      Metric.closedBall (toLp 2 (μ.node i)) ρ ⊆ (toLp 2) '' K := by
    intro i
    exact (hballInterior i).trans interior_subset
  have hradiusVariation : ∀ i,
      ∀ z ∈ Metric.closedBall (toLp 2 (μ.node i)) ρ,
      ∀ v : EuclideanSpace ℝ (Fin d),
        lineCurvature
            (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
              (segmentedNoiselessMatrix m r D μ) n)
            (toLp 2 (μ.node i)) v -
          8 * ΩA ^ 3 * ρ * ‖v‖ ^ 2 ≤
        lineCurvature
          (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ) n) z v := by
    intro i z hz v
    exact segmentedFourierMUSIC_radialCurvature_lower (n := n)
      (segmentedNoiselessMatrix m r D μ) (toLp 2 (μ.node i)) z v ρ hz
  have hprojectorVariation : ∀ i,
      ∀ z ∈ Metric.closedBall (toLp 2 (μ.node i)) ρ,
      ∀ v : EuclideanSpace ℝ (Fin d),
        lineCurvature
            (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
              (segmentedNoiselessMatrix m r D μ) n) z v -
          4 * ΩA ^ 2 * ε * ‖v‖ ^ 2 ≤
        lineCurvature
          (finiteFourierSquaredMUSIC (segmentedFrequency d m r D)
            (segmentedNoiselessMatrix m r D μ + E) n) z v := by
    intro i z hz v
    exact segmentedMUSIC_lineCurvature_lower_of_matrixPerturb
      μ E B (by omega) hn0 hm hBpos hB hsmallMatrix z v
  have hstrict := segmentedMUSIC_strictConvexOn_sourceBalls_of_curvatureBounds
    μ E K Δ w ρ ΩA ε (by omega) hn0 hm hD hΔ hw hρ
    hnodeK hwidth hsep hballK hradiusVariation hprojectorVariation
    hrad hcurvNoise
  have hobs : segmentedNoiselessMatrix m r D μ + E =
      segmentedMeasurementMatrix m r D Y := by
    dsimp [E]
    abel
  have hnoisePeak : εBudget <
      min 1 (segmentedMUSICGrowthConstant d n m r Δ w * ρ / 2) := by
    exact lt_min_iff.mpr ⟨(lt_min_iff.mp hnoise').1,
      (lt_min_iff.mp (lt_min_iff.mp hnoise').2).1⟩
  obtain ⟨estimate, hest, hinj, htop⟩ :=
    exists_segmentedMUSIC_highestPeaks_explicit μ Y K hd hn hclumps hm hD
      hτ hβ hη hr hlocal hΔ hw hρ hfour hK hnodeK hwidth hsep
      hmeasurement hnoisePeak (by simpa only [hobs] using hstrict)
  let Rσ : EuclideanSpace ℝ (Fin d) → ℝ := fun z =>
    rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
      (segmentedMeasurementMatrix m r D Y) n (ofLp z)
  have hpos : ∀ z ∈ (toLp 2) '' K, 0 ≤ Rσ z := by
    intro z _
    exact norm_nonneg _
  have hJ := top_squaredResidual_minima_are_extendedMUSIC_peaks
    Rσ ((toLp 2) '' K) estimate hpos
    (fun i => (hest i).1)
    (fun i => (hest i).2.1) htop
  refine ⟨estimate, ?_, hinj, ?_⟩
  · intro i
    exact ⟨(hest i).1, hJ.1 i, (hest i).2.2⟩
  · exact hJ.2

end
end NumDetect
end LeanNumDetect
