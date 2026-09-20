import NumDetectMain.SegmentedProofSupport
import NumDetectMain.SegmentedThresholdSupport

/-! Segmented-frequency Vandermonde and thresholding results. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Manuscript-shaped segmented Vandermonde bound from an explicit fine-cube
frame input. -/
theorem segmentedVandermonde_minimumSingularValue_of_fineCubeFrame
    {d n A nStar m r D : ℕ} {τ η β : ℝ}
    (μ : AtomicMeasure d n)
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hm : 1 ≤ m) (hD : m < D)
    (hτ : τ ≤ Real.pi / (2 * D * d))
    (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β * d / (localizationOrder m nStar + 1) ≤ η)
    (hframe :
      HasFineCubeFrame d (localizationOrder m nStar) η
        (2 - Real.exp (1 / (2 * β))))
    (hr : 2 * nStar ≤ r)
    (hlocal :
      periodicMinimumL1Separation μ.node hn ≤
        Real.pi * nStar / ((r * D : ℕ) : ℝ)) :
    segmentedVandermondeLowerBound d n nStar m r D β
        (periodicMinimumL1Separation μ.node hn) ≤
      matrixSingularValue (segmentedVandermonde m r D μ.node) (n - 1) := by
  let Δ := periodicMinimumL1Separation μ.node hn
  have hDpos : 0 < D := Nat.zero_lt_of_lt (hm.trans_lt hD)
  have hΔ : 0 < Δ :=
    segmented_periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
  have hmin : ∀ i j, i ≠ j →
      Δ ≤ periodicL1Distance (μ.node i) (μ.node j) := by
    intro i j hij
    exact periodicMinimumL1Separation_le hn hij
  have hscale : Δ ≤ Real.pi * nStar / (r * D) := by
    change Δ ≤ Real.pi * (nStar : ℝ) / ((r : ℝ) * D)
    simpa only [Nat.cast_mul] using hlocal
  have hsplit : localizationHalfWidth m + m / 2 = m := by
    unfold localizationHalfWidth
    omega
  have hK :
      nStar * localizationOrder m nStar ≤ localizationHalfWidth m := by
    unfold localizationOrder
    simpa only [Nat.mul_comm] using
      Nat.div_mul_le_self (localizationHalfWidth m) nStar
  apply
    segmentedVandermonde_minimumSingularValue_of_colorFrames
      (m₁ := localizationHalfWidth m) (b := m / 2)
      (K := localizationOrder m nStar)
      μ hd hn hclumps hsplit hK hDpos hτ hβ hr hΔ hmin hscale
  intro C anchor _hsame hcross color v
  unfold HasFineCubeFrame at hframe
  have hcubeColor :
      ∀ j : ↥(clumpColorClass C anchor color), InAngularCube (μ.node j) :=
    fun j => hclumps.2.2.2.1 j
  have hsepColor :
      ∀ i j : ↥(clumpColorClass C anchor color), i ≠ j →
        η < periodicLInfDistance (μ.node i) (μ.node j) :=
    fun i j hij =>
      hcross i j (clumpColorClass_labels_ne C anchor color i j hij)
  exact @hframe
    (↥(clumpColorClass C anchor color)) inferInstance inferInstance
    (fun j => μ.node j) hcubeColor hsepColor v

/-- One-dimensional automatic range supplied by the proved consecutive-block
frame bound: `β ≥ 1` and the requested source constant is at most `1/2`. -/
theorem segmentedVandermonde_minimumSingularValue_oneDimensional_of_halfFrameRange
    {n A nStar m r D : ℕ} {τ η β : ℝ}
    (μ : AtomicMeasure 1 n)
    (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hm : 1 ≤ m) (hD : m < D)
    (hτ : τ ≤ Real.pi / (2 * D))
    (hβ : 1 / (2 * Real.log 2) < β)
    (hβone : 1 ≤ β)
    (ha : 2 - Real.exp (1 / (2 * β)) ≤ 1 / 2)
    (hη : 4 * Real.pi * β / (localizationOrder m nStar + 1) ≤ η)
    (hr : 2 * nStar ≤ r)
    (hlocal :
      periodicMinimumL1Separation μ.node hn ≤
        Real.pi * nStar / ((r * D : ℕ) : ℝ)) :
    segmentedVandermondeLowerBound 1 n nStar m r D β
        (periodicMinimumL1Separation μ.node hn) ≤
      matrixSingularValue (segmentedVandermonde m r D μ.node) (n - 1) := by
  let Δ := periodicMinimumL1Separation μ.node hn
  have hDpos : 0 < D := Nat.zero_lt_of_lt (hm.trans_lt hD)
  have hΔ : 0 < Δ :=
    segmented_periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
  have hmin : ∀ i j, i ≠ j →
      Δ ≤ periodicL1Distance (μ.node i) (μ.node j) := by
    intro i j hij
    exact periodicMinimumL1Separation_le hn hij
  have hscale : Δ ≤ Real.pi * nStar / (r * D) := by
    change Δ ≤ Real.pi * (nStar : ℝ) / ((r : ℝ) * D)
    simpa only [Nat.cast_mul] using hlocal
  have hsplit : localizationHalfWidth m + m / 2 = m := by
    unfold localizationHalfWidth
    omega
  have hK :
      nStar * localizationOrder m nStar ≤ localizationHalfWidth m := by
    unfold localizationOrder
    simpa only [Nat.mul_comm] using
      Nat.div_mul_le_self (localizationHalfWidth m) nStar
  apply
    segmentedVandermonde_minimumSingularValue_of_colorFrames
      (m₁ := localizationHalfWidth m) (b := m / 2)
      (K := localizationOrder m nStar)
      μ (by omega) hn hclumps hsplit hK hDpos (by simpa using hτ)
        hβ hr hΔ hmin hscale
  intro C anchor _hsame hcross color v
  apply fineCube_frame_oneDimensional_of_sourceRange
    β η hβone ha hη
    (fun j : ↥(clumpColorClass C anchor color) => μ.node j)
  · intro j
    exact hclumps.2.2.2.1 j
  · intro i j hij
    exact hcross i j (clumpColorClass_labels_ne C anchor color i j hij)

/-- Segmented threshold theorem from an explicit fine-cube frame input.
Singular-value indices are zero-based. -/
theorem segmentedGHM_singularValueThreshold_of_fineCubeFrame
    {d n A nStar m r D : ℕ} {τ η β σ mMin : ℝ}
    (μ : AtomicMeasure d n) (Y : Point d → ℂ)
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hm : 1 ≤ m) (hD : m < D)
    (hτ : τ ≤ Real.pi / (2 * D * d))
    (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β * d / (localizationOrder m nStar + 1) ≤ η)
    (hframe :
      HasFineCubeFrame d (localizationOrder m nStar) η
        (2 - Real.exp (1 / (2 * β))))
    (hr : 2 * nStar ≤ r)
    (hσ : 0 < σ)
    (hmMin : minAmplitude μ (Nat.zero_lt_of_lt hn) = mMin)
    (hnoise : σ < mMin)
    (hmeasurement :
      IsBandMeasurement μ (segmentedCutoff m r D) σ Y) :
    (∀ j, n ≤ j → j < (segmentedLength m r) ^ d →
      matrixSingularValue (segmentedMeasurementMatrix m r D Y) j ≤
        ((segmentedLength m r : ℕ) : ℝ) ^ d * σ) ∧
    (periodicMinimumL1Separation μ.node hn ≤
        Real.pi * nStar / ((r * D : ℕ) : ℝ) →
      segmentedDetectionSeparationThreshold d n nStar m r D β σ mMin <
          periodicMinimumL1Separation μ.node hn →
      ((segmentedLength m r : ℕ) : ℝ) ^ d * σ <
        matrixSingularValue (segmentedMeasurementMatrix m r D Y) (n - 1)) := by
  let B :=
    segmentedVandermondeLowerBound d n nStar m r D β
      (periodicMinimumL1Separation μ.node hn)
  constructor
  · intro j hj hjcard
    exact segmentedThreshold_noise_singularValue_le
      μ Y hmeasurement hj hjcard
  · intro hlocal hseparation
    have hB :
        B ≤ matrixSingularValue
          (segmentedVandermonde m r D μ.node) (n - 1) := by
      exact segmentedVandermonde_minimumSingularValue_of_fineCubeFrame
        μ hd hn hclumps hm hD hτ hβ hη hframe hr hlocal
    exact
      (segmentedGHM_singularValueThreshold_of_segmentedLowerBound
        μ Y hd hn hclumps hm hD hτ hβ hη hr hσ hmMin hnoise hmeasurement
        (B := B) le_rfl hB).2 hlocal hseparation

/-- One-dimensional segmented threshold theorem in the range supplied by the
proved `1/2` consecutive-block frame bound. -/
theorem segmentedGHM_singularValueThreshold_oneDimensional_of_halfFrameRange
    {n A nStar m r D : ℕ} {τ η β σ mMin : ℝ}
    (μ : AtomicMeasure 1 n) (Y : Point 1 → ℂ)
    (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hm : 1 ≤ m) (hD : m < D)
    (hτ : τ ≤ Real.pi / (2 * D))
    (hβ : 1 / (2 * Real.log 2) < β)
    (hβone : 1 ≤ β)
    (ha : 2 - Real.exp (1 / (2 * β)) ≤ 1 / 2)
    (hη : 4 * Real.pi * β / (localizationOrder m nStar + 1) ≤ η)
    (hr : 2 * nStar ≤ r)
    (hσ : 0 < σ)
    (hmMin : minAmplitude μ (Nat.zero_lt_of_lt hn) = mMin)
    (hnoise : σ < mMin)
    (hmeasurement :
      IsBandMeasurement μ (segmentedCutoff m r D) σ Y) :
    (∀ j, n ≤ j → j < segmentedLength m r →
      matrixSingularValue (segmentedMeasurementMatrix m r D Y) j ≤
        (segmentedLength m r : ℝ) * σ) ∧
    (periodicMinimumL1Separation μ.node hn ≤
        Real.pi * nStar / ((r * D : ℕ) : ℝ) →
      segmentedDetectionSeparationThreshold 1 n nStar m r D β σ mMin <
          periodicMinimumL1Separation μ.node hn →
      (segmentedLength m r : ℝ) * σ <
        matrixSingularValue (segmentedMeasurementMatrix m r D Y) (n - 1)) := by
  let B :=
    segmentedVandermondeLowerBound 1 n nStar m r D β
      (periodicMinimumL1Separation μ.node hn)
  constructor
  · intro j hj hjcard
    simpa using
      (segmentedThreshold_noise_singularValue_le
        μ Y hmeasurement hj (by simpa using hjcard))
  · intro hlocal hseparation
    have hB :
        B ≤ matrixSingularValue
          (segmentedVandermonde m r D μ.node) (n - 1) := by
      exact
        segmentedVandermonde_minimumSingularValue_oneDimensional_of_halfFrameRange
          μ hn hclumps hm hD hτ hβ hβone ha hη hr hlocal
    have h :=
      (segmentedGHM_singularValueThreshold_of_segmentedLowerBound
        μ Y (by omega) hn hclumps hm hD (by simpa using hτ) hβ
        (by simpa using hη) hr hσ hmMin hnoise hmeasurement
        (B := B) le_rfl hB).2 hlocal hseparation
    simpa using h

end

end NumDetect
end LeanNumDetect
