import General.Probability.BoundedRowEstimates

/-!
# The deterministic small-envelope regime of bounded-row concentration

If the row-energy envelope is already below the requested error, every
outcome satisfies the uniform estimate almost everywhere. This discharges
the small-radius case without imposing an artificial lower bound on `s K²`.
Arbitrary target sets and arbitrary probability spaces are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MeasureTheory ProbabilityTheory

universe u v
namespace LeanNumDetect.BoundedRieszConcentration

/-- Identically distributed rows share their coordinate envelope jointly,
without any independence assumption. -/
theorem identDistrib_rows_ae_bound {N m : ℕ} {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ComplexVector N)
    (rows : Fin m → Ω' → ComplexVector N)
    (hcopy : ∀ i, IdentDistrib (rows i) X ν μ) {K : ℝ}
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    ∀ᵐ ω ∂ν, ∀ i j, ‖rows i ω j‖ ≤ K := by
  apply ae_all_iff.mpr
  intro i
  exact identDistrib_ae_all_coordinates_bound μ ν X (rows i) (hcopy i) hbound

/-- Uniform error bounded by the energy envelope almost everywhere. -/
theorem restrictedDeviation_ae_le_radius {N m : ℕ} {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ)
    (rows : Fin m → Ω' → ComplexVector N) (hm : 0 < m)
    (hcopy : ∀ i, IdentDistrib (rows i) X ν μ)
    (T : Set (ComplexVector N)) {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    ∀ᵐ ω ∂ν, restrictedDeviation μ X rows T ω ≤ s * K ^ 2 := by
  filter_upwards [identDistrib_rows_ae_bound μ ν X rows hcopy hbound] with ω hω
  exact restrictedDeviation_le_radius μ X hX rows hm T ω hs hK hT hbound hω

/-- The original additive-plus-covariance deviation event has probability one
when the energy envelope is below the distortion parameter. -/
theorem smallEnvelope_success_probability {N m : ℕ} {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ)
    (rows : Fin m → Ω' → ComplexVector N) (hm : 0 < m)
    (hcopy : ∀ i, IdentDistrib (rows i) X ν μ)
    (T : Set (ComplexVector N)) {s K δ c : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hδ : 0 ≤ δ) (hc : 1 ≤ c) (henvelope : s * K ^ 2 ≤ δ)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    (ν {ω | restrictedDeviation μ X rows T ω ≤
      c * (δ + δ * populationEnergySup μ X T)}).toReal = 1 := by
  have hmean := populationEnergySup_nonneg μ X hX T hs hK hT hbound
  have hthreshold : s * K ^ 2 ≤ c * (δ + δ * populationEnergySup μ X T) := by
    have hd : δ ≤ δ + δ * populationEnergySup μ X T :=
      le_add_of_nonneg_right (mul_nonneg hδ hmean)
    exact henvelope.trans (hd.trans (le_mul_of_one_le_left (by positivity) hc))
  have hgood : ∀ᵐ ω ∂ν, restrictedDeviation μ X rows T ω ≤
      c * (δ + δ * populationEnergySup μ X T) :=
    (restrictedDeviation_ae_le_radius μ ν X hX rows hm hcopy T hs hK hT hbound).mono
      (fun _ h => h.trans hthreshold)
  have hset : {ω | restrictedDeviation μ X rows T ω ≤
      c * (δ + δ * populationEnergySup μ X T)} =ᵐ[ν] Set.univ := by
    filter_upwards [hgood] with ω hω
    change (restrictedDeviation μ X rows T ω ≤
      c * (δ + δ * populationEnergySup μ X T)) = True
    exact propext (iff_true_intro hω)
  rw [measure_congr hset]
  simp

/-- More generally, any positive multiple of the distortion can serve as
the deterministic envelope threshold. This handles the regime where the
source logarithm is small without strengthening its sampling premise. -/
theorem scaledEnvelope_success_probability {N m : ℕ} {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ)
    (rows : Fin m → Ω' → ComplexVector N) (hm : 0 < m)
    (hcopy : ∀ i, IdentDistrib (rows i) X ν μ)
    (T : Set (ComplexVector N)) {s K δ c : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (henvelope : s * K ^ 2 ≤ c * δ)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    (ν {ω | restrictedDeviation μ X rows T ω ≤
      c * (δ + δ * populationEnergySup μ X T)}).toReal = 1 := by
  have hmean := populationEnergySup_nonneg μ X hX T hs hK hT hbound
  have hthreshold : s * K ^ 2 ≤ c * (δ + δ * populationEnergySup μ X T) :=
    henvelope.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (mul_nonneg hδ hmean)) hc)
  have hgood : ∀ᵐ ω ∂ν, restrictedDeviation μ X rows T ω ≤
      c * (δ + δ * populationEnergySup μ X T) :=
    (restrictedDeviation_ae_le_radius μ ν X hX rows hm hcopy T hs hK hT hbound).mono
      (fun _ h => h.trans hthreshold)
  have hset : {ω | restrictedDeviation μ X rows T ω ≤
      c * (δ + δ * populationEnergySup μ X T)} =ᵐ[ν] Set.univ := by
    filter_upwards [hgood] with ω hω
    change (restrictedDeviation μ X rows T ω ≤
      c * (δ + δ * populationEnergySup μ X T)) = True
    exact propext (iff_true_intro hω)
  rw [measure_congr hset]
  simp

/-- The strict lower probability bound in the source is also satisfied in
this regime, for every positive distortion and energy radius. -/
theorem smallEnvelope_strict_success_probability {N m : ℕ} {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ)
    (rows : Fin m → Ω' → ComplexVector N) (hm : 0 < m)
    (hcopy : ∀ i, IdentDistrib (rows i) X ν μ)
    (T : Set (ComplexVector N)) {s K δ c : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hδ : 0 ≤ δ) (hc : 1 ≤ c) (henvelope : s * K ^ 2 ≤ δ)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    1 - 2 * Real.exp (-(δ ^ 2 * (m : ℝ) / (s * K ^ 2))) <
      (ν {ω | restrictedDeviation μ X rows T ω ≤
        c * (δ + δ * populationEnergySup μ X T)}).toReal := by
  rw [smallEnvelope_success_probability μ ν X hX rows hm hcopy T hs hK hδ hc
    henvelope hT hbound]
  linarith [Real.exp_pos (-(δ ^ 2 * (m : ℝ) / (s * K ^ 2)))]

end LeanNumDetect.BoundedRieszConcentration
