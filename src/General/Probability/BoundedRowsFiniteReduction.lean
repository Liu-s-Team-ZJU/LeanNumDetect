import General.Probability.BoundedRowQuantization
import General.Probability.BoundedRowDistributionApproximation
import General.Probability.BoundedRowTargetApproximation
import General.Probability.FiniteBoundedRowConcentration
import General.Probability.FiniteWeightedLaw
import General.Probability.IIDJointLaw

/-! Finite reduction of arbitrary bounded row distributions and arbitrary
coefficient classes. The concentration premise concerns only finite alphabets
and finite target families; all approximation and law transport below are
proved independently of any sample-size requirement. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe u v

namespace LeanNumDetect.BoundedRieszConcentration

open FiniteEntropy

/-- Finite enumeration of a target subset gives its actual population supremum. -/
theorem populationEnergySup_eq_finiteRowPopulationSup {N L J : ℕ}
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ComplexVector N) (decoder : Fin L → ComplexVector N)
    (f : Fin J → ComplexVector N) (q : Fin L → ℝ)
    (F : Set (ComplexVector N)) (hF : Set.range f = F)
    (hpop : ∀ g, populationEnergy μ Y g =
      weightedMean q (fun a => rowEnergy g (decoder a))) :
    populationEnergySup μ Y F = finiteRowPopulationSup decoder f q := by
  unfold populationEnergySup finiteRowPopulationSup
  rw [← hF, ← Set.range_comp']
  apply congrArg sSup
  apply congrArg Set.range
  funext j
  exact hpop (f j)

/-- The finite weighted deviation is exactly the deviation of the corresponding
quantized row tuple, with the same finite target subset. -/
theorem restrictedDeviation_eq_finiteRowDeviation {N L J m : ℕ}
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ComplexVector N)
    (decoder : Fin L → ComplexVector N) (f : Fin J → ComplexVector N)
    (q : Fin L → ℝ) (rows : Fin m → Ω' → Fin L) (ω : Ω')
    (F : Set (ComplexVector N)) (hF : Set.range f = F)
    (hpop : ∀ g, populationEnergy μ Y g =
      weightedMean q (fun a => rowEnergy g (decoder a))) :
    restrictedDeviation μ Y (fun i ω => decoder (rows i ω)) F ω =
      finiteRowDeviation decoder f q (fun i => rows i ω) := by
  unfold restrictedDeviation finiteRowDeviation
  rw [← hF, ← Set.range_comp']
  apply congrArg sSup
  apply congrArg Set.range
  funext j
  rw [hpop]
  rfl

/-- Pushforward integration also applies to an almost everywhere measurable
quantizer, as required when the original row is only AE measurable. -/
theorem quantized_populationEnergy_eq_weightedMean {N : ℕ} {K ε : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ)
    (Q : BoundedRowQuantizer N K ε) (f : ComplexVector N) :
    populationEnergy μ (fun ω => Q.decoded (X ω)) f =
      weightedMean (FiniteWeightedLaw.singletonWeight (μ.map (fun ω => Q.quantize (X ω))))
        (fun a => rowEnergy f (Q.decoder a)) := by
  have hQ := Q.aemeasurable_quantized μ X hX
  letI : IsProbabilityMeasure (μ.map (fun ω => Q.quantize (X ω))) :=
    Measure.isProbabilityMeasure_map hQ
  unfold populationEnergy BoundedRowQuantizer.decoded
  change (∫ ω, (fun a => rowEnergy f (Q.decoder a)) (Q.quantize (X ω)) ∂μ) = _
  have hi := integral_map (f := fun a => rowEnergy f (Q.decoder a)) hQ
    (Integrable.of_finite.aestronglyMeasurable)
  rw [← hi, FiniteWeightedLaw.integral_eq_weightedMean]

/-- Population suprema increase when the target class is enlarged. -/
theorem populationEnergySup_mono_target {N : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ)
    (F T : Set (ComplexVector N)) (hFT : F ⊆ T)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    populationEnergySup μ X F ≤ populationEnergySup μ X T := by
  by_cases hF : F.Nonempty
  · apply csSup_le (hF.image _)
    rintro _ ⟨f, hf, rfl⟩
    exact le_csSup (⟨s * K ^ 2, by
      rintro _ ⟨g, hg, rfl⟩
      exact populationEnergy_le_radius μ X hX g hs hK (hT g hg) hbound⟩)
      (Set.mem_image_of_mem (populationEnergy μ X) (hFT hf))
  · rw [Set.not_nonempty_iff_eq_empty.mp hF, populationEnergySup_empty]
    exact populationEnergySup_nonneg μ X hX T hs hK hT hbound

/-- Absorbing the two fixed finite-approximation errors requires only
positivity of the radius parameters and the original relative-error bound. -/
theorem finite_reduction_threshold_le {B δ S S' D D' : ℝ}
    (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hS : 0 ≤ S)
    (hS' : S' ≤ S + δ / 8) (hD : D ≤ D' + δ / 2)
    (hD' : D' ≤ B * δ * (1 + S')) :
    D ≤ (2 * B + 2) * (δ + δ * S) := by
  have hS'1 : 1 + S' ≤ 2 + S := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hS'1 (mul_nonneg hB hδ.le)
  have hBS : 0 ≤ B * S := mul_nonneg hB hS
  have hδBS : 0 ≤ δ * (B * S) := mul_nonneg hδ.le hBS
  have hδS : 0 ≤ δ * S := mul_nonneg hδ.le hS
  nlinarith

/-- A concentration estimate for every finite row law and finite target family
lifts to arbitrary row laws and arbitrary coefficient sets. The only change
is the universal deviation constant `2 * B + 2`; the exponential rate is
preserved, and its factor two gives the original strict success inequality. -/
theorem boundedRows_concentration_of_finite {N m : ℕ} (hm : 0 < m)
    {s K δ B : ℝ} (hs : 0 < s) (hK : 0 < K) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hB : 0 ≤ B)
    (hfinite : FiniteRowConcentrationAt N m s K δ B)
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ComplexVector N) (rows : Fin m → Ω' → ComplexVector N)
    (hindep : iIndepFun rows ν) (hcopy : ∀ i, IdentDistrib (rows i) X ν μ)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K)
    (T : Set (ComplexVector N))
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s) :
    1 - 2 * Real.exp (-(δ ^ 2 * (m : ℝ) / (s * K ^ 2))) <
      (ν {ω | restrictedDeviation μ X rows T ω ≤
        (2 * B + 2) * (δ + δ * populationEnergySup μ X T)}).toReal := by
  classical
  have hX : AEMeasurable X μ := (hcopy ⟨0, hm⟩).aemeasurable_snd
  have hS0 := populationEnergySup_nonneg μ X hX T hs.le hK.le hT hbound
  by_cases hTne : T.Nonempty
  · let εrow := δ / (16 * s * K)
    let εtarget := δ / (16 * K ^ 2 * Real.sqrt s)
    have hεrow : 0 < εrow := by dsimp [εrow]; positivity
    have hεtarget : 0 < εtarget := by dsimp [εtarget]; positivity
    obtain ⟨Q⟩ := boundedRowQuantizer_exists N hK.le hεrow
    obtain ⟨F, hFT, hFfinite, happrox⟩ :=
      coefficientClass_finite_approximation T hs.le hεtarget hT
    obtain ⟨f₀, hf₀⟩ := hTne
    obtain ⟨g₀, hg₀, _⟩ := happrox f₀ hf₀
    letI : Fintype F := hFfinite.fintype
    letI : Nonempty F := ⟨⟨g₀, hg₀⟩⟩
    let J := Fintype.card F
    have hJ : 0 < J := Fintype.card_pos
    let enumerate : Fin J ≃ F := (Fintype.equivFin F).symm
    let f : Fin J → ComplexVector N := fun j => (enumerate j).val
    have hrange : Set.range f = F := by
      ext g
      constructor
      · rintro ⟨j, rfl⟩
        exact (enumerate j).property
      · intro hg
        refine ⟨enumerate.symm ⟨g, hg⟩, ?_⟩
        exact congrArg Subtype.val (enumerate.apply_symm_apply ⟨g, hg⟩)
    have hf : ∀ j, coefficientL1Norm (f j) ≤ Real.sqrt s :=
      fun j => hT (f j) (hFT (enumerate j).property)
    have hTF : ∀ g ∈ F, coefficientL1Norm g ≤ Real.sqrt s :=
      fun g hg => hT g (hFT hg)
    let Y : Ω → ComplexVector N := fun ω => Q.decoded (X ω)
    let other : Fin m → Ω' → ComplexVector N := fun i ω => Q.decoded (rows i ω)
    let quantized : Fin m → Ω' → Fin Q.alphabetSize :=
      fun i ω => Q.quantize (rows i ω)
    let law := μ.map (fun ω => Q.quantize (X ω))
    have hA := Q.aemeasurable_quantized μ X hX
    letI : IsProbabilityMeasure law := Measure.isProbabilityMeasure_map hA
    let q := FiniteWeightedLaw.singletonWeight law
    have hq : ∀ a, 0 ≤ q a := FiniteWeightedLaw.singletonWeight_nonneg law
    have hqs : ∑ a, q a = 1 := FiniteWeightedLaw.singletonWeight_sum law
    have hY : AEMeasurable Y μ := Q.aemeasurable_decoded μ X hX
    have hYbound : ∀ j, ∀ᵐ ω ∂μ, ‖Y ω j‖ ≤ K :=
      fun j => Filter.Eventually.of_forall (fun ω => Q.decoded_coordinate_norm_le (X ω) j)
    have hXY : ∀ᵐ ω ∂μ, ‖X ω - Y ω‖ ≤ εrow :=
      Q.ae_decoded_error_le μ X hK.le hbound
    have hpop (g : ComplexVector N) : populationEnergy μ Y g =
        weightedMean q (fun a => rowEnergy g (Q.decoder a)) :=
      quantized_populationEnergy_eq_weightedMean μ X hX Q g
    have hSfinite : populationEnergySup μ Y F = finiteRowPopulationSup Q.decoder f q :=
      populationEnergySup_eq_finiteRowPopulationSup μ Y Q.decoder f q F hrange hpop
    have hDfinite (ω : Ω') : restrictedDeviation μ Y other F ω =
        finiteRowDeviation Q.decoder f q (fun i => quantized i ω) :=
      restrictedDeviation_eq_finiteRowDeviation μ Y Q.decoder f q quantized ω F hrange hpop
    have hrowerr : 4 * s * K * εrow = δ / 4 := by
      dsimp [εrow]
      field_simp
      ring
    have hpoperr : 2 * s * K * εrow = δ / 8 := by
      dsimp [εrow]
      field_simp
      ring
    have htargeterr : 4 * K ^ 2 * Real.sqrt s * εtarget = δ / 4 := by
      dsimp [εtarget]
      field_simp
      ring
    have hSupDiff := populationEnergySup_row_sub_le μ X Y hX hY F
      hs.le hK.le hεrow.le hTF hbound hYbound hXY
    have hSupMono := populationEnergySup_mono_target μ X hX F T hFT hs.le hK.le hT hbound
    have hSdec : populationEnergySup μ Y F ≤ populationEnergySup μ X T + δ / 8 := by
      rw [hpoperr] at hSupDiff
      have h := (abs_le.mp hSupDiff).1
      linarith
    have hrowsbound : ∀ᵐ ω ∂ν, ∀ i j, ‖rows i ω j‖ ≤ K := by
      apply ae_all_iff.mpr
      intro i
      exact identDistrib_ae_all_coordinates_bound μ ν X (rows i) (hcopy i) hbound
    have hrowsapprox : ∀ᵐ ω ∂ν, ∀ i, ‖rows i ω - other i ω‖ ≤ εrow :=
      Q.ae_sampled_decoded_error_le μ ν X rows hcopy hK.le hbound
    have hDdec : ∀ᵐ ω ∂ν, restrictedDeviation μ X rows T ω ≤
        restrictedDeviation μ Y other F ω + δ / 2 := by
      filter_upwards [hrowsbound, hrowsapprox] with ω hωbound hωapprox
      have htarget := restrictedDeviation_le_finite_approximation μ X hX rows hm ω
        T F hFT hFfinite hs.le hK.le hεtarget.le hT hbound hωbound happrox
      have hrow := restrictedDeviation_row_sub_le μ X Y hX hY rows other hm ω F
        hs.le hK.le hεrow.le hTF hbound hYbound hXY hωbound
        (fun i j => Q.decoded_coordinate_norm_le (rows i ω) j) hωapprox
      rw [htargeterr] at htarget
      rw [hrowerr] at hrow
      have h := (abs_le.mp hrow).2
      linarith
    let failure : (Fin m → Fin Q.alphabetSize) → Prop := fun x =>
      B * δ * (1 + finiteRowPopulationSup Q.decoder f q) < finiteRowDeviation Q.decoder f q x
    have hfailure := hfinite Q.alphabetSize J Q.alphabet_pos hJ Q.decoder f q
      (fun a j => (norm_le_pi_norm (Q.decoder a) j).trans (Q.decoder_bound a)) hf hq hqs
    have hquantIndep : iIndepFun quantized ν := Q.independent_quantized ν rows hindep
    have hquantCopy : ∀ i, IdentDistrib (quantized i) (fun ω => Q.quantize (X ω)) ν μ :=
      fun i => Q.identDistrib_quantized μ ν X (rows i) (hcopy i)
    have hlaw := IIDJointLaw.iid_tuple_event_measure_eq μ ν
      (fun ω => Q.quantize (X ω)) quantized hquantIndep hquantCopy
      {x | failure x} ((Set.toFinite _).measurableSet)
    simp only [Set.mem_setOf_eq] at hlaw
    have hfailProb : (ν {ω | failure (fun i => quantized i ω)}).toReal ≤
        Real.exp (-(δ ^ 2 * (m : ℝ) / (s * K ^ 2))) := by
      rw [hlaw, FiniteWeightedLaw.product_event_probability_eq_weightedProbability]
      exact hfailure
    let threshold := (2 * B + 2) * (δ + δ * populationEnergySup μ X T)
    let bad := {ω | threshold < restrictedDeviation μ X rows T ω}
    have hbad_le : ν bad ≤ ν {ω | failure (fun i => quantized i ω)} := by
      apply measure_mono_ae
      filter_upwards [hDdec] with ω hω
      intro hbad
      by_contra hgood
      have hfinitegood : finiteRowDeviation Q.decoder f q (fun i => quantized i ω) ≤
          B * δ * (1 + finiteRowPopulationSup Q.decoder f q) :=
        le_of_not_gt hgood
      rw [← hDfinite ω, ← hSfinite] at hfinitegood
      have hfull := finite_reduction_threshold_le hB hδ hδ1 hS0 hSdec hω hfinitegood
      exact (not_lt_of_ge hfull) hbad
    have hbadProb : (ν bad).toReal ≤ Real.exp (-(δ ^ 2 * (m : ℝ) / (s * K ^ 2))) :=
      (ENNReal.toReal_mono (measure_ne_top ν _) hbad_le).trans hfailProb
    have hdev := restrictedDeviation_aemeasurable μ ν X hX hm rows
      (fun i => (hcopy i).aemeasurable_fst) T hs.le hK.le hT hbound
    have hbadMeas : NullMeasurableSet bad ν :=
      nullMeasurableSet_lt aemeasurable_const hdev
    have hcompl := probReal_compl_eq_one_sub₀ hbadMeas
    have hgood : (ν {ω | restrictedDeviation μ X rows T ω ≤ threshold}).toReal =
        1 - (ν bad).toReal := by
      simpa only [Measure.real, bad, Set.compl_setOf, not_lt] using hcompl
    change 1 - 2 * Real.exp _ < (ν {ω | restrictedDeviation μ X rows T ω ≤ threshold}).toReal
    rw [hgood]
    have he := Real.exp_pos (-(δ ^ 2 * (m : ℝ) / (s * K ^ 2)))
    linarith
  · have hTempty := Set.not_nonempty_iff_eq_empty.mp hTne
    rw [hTempty, populationEnergySup_empty]
    simp only [restrictedDeviation_empty, mul_zero, add_zero]
    have hthreshold : 0 ≤ (2 * B + 2) * δ := by positivity
    simp only [hthreshold, Set.setOf_true, measure_univ, ENNReal.toReal_one]
    have he := Real.exp_pos (-(δ ^ 2 * (m : ℝ) / (s * K ^ 2)))
    linarith

end LeanNumDetect.BoundedRieszConcentration
