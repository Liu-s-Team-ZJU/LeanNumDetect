import General.Probability.BoundedRowContinuity

/-! Uniform perturbation of the reference distribution and sampled rows.
The estimates hold for arbitrary coefficient sets, and consequently allow
finite quantization without imposing a finite-support hypothesis on a law. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe u v

namespace LeanNumDetect.BoundedRieszConcentration

theorem populationEnergy_row_sub_le {N : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ComplexVector N) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (f : ComplexVector N) {s K ε : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hf : coefficientL1Norm f ≤ Real.sqrt s)
    (hx : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) (hy : ∀ j, ∀ᵐ ω ∂μ, ‖Y ω j‖ ≤ K)
    (hxy : ∀ᵐ ω ∂μ, ‖X ω - Y ω‖ ≤ ε) :
    |populationEnergy μ X f - populationEnergy μ Y f| ≤ 2 * s * K * ε := by
  have hxi := rowEnergy_integrable μ X hX f hK hx
  have hyi := rowEnergy_integrable μ Y hY f hK hy
  unfold populationEnergy
  rw [← integral_sub hxi hyi, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ ω, ‖rowEnergy f (X ω) - rowEnergy f (Y ω)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _ω, 2 * s * K * ε ∂μ := integral_mono_ae
      ((hxi.sub hyi).norm) (integrable_const _) (by
        filter_upwards [ae_all_coordinates_bound μ X hx,
          ae_all_coordinates_bound μ Y hy, hxy] with ω hωx hωy hωxy
        have hnx := (pi_norm_le_iff_of_nonneg hK).mpr hωx
        have hny := (pi_norm_le_iff_of_nonneg hK).mpr hωy
        have hd := rowEnergy_sub_le f (X ω) (Y ω) hs hf
        have hb := mul_le_mul
          (mul_le_mul_of_nonneg_left (add_le_add hnx hny) hs) hωxy
          (norm_nonneg _) (by positivity : 0 ≤ s * (K + K))
        simp only [Real.norm_eq_abs]
        exact hd.trans (by convert hb using 1 <;> ring))
    _ = _ := by simp

theorem empiricalEnergy_row_sub_le {N m : ℕ} {Ω : Type v}
    (hm : 0 < m) (rows other : Fin m → Ω → ComplexVector N) (ω : Ω)
    (f : ComplexVector N) {s K ε : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hf : coefficientL1Norm f ≤ Real.sqrt s)
    (hx : ∀ i j, ‖rows i ω j‖ ≤ K) (hy : ∀ i j, ‖other i ω j‖ ≤ K)
    (hxy : ∀ i, ‖rows i ω - other i ω‖ ≤ ε) :
    |empiricalEnergy rows ω f - empiricalEnergy other ω f| ≤ 2 * s * K * ε := by
  have hnx : ‖fun i => rows i ω‖ ≤ K :=
    (pi_norm_le_iff_of_nonneg hK).mpr fun i => (pi_norm_le_iff_of_nonneg hK).mpr (hx i)
  have hny : ‖fun i => other i ω‖ ≤ K :=
    (pi_norm_le_iff_of_nonneg hK).mpr fun i => (pi_norm_le_iff_of_nonneg hK).mpr (hy i)
  have hnd : ‖(fun i => rows i ω) - (fun i => other i ω)‖ ≤ ε :=
    (pi_norm_le_iff_of_nonneg hε).mpr hxy
  have hd := empiricalEnergy_sub_le hm (fun i => rows i ω) (fun i => other i ω) f hs hf
  have hb := mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add hnx hny) hs)
    hnd (norm_nonneg _) (by positivity : 0 ≤ s * (K + K))
  exact hd.trans (by convert hb using 1 <;> ring)

theorem populationEnergySup_row_sub_le {N : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ComplexVector N) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (T : Set (ComplexVector N)) {s K ε : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hx : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) (hy : ∀ j, ∀ᵐ ω ∂μ, ‖Y ω j‖ ≤ K)
    (hxy : ∀ᵐ ω ∂μ, ‖X ω - Y ω‖ ≤ ε) :
    |populationEnergySup μ X T - populationEnergySup μ Y T| ≤ 2 * s * K * ε := by
  have hb (Z : Ω → ComplexVector N) (hZ : AEMeasurable Z μ)
      (hz : ∀ j, ∀ᵐ ω ∂μ, ‖Z ω j‖ ≤ K) : BddAbove (populationEnergy μ Z '' T) := by
    refine ⟨s * K ^ 2, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    exact populationEnergy_le_radius μ Z hZ f hs hK (hT f hf) hz
  exact abs_sup_image_sub_le T _ _ (hb X hX hx) (hb Y hY hy) (by positivity)
    (fun f hf => populationEnergy_row_sub_le μ X Y hX hY f hs hK hε (hT f hf) hx hy hxy)

theorem restrictedDeviation_row_sub_le {N m : ℕ} {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ComplexVector N) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (rows other : Fin m → Ω' → ComplexVector N) (hm : 0 < m) (ω : Ω')
    (T : Set (ComplexVector N)) {s K ε : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hx : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) (hy : ∀ j, ∀ᵐ ω ∂μ, ‖Y ω j‖ ≤ K)
    (hxy : ∀ᵐ ω ∂μ, ‖X ω - Y ω‖ ≤ ε)
    (hr : ∀ i j, ‖rows i ω j‖ ≤ K) (ho : ∀ i j, ‖other i ω j‖ ≤ K)
    (hro : ∀ i, ‖rows i ω - other i ω‖ ≤ ε) :
    |restrictedDeviation μ X rows T ω - restrictedDeviation μ Y other T ω| ≤
      4 * s * K * ε := by
  have hb (Z : Ω → ComplexVector N) (hZ : AEMeasurable Z μ)
      (hz : ∀ j, ∀ᵐ ω ∂μ, ‖Z ω j‖ ≤ K)
      (r : Fin m → Ω' → ComplexVector N) (hrr : ∀ i j, ‖r i ω j‖ ≤ K) :
      BddAbove ((fun f => |empiricalEnergy r ω f - populationEnergy μ Z f|) '' T) := by
    refine ⟨s * K ^ 2, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    have he := empiricalEnergy_le_radius hm r ω f hs hK (hT f hf) hrr
    have hp := populationEnergy_le_radius μ Z hZ f hs hK (hT f hf) hz
    have he0 := empiricalEnergy_nonneg r ω f
    have hp0 := populationEnergy_nonneg μ Z f
    apply abs_le.mpr
    constructor <;> linarith
  apply abs_sup_image_sub_le T _ _ (hb X hX hx rows hr) (hb Y hY hy other ho) (by positivity)
  intro f hf
  have h1 := abs_abs_sub_abs_le_abs_sub
    (empiricalEnergy rows ω f - populationEnergy μ X f)
    (empiricalEnergy other ω f - populationEnergy μ Y f)
  have h2 : |(empiricalEnergy rows ω f - populationEnergy μ X f) -
      (empiricalEnergy other ω f - populationEnergy μ Y f)| ≤
      |empiricalEnergy rows ω f - empiricalEnergy other ω f| +
      |populationEnergy μ X f - populationEnergy μ Y f| := by
    rw [show (empiricalEnergy rows ω f - populationEnergy μ X f) -
      (empiricalEnergy other ω f - populationEnergy μ Y f) =
      (empiricalEnergy rows ω f - empiricalEnergy other ω f) +
      (populationEnergy μ Y f - populationEnergy μ X f) by ring]
    simpa only [abs_sub_comm] using abs_add_le
      (empiricalEnergy rows ω f - empiricalEnergy other ω f)
      (populationEnergy μ Y f - populationEnergy μ X f)
  have he := empiricalEnergy_row_sub_le hm rows other ω f hs hK hε (hT f hf) hr ho hro
  have hp := populationEnergy_row_sub_le μ X Y hX hY f hs hK hε (hT f hf) hx hy hxy
  exact h1.trans (h2.trans (by linarith))

end LeanNumDetect.BoundedRieszConcentration
