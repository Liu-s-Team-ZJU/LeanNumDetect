import General.Probability.BoundedRowModel
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
Elementary deterministic and measure-theoretic estimates for arbitrary bounded
row distributions. In particular, all suprema used by bounded-row concentration
are finite under its original ℓ¹-ball hypotheses. No iid or concentration theorem
is assumed in this module.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open MeasureTheory ProbabilityTheory

universe u v

namespace LeanNumDetect.BoundedRieszConcentration

theorem coefficientL1Norm_nonneg {N : ℕ} (f : ComplexVector N) :
    0 ≤ coefficientL1Norm f := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem continuous_coefficientL1Norm {N : ℕ} :
    Continuous (coefficientL1Norm : ComplexVector N → ℝ) := by
  unfold coefficientL1Norm
  fun_prop

theorem continuous_rowPairing {N : ℕ} :
    Continuous (fun p : ComplexVector N × ComplexVector N => rowPairing p.1 p.2) := by
  unfold rowPairing
  fun_prop

theorem continuous_rowEnergy {N : ℕ} :
    Continuous (fun p : ComplexVector N × ComplexVector N => rowEnergy p.1 p.2) := by
  unfold rowEnergy
  exact continuous_rowPairing.norm.pow 2

theorem rowPairing_sub_left {N : ℕ} (f g x : ComplexVector N) :
    rowPairing (f - g) x = rowPairing f x - rowPairing g x := by
  simp [rowPairing, sub_mul, Finset.sum_sub_distrib]

theorem rowPairing_ofReal_smul {N : ℕ} (r : ℝ) (f x : ComplexVector N) :
    rowPairing ((r : ℂ) • f) x = (r : ℂ) * rowPairing f x := by
  simp [rowPairing, Finset.mul_sum, mul_assoc]

theorem rowPairing_sum_left {N : ℕ} {α : Type*} [Fintype α]
    (f : α → ComplexVector N) (x : ComplexVector N) :
    rowPairing (∑ a, f a) x = ∑ a, rowPairing (f a) x := by
  simp only [rowPairing, Finset.sum_apply, star_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem rowPairing_norm_le {N : ℕ} (f x : ComplexVector N)
    {K : ℝ} (hbound : ∀ j, ‖x j‖ ≤ K) :
    ‖rowPairing f x‖ ≤ K * coefficientL1Norm f := by
  calc
    _ ≤ ∑ j, ‖star (f j) * x j‖ := norm_sum_le _ _
    _ = ∑ j, ‖f j‖ * ‖x j‖ := by simp only [norm_mul, norm_star]
    _ ≤ ∑ j, ‖f j‖ * K :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbound j) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]; rfl

/-- The pointwise envelope needed for both symmetrization and variance
concentration: squared row energy is bounded by `s K²`. -/
theorem rowEnergy_le_radius {N : ℕ} (f x : ComplexVector N)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hf : coefficientL1Norm f ≤ Real.sqrt s) (hbound : ∀ j, ‖x j‖ ≤ K) :
    rowEnergy f x ≤ s * K ^ 2 := by
  have hnorm := (rowPairing_norm_le f x hbound).trans
    (mul_le_mul_of_nonneg_left hf hK)
  unfold rowEnergy
  calc
    _ ≤ (K * Real.sqrt s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hs]; ring

/-- The fourth-moment envelope keeps the population-energy factor, rather
than replacing it by the coarser square of the envelope. -/
theorem rowEnergy_sq_le_radius_mul {N : ℕ} (f x : ComplexVector N)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hf : coefficientL1Norm f ≤ Real.sqrt s) (hbound : ∀ j, ‖x j‖ ≤ K) :
    rowEnergy f x ^ 2 ≤ (s * K ^ 2) * rowEnergy f x := by
  simpa only [pow_two, mul_comm] using
    mul_le_mul_of_nonneg_right (rowEnergy_le_radius f x hs hK hf hbound)
      (rowEnergy_nonneg f x)

theorem ae_all_coordinates_bound {N : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ComplexVector N) {K : ℝ}
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    ∀ᵐ ω ∂μ, ∀ j, ‖X ω j‖ ≤ K := ae_all_iff.mpr hbound

theorem rowEnergy_aestronglyMeasurable {N : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ComplexVector N)
    (hX : AEMeasurable X μ) (f : ComplexVector N) :
    AEStronglyMeasurable (fun ω => rowEnergy f (X ω)) μ := by
  have hc : Continuous (fun x : ComplexVector N => rowEnergy f x) := by
    unfold rowEnergy rowPairing
    fun_prop
  exact (hc.measurable.comp_aemeasurable hX).aestronglyMeasurable

theorem rowEnergy_integrable {N : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ) (f : ComplexVector N)
    {K : ℝ} (_hK : 0 ≤ K) (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    Integrable (fun ω => rowEnergy f (X ω)) μ := by
  apply Integrable.of_bound (rowEnergy_aestronglyMeasurable μ X hX f)
    ((K * coefficientL1Norm f) ^ 2)
  filter_upwards [ae_all_coordinates_bound μ X hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (rowEnergy_nonneg _ _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (rowPairing_norm_le f (X ω) hω) 2

theorem populationEnergy_nonneg {N : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ComplexVector N) (f : ComplexVector N) :
    0 ≤ populationEnergy μ X f := integral_nonneg fun _ => rowEnergy_nonneg _ _

theorem populationEnergy_le_radius {N : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ) (f : ComplexVector N)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hf : coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    populationEnergy μ X f ≤ s * K ^ 2 := by
  unfold populationEnergy
  calc
    _ ≤ ∫ _ω, s * K ^ 2 ∂μ := integral_mono_ae
      (rowEnergy_integrable μ X hX f hK hbound) (integrable_const _) (by
        filter_upwards [ae_all_coordinates_bound μ X hbound] with ω hω
        exact rowEnergy_le_radius f (X ω) hs hK hf hω)
    _ = _ := by simp

theorem populationEnergySup_le_radius {N : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ) (T : Set (ComplexVector N))
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    populationEnergySup μ X T ≤ s * K ^ 2 := by
  by_cases hne : T.Nonempty
  · apply csSup_le (hne.image _)
    rintro _ ⟨f, hf, rfl⟩
    exact populationEnergy_le_radius μ X hX f hs hK (hT f hf) hbound
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, populationEnergySup_empty]
    positivity

theorem empiricalEnergy_nonneg {N m : ℕ} {Ω : Type u}
    (rows : Fin m → Ω → ComplexVector N) (ω : Ω) (f : ComplexVector N) :
    0 ≤ empiricalEnergy rows ω f := by
  unfold empiricalEnergy
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => rowEnergy_nonneg _ _)

theorem empiricalEnergy_le_radius {N m : ℕ} {Ω : Type u} (hm : 0 < m)
    (rows : Fin m → Ω → ComplexVector N) (ω : Ω) (f : ComplexVector N)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hf : coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ i j, ‖rows i ω j‖ ≤ K) :
    empiricalEnergy rows ω f ≤ s * K ^ 2 := by
  unfold empiricalEnergy
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ _i : Fin m, s * K ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        rowEnergy_le_radius f (rows i ω) hs hK hf (hbound i)) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_mul]

theorem rowEnergy_square_integrable {N : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ) (f : ComplexVector N)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hf : coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    Integrable (fun ω => rowEnergy f (X ω) ^ 2) μ := by
  apply Integrable.of_bound (rowEnergy_aestronglyMeasurable μ X hX f |>.pow 2)
    ((s * K ^ 2) ^ 2)
  filter_upwards [ae_all_coordinates_bound μ X hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (rowEnergy_nonneg _ _)
    (rowEnergy_le_radius f (X ω) hs hK hf hω) 2

/-- The variance proxy in BDJR's empirical-process reduction (their equation
(4.3)) follows from the original coordinate and ℓ¹ bounds alone. -/
theorem population_rowEnergy_square_le {N : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ) (f : ComplexVector N)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hf : coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    (∫ ω, rowEnergy f (X ω) ^ 2 ∂μ) ≤
      (s * K ^ 2) * populationEnergy μ X f := by
  calc
    _ ≤ ∫ ω, (s * K ^ 2) * rowEnergy f (X ω) ∂μ := integral_mono_ae
      (rowEnergy_square_integrable μ X hX f hs hK hf hbound)
      ((rowEnergy_integrable μ X hX f hK hbound).const_mul _) (by
        filter_upwards [ae_all_coordinates_bound μ X hbound] with ω hω
        exact rowEnergy_sq_le_radius_mul f (X ω) hs hK hf hω)
    _ = _ := by rw [integral_const_mul]; rfl

theorem populationEnergySup_nonneg {N : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ) (T : Set (ComplexVector N))
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    0 ≤ populationEnergySup μ X T := by
  by_cases hne : T.Nonempty
  · obtain ⟨f, hf⟩ := hne
    apply (populationEnergy_nonneg μ X f).trans
    exact le_csSup (⟨s * K ^ 2, by
      rintro _ ⟨g, hg, rfl⟩
      exact populationEnergy_le_radius μ X hX g hs hK (hT g hg) hbound⟩)
      ⟨f, hf, rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, populationEnergySup_empty]

/-- An entire infinite target class has a bounded deviation on every row
outcome satisfying the common coordinate envelope. -/
theorem restrictedDeviation_le_radius {N m : ℕ} {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ)
    (rows : Fin m → Ω' → ComplexVector N) (hm : 0 < m)
    (T : Set (ComplexVector N)) (ω : Ω') {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hXbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K)
    (hrows : ∀ i j, ‖rows i ω j‖ ≤ K) :
    restrictedDeviation μ X rows T ω ≤ s * K ^ 2 := by
  by_cases hne : T.Nonempty
  · apply csSup_le (hne.image _)
    rintro _ ⟨f, hf, rfl⟩
    apply abs_le.mpr
    have hpop := populationEnergy_le_radius μ X hX f hs hK (hT f hf) hXbound
    have hemp := empiricalEnergy_le_radius hm rows ω f hs hK (hT f hf) hrows
    have hpop0 := populationEnergy_nonneg μ X f
    have hemp0 := empiricalEnergy_nonneg rows ω f
    constructor <;> linarith
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, restrictedDeviation_empty]
    positivity

/-- Copying the row distribution preserves its common almost-everywhere
coordinate envelope, with no condition on the source probability spaces. -/
theorem identDistrib_ae_all_coordinates_bound {N : ℕ}
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → ComplexVector N)
    (Y : Ω' → ComplexVector N) (hcopy : IdentDistrib Y X ν μ) {K : ℝ}
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    ∀ᵐ ω ∂ν, ∀ j, ‖Y ω j‖ ≤ K := by
  apply ae_all_iff.mpr
  intro j
  exact hcopy.symm.ae_snd (isClosed_le (continuous_apply j |>.norm) continuous_const |>.measurableSet)
    (hbound j)

end LeanNumDetect.BoundedRieszConcentration
