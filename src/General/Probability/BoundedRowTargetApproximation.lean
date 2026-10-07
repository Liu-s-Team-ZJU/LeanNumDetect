import General.Probability.BoundedRowContinuity
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Finite approximation of arbitrary bounded coefficient classes

Uniform coefficient perturbation bounds apply to both empirical and
population energies. Compactness of the finite-dimensional coefficient ball
then supplies finite target subsets. No probabilistic concentration estimate
or regularity of the original target set is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe u v
namespace LeanNumDetect.BoundedRieszConcentration

theorem coefficientL1Norm_le_card_mul_norm {N : ℕ} (f : ComplexVector N) :
    coefficientL1Norm f ≤ (N : ℝ) * ‖f‖ := by
  calc
    _ ≤ ∑ _j : Fin N, ‖f‖ := Finset.sum_le_sum fun j _ => norm_le_pi_norm f j
    _ = _ := by simp

theorem norm_le_coefficientL1Norm {N : ℕ} (f : ComplexVector N) :
    ‖f‖ ≤ coefficientL1Norm f := by
  apply (pi_norm_le_iff_of_nonneg (coefficientL1Norm_nonneg f)).mpr
  intro j
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

/-- Uniform row-energy perturbation in the coefficient ℓ¹ metric. -/
theorem rowEnergy_coefficient_sub_le {N : ℕ} (f g x : ComplexVector N)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hf : coefficientL1Norm f ≤ Real.sqrt s)
    (hg : coefficientL1Norm g ≤ Real.sqrt s) (hrow : ∀ j, ‖x j‖ ≤ K) :
    |rowEnergy f x - rowEnergy g x| ≤
      2 * K ^ 2 * Real.sqrt s * coefficientL1Norm (f - g) := by
  have ha := (rowPairing_norm_le f x hrow).trans
    (mul_le_mul_of_nonneg_left hf hK)
  have hb := (rowPairing_norm_le g x hrow).trans
    (mul_le_mul_of_nonneg_left hg hK)
  have hd := rowPairing_norm_le (f - g) x hrow
  rw [rowPairing_sub_left] at hd
  have heq : |rowEnergy f x - rowEnergy g x| =
      |‖rowPairing f x‖ - ‖rowPairing g x‖| *
        (‖rowPairing f x‖ + ‖rowPairing g x‖) := by
    unfold rowEnergy
    rw [show ‖rowPairing f x‖ ^ 2 - ‖rowPairing g x‖ ^ 2 =
      (‖rowPairing f x‖ - ‖rowPairing g x‖) *
        (‖rowPairing f x‖ + ‖rowPairing g x‖) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [heq]
  calc
    _ ≤ ‖rowPairing f x - rowPairing g x‖ *
        (‖rowPairing f x‖ + ‖rowPairing g x‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (by positivity)
    _ ≤ (K * coefficientL1Norm (f - g)) * (K * Real.sqrt s + K * Real.sqrt s) :=
      mul_le_mul hd (add_le_add ha hb) (by positivity)
        (mul_nonneg hK (coefficientL1Norm_nonneg _))
    _ = _ := by ring

theorem empiricalEnergy_coefficient_sub_le {N m : ℕ} {Ω : Type*} (hm : 0 < m)
    (rows : Fin m → Ω → ComplexVector N) (ω : Ω) (f g : ComplexVector N)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hf : coefficientL1Norm f ≤ Real.sqrt s)
    (hg : coefficientL1Norm g ≤ Real.sqrt s) (hrows : ∀ i j, ‖rows i ω j‖ ≤ K) :
    |empiricalEnergy rows ω f - empiricalEnergy rows ω g| ≤
      2 * K ^ 2 * Real.sqrt s * coefficientL1Norm (f - g) := by
  unfold empiricalEnergy
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (m : ℝ)⁻¹)]
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ i, |rowEnergy f (rows i ω) - rowEnergy g (rows i ω)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (m : ℝ)⁻¹ * ∑ _i : Fin m,
        2 * K ^ 2 * Real.sqrt s * coefficientL1Norm (f - g) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        rowEnergy_coefficient_sub_le f g (rows i ω) hs hK hf hg (hrows i)) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_mul]

theorem populationEnergy_coefficient_sub_le {N : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ) (f g : ComplexVector N)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hf : coefficientL1Norm f ≤ Real.sqrt s)
    (hg : coefficientL1Norm g ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    |populationEnergy μ X f - populationEnergy μ X g| ≤
      2 * K ^ 2 * Real.sqrt s * coefficientL1Norm (f - g) := by
  have hfi := rowEnergy_integrable μ X hX f hK hbound
  have hgi := rowEnergy_integrable μ X hX g hK hbound
  unfold populationEnergy
  rw [← integral_sub hfi hgi, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ ω, ‖rowEnergy f (X ω) - rowEnergy g (X ω)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _ω, 2 * K ^ 2 * Real.sqrt s * coefficientL1Norm (f - g) ∂μ :=
      integral_mono_ae ((hfi.sub hgi).norm) (integrable_const _) (by
        filter_upwards [ae_all_coordinates_bound μ X hbound] with ω hω
        simpa only [Real.norm_eq_abs] using
          rowEnergy_coefficient_sub_le f g (X ω) hs hK hf hg hω)
    _ = _ := by simp

/-- Finite subsets of the actual target, rather than larger coefficient
balls, approximate every point of an arbitrary ℓ¹-bounded class. -/
theorem coefficientClass_finite_approximation {N : ℕ} (T : Set (ComplexVector N))
    {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s) :
    ∃ F : Set (ComplexVector N), F ⊆ T ∧ F.Finite ∧
      ∀ f ∈ T, ∃ g ∈ F, coefficientL1Norm (f - g) ≤ ε := by
  have hsub : T ⊆ Metric.closedBall (0 : ComplexVector N) (Real.sqrt s) := by
    intro f hf
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_coefficientL1Norm f).trans (hT f hf)
  have hcl := closure_minimal hsub Metric.isClosed_closedBall
  have hc := (isCompact_closedBall (0 : ComplexVector N) (Real.sqrt s)).of_isClosed_subset
    isClosed_closure hcl
  have hε' : 0 < ε / ((N : ℝ) + 1) := by positivity
  obtain ⟨F, hFT, hF, hcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hc hε'
  refine ⟨F, hFT, hF, ?_⟩
  intro f hf
  obtain ⟨g, hg, hfg⟩ := Set.mem_iUnion₂.mp (hcover hf)
  refine ⟨g, hg, ?_⟩
  have hn : ‖f - g‖ < ε / ((N : ℝ) + 1) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hfg
  calc
    _ ≤ (N : ℝ) * ‖f - g‖ := coefficientL1Norm_le_card_mul_norm _
    _ ≤ (N : ℝ) * (ε / ((N : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hn.le (Nat.cast_nonneg N)
    _ ≤ ε := by
      have hden : 0 < (N : ℝ) + 1 := by positivity
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

/-- A finite target approximation controls the population covariance supremum. -/
theorem populationEnergySup_le_finite_approximation {N : ℕ} {Ω : Type u}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ)
    (T F : Set (ComplexVector N)) (hFT : F ⊆ T) (hF : F.Finite)
    {s K ε : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K)
    (happrox : ∀ f ∈ T, ∃ g ∈ F, coefficientL1Norm (f - g) ≤ ε) :
    populationEnergySup μ X T ≤ populationEnergySup μ X F + 2 * K ^ 2 * Real.sqrt s * ε := by
  by_cases hne : T.Nonempty
  · apply csSup_le (hne.image _)
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg, hfg⟩ := happrox f hf
    have hpop := populationEnergy_coefficient_sub_le μ X hX f g hs hK
      (hT f hf) (hT g (hFT hg)) hbound
    have he := (abs_le.mp hpop).2
    have hl := le_csSup (hF.image _).bddAbove (Set.mem_image_of_mem (populationEnergy μ X) hg)
    change populationEnergy μ X g ≤ populationEnergySup μ X F at hl
    have he' := mul_le_mul_of_nonneg_left hfg
      (show 0 ≤ 2 * K ^ 2 * Real.sqrt s by positivity)
    linarith
  · have hT0 := Set.not_nonempty_iff_eq_empty.mp hne
    have hF0 : F = ∅ := Set.Subset.antisymm (by simpa [hT0] using hFT) (Set.empty_subset _)
    simp only [hT0, hF0, populationEnergySup_empty]
    positivity

/-- The same finite approximation controls the full empirical deviation. -/
theorem restrictedDeviation_le_finite_approximation {N m : ℕ} {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ)
    (rows : Fin m → Ω' → ComplexVector N) (hm : 0 < m) (ω : Ω')
    (T F : Set (ComplexVector N)) (hFT : F ⊆ T) (hF : F.Finite)
    {s K ε : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K)
    (hrows : ∀ i j, ‖rows i ω j‖ ≤ K)
    (happrox : ∀ f ∈ T, ∃ g ∈ F, coefficientL1Norm (f - g) ≤ ε) :
    restrictedDeviation μ X rows T ω ≤ restrictedDeviation μ X rows F ω +
      4 * K ^ 2 * Real.sqrt s * ε := by
  by_cases hne : T.Nonempty
  · apply csSup_le (hne.image _)
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg, hfg⟩ := happrox f hf
    have hpf := hT f hf
    have hpg := hT g (hFT hg)
    have he := empiricalEnergy_coefficient_sub_le hm rows ω f g hs hK hpf hpg hrows
    have hp := populationEnergy_coefficient_sub_le μ X hX f g hs hK hpf hpg hbound
    have hc := mul_le_mul_of_nonneg_left hfg
      (show 0 ≤ 2 * K ^ 2 * Real.sqrt s by positivity)
    have hl := le_csSup (hF.image _).bddAbove (Set.mem_image_of_mem
      (fun f => |empiricalEnergy rows ω f - populationEnergy μ X f|) hg)
    change |empiricalEnergy rows ω g - populationEnergy μ X g| ≤
      restrictedDeviation μ X rows F ω at hl
    have ht := norm_le_norm_add_norm_sub
      (empiricalEnergy rows ω g - populationEnergy μ X g)
      (empiricalEnergy rows ω f - populationEnergy μ X f)
    simp only [Real.norm_eq_abs] at ht
    have hd : |empiricalEnergy rows ω g - populationEnergy μ X g -
        (empiricalEnergy rows ω f - populationEnergy μ X f)| ≤
        |empiricalEnergy rows ω f - empiricalEnergy rows ω g| +
        |populationEnergy μ X f - populationEnergy μ X g| := by
      rw [show empiricalEnergy rows ω g - populationEnergy μ X g -
        (empiricalEnergy rows ω f - populationEnergy μ X f) =
        (empiricalEnergy rows ω g - empiricalEnergy rows ω f) +
          (populationEnergy μ X f - populationEnergy μ X g) by ring]
      simpa only [abs_sub_comm] using abs_add_le
        (empiricalEnergy rows ω g - empiricalEnergy rows ω f)
        (populationEnergy μ X f - populationEnergy μ X g)
    linarith
  · have hT0 := Set.not_nonempty_iff_eq_empty.mp hne
    have hF0 : F = ∅ := Set.Subset.antisymm (by simpa [hT0] using hFT) (Set.empty_subset _)
    simp only [hT0, hF0, restrictedDeviation_empty]
    positivity

end LeanNumDetect.BoundedRieszConcentration
