import General.Probability.BoundedRowEstimates

/-!
# Continuity of arbitrary-class bounded-row deviation

The target class need not be finite, closed, or measurable. Its coordinate
ℓ¹ envelope gives uniform continuity estimates for the supremum as a
function of the finite tuple of rows. Consequently the sampled deviation
is almost everywhere measurable whenever the rows are.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
open MeasureTheory ProbabilityTheory

universe u
namespace LeanNumDetect.BoundedRieszConcentration

/-- Uniform pointwise perturbations control suprema over an arbitrary set. -/
theorem abs_sup_image_sub_le {ι : Type*} (T : Set ι) (f g : ι → ℝ)
    (hf : BddAbove (f '' T)) (hg : BddAbove (g '' T)) {D : ℝ} (hD : 0 ≤ D)
    (hdiff : ∀ i ∈ T, |f i - g i| ≤ D) :
    |sSup (f '' T) - sSup (g '' T)| ≤ D := by
  by_cases hne : T.Nonempty
  · apply abs_le.mpr
    have hfg : sSup (f '' T) ≤ sSup (g '' T) + D := by
      apply csSup_le (hne.image _)
      rintro _ ⟨i, hi, rfl⟩
      have hgi := le_csSup hg (Set.mem_image_of_mem g hi)
      have hd := (abs_le.mp (hdiff i hi)).2
      linarith
    have hgf : sSup (g '' T) ≤ sSup (f '' T) + D := by
      apply csSup_le (hne.image _)
      rintro _ ⟨i, hi, rfl⟩
      have hfi := le_csSup hf (Set.mem_image_of_mem f hi)
      have hd := (abs_le.mp (hdiff i hi)).1
      linarith
    constructor <;> linarith
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simpa using hD

theorem rowPairing_sub_right {N : ℕ} (f x y : ComplexVector N) :
    rowPairing f (x - y) = rowPairing f x - rowPairing f y := by
  simp [rowPairing, mul_sub, Finset.sum_sub_distrib]

/-- A dimension-free perturbation estimate for a single row energy. -/
theorem rowEnergy_sub_le {N : ℕ} (f x y : ComplexVector N) {s : ℝ}
    (hs : 0 ≤ s) (hf : coefficientL1Norm f ≤ Real.sqrt s) :
    |rowEnergy f x - rowEnergy f y| ≤
      s * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have hx := (rowPairing_norm_le f x (fun j => norm_le_pi_norm x j)).trans
    (mul_le_mul_of_nonneg_left hf (norm_nonneg x))
  have hy := (rowPairing_norm_le f y (fun j => norm_le_pi_norm y j)).trans
    (mul_le_mul_of_nonneg_left hf (norm_nonneg y))
  have hd := (rowPairing_norm_le f (x - y)
    (fun j => norm_le_pi_norm (x - y) j)).trans
    (mul_le_mul_of_nonneg_left hf (norm_nonneg (x - y)))
  rw [rowPairing_sub_right] at hd
  have heq : |rowEnergy f x - rowEnergy f y| =
      |‖rowPairing f x‖ - ‖rowPairing f y‖| *
        (‖rowPairing f x‖ + ‖rowPairing f y‖) := by
    unfold rowEnergy
    rw [show ‖rowPairing f x‖ ^ 2 - ‖rowPairing f y‖ ^ 2 =
      (‖rowPairing f x‖ - ‖rowPairing f y‖) *
        (‖rowPairing f x‖ + ‖rowPairing f y‖) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [heq]
  calc
    _ ≤ ‖rowPairing f x - rowPairing f y‖ *
        (‖rowPairing f x‖ + ‖rowPairing f y‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (by positivity)
    _ ≤ (‖x - y‖ * Real.sqrt s) *
        (‖x‖ * Real.sqrt s + ‖y‖ * Real.sqrt s) :=
      mul_le_mul hd (add_le_add hx hy) (by positivity) (by positivity)
    _ = ‖x - y‖ * (‖x‖ + ‖y‖) * (Real.sqrt s)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt hs]; ring

/-- The same estimate for the average of a finite tuple of rows. -/
theorem empiricalEnergy_sub_le {N m : ℕ} (hm : 0 < m)
    (x y : Fin m → ComplexVector N) (f : ComplexVector N) {s : ℝ}
    (hs : 0 ≤ s) (hf : coefficientL1Norm f ≤ Real.sqrt s) :
    |empiricalEnergy (fun i z => z i) x f -
        empiricalEnergy (fun i z => z i) y f| ≤
      s * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have hrow (i : Fin m) : |rowEnergy f (x i) - rowEnergy f (y i)| ≤
      s * (‖x‖ + ‖y‖) * ‖x - y‖ := by
    exact (rowEnergy_sub_le f (x i) (y i) hs hf).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left
        (add_le_add (norm_le_pi_norm x i) (norm_le_pi_norm y i)) hs)
        (norm_le_pi_norm (x - y) i) (by positivity) (by positivity))
  unfold empiricalEnergy
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (m : ℝ)⁻¹)]
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ i, |rowEnergy f (x i) - rowEnergy f (y i)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (m : ℝ)⁻¹ * ∑ _i : Fin m, s * (‖x‖ + ‖y‖) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hrow i) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hm.ne'), one_mul]

/-- The deviation viewed as a function on actual finite row tuples. -/
noncomputable def tupleDeviation {N m : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ComplexVector N) (T : Set (ComplexVector N))
    (x : Fin m → ComplexVector N) : ℝ :=
  restrictedDeviation μ X (fun i z => z i) T x

theorem tupleDeviation_sub_le {N m : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ) (hm : 0 < m)
    (T : Set (ComplexVector N)) {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K)
    (x y : Fin m → ComplexVector N) :
    |tupleDeviation μ X T x - tupleDeviation μ X T y| ≤
      s * (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have hb (z : Fin m → ComplexVector N) : BddAbove
      ((fun f => |empiricalEnergy (fun i z => z i) z f - populationEnergy μ X f|) '' T) := by
    refine ⟨s * ‖z‖ ^ 2 + s * K ^ 2, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    have hpop := populationEnergy_le_radius μ X hX f hs hK (hT f hf) hbound
    have hpop0 := populationEnergy_nonneg μ X f
    have hemp := empiricalEnergy_le_radius hm (fun i z => z i) z f hs
      (norm_nonneg z) (hT f hf) (fun i j =>
        (norm_le_pi_norm (z i) j).trans (norm_le_pi_norm z i))
    have hemp0 := empiricalEnergy_nonneg (fun i z => z i) z f
    apply abs_le.mpr
    constructor <;> linarith
  apply abs_sup_image_sub_le T _ _ (hb x) (hb y) (by positivity)
  intro f hf
  have h := abs_abs_sub_abs_le_abs_sub
    (empiricalEnergy (fun i z => z i) x f - populationEnergy μ X f)
    (empiricalEnergy (fun i z => z i) y f - populationEnergy μ X f)
  exact h.trans (by
    simp only [sub_sub_sub_cancel_right]
    exact empiricalEnergy_sub_le hm x y f hs (hT f hf))

/-- Continuity of the deviation requires no regularity of the target set. -/
theorem continuous_tupleDeviation {N m : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ) (hm : 0 < m)
    (T : Set (ComplexVector N)) {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    Continuous (tupleDeviation (m := m) μ X T) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun y => by simpa only [Real.norm_eq_abs] using
      tupleDeviation_sub_le μ X hX hm T hs hK hT hbound y x)
  have hc : Continuous (fun y : Fin m → ComplexVector N =>
      s * (‖y‖ + ‖x‖) * ‖y - x‖) := by fun_prop
  simpa using (hc.continuousAt (x := x)).tendsto

/-- The actual arbitrary-class sample deviation is almost everywhere
measurable on any sample probability space. -/
theorem restrictedDeviation_aemeasurable {N m : ℕ} {Ω : Type u} {Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    (X : Ω → ComplexVector N) (hX : AEMeasurable X μ) (hm : 0 < m)
    (rows : Fin m → Ω' → ComplexVector N)
    (hrows : ∀ i, AEMeasurable (rows i) ν)
    (T : Set (ComplexVector N)) {s K : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hT : ∀ f ∈ T, coefficientL1Norm f ≤ Real.sqrt s)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    AEMeasurable (restrictedDeviation μ X rows T) ν := by
  have hc := continuous_tupleDeviation μ X hX hm T hs hK hT hbound
  have hr := aemeasurable_pi_lambda (fun ω i => rows i ω) hrows
  exact hc.measurable.comp_aemeasurable hr

end LeanNumDetect.BoundedRieszConcentration
