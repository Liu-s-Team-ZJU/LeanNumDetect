import MultiTuran.Turan.ComplexGeometric
import MultiTuran.Turan.WeakLogDerivative
import MultiTuran.Turan.PruningModulation
import MultiTuran.Turan.GeometricBase

/-! # Actual measurable Turan bounds on the centered unit interval

Every analytic input to the geometric-mean pruning induction is discharged
here. The constants are explicit absolute real numbers. Frequencies may
repeat, coefficients may vanish, and the zero function is included.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory
open scoped BigOperators ENNReal

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- A fixed absolute weak-pruning constant. -/
def oneDimensionalPruningWeakConstant : ℝ := 1+20*logarithmicDerivativeWeakConstant

theorem oneDimensionalPruningWeakConstant_pos : 0 < oneDimensionalPruningWeakConstant := by
  unfold oneDimensionalPruningWeakConstant
  have h := logarithmicDerivativeWeakConstant_pos
  positivity

/-- One universal base for the measurable one-dimensional Turan inequality. -/
def oneDimensionalTuranConstant : ℝ :=
  Real.exp 1000000+2*Real.exp 1*oneDimensionalPruningWeakConstant

theorem oneDimensionalTuranConstant_pos : 0 < oneDimensionalTuranConstant := by
  unfold oneDimensionalTuranConstant
  have h := oneDimensionalPruningWeakConstant_pos
  positivity

private theorem finite_volume_unit_subset {E : Set ℝ}
    (hsub : E ⊆ Icc (-1/2 : ℝ) (1/2)) : volume E < ∞ :=
  lt_of_le_of_lt (measure_mono hsub) (by simp)

private theorem real_volume_unit_subset_le_one {E : Set ℝ}
    (hsub : E ⊆ Icc (-1/2 : ℝ) (1/2)) : (volume E).toReal ≤ 1 := by
  have h := ENNReal.toReal_mono (by simp : volume (Icc (-1/2 : ℝ) (1/2)) ≠ ∞)
    (measure_mono hsub)
  norm_num at h
  exact h

/-- Actual a.e. nonvanishing and logarithmic integrability on every measurable
subset of the unit interval, for any nonzero imaginary exponential sum. -/
theorem exponentialSum_unit_logRegular {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    (hzero : ExponentialSumEstimates.exponentialSum frequency c ≠ 0)
    (E : Set ℝ) (hE : MeasurableSet E) (hEsub : E ⊆ Icc (-1/2 : ℝ) (1/2)) :
    LogRegular (volume.restrict E) (ExponentialSumEstimates.exponentialSum frequency c) := by
  let σ : ℝ := ∑ j, |frequency j|
  have hσ : 0 ≤ σ := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hexponent : ∀ j, ‖imaginaryExponents frequency j‖ ≤ σ := by
    intro j
    rw [norm_imaginaryExponents]
    change |frequency j| ≤ ∑ k, |frequency k|
    exact Finset.single_le_sum (fun k _ => abs_nonneg (frequency k)) (Finset.mem_univ j)
  have he : (fun x : ℝ => complexExponentialSum (imaginaryExponents frequency) c (x : ℂ)) =
      ExponentialSumEstimates.exponentialSum frequency c :=
    funext (complexExponentialSum_imaginary frequency c)
  have hz : (fun x : ℝ => complexExponentialSum (imaginaryExponents frequency) c (x : ℂ)) ≠ 0 := by
    rwa [he]
  have h := complexExponentialSum_logRegular_on_unit_subset hn
    (imaginaryExponents frequency) c hσ hexponent hz E hE hEsub
  rwa [he] at h

/-- The actual pruning weak estimate, with a fixed absolute constant once the
spectral diameter exceeds the number of terms. -/
theorem prunedExponentialSum_unit_weak_bound {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    (hzero : ExponentialSumEstimates.exponentialSum frequency c ≠ 0)
    (a : Fin n) {ρ : ℝ} (hlarge : (n : ℝ) < ρ)
    (hdiam : ∀ i j, |frequency j-frequency i| ≤ ρ)
    {E : Set ℝ} (hEsub : E ⊆ Icc (-1/2 : ℝ) (1/2)) {u : ℝ} (hu : 0 < u) :
    volume {t | t ∈ E ∧ ExponentialSumEstimates.exponentialSum frequency c t ≠ 0 ∧
      u*‖ExponentialSumEstimates.exponentialSum frequency c t‖ <
        ‖prunedExponentialSum frequency c a ρ t‖} ≤
      ENNReal.ofReal (oneDimensionalPruningWeakConstant/u) := by
  have hρ : 0 < ρ := lt_of_le_of_lt (Nat.cast_nonneg n) hlarge
  let exponent := imaginaryExponents (fun j => frequency j-frequency a)
  let f := complexExponentialSum exponent c
  have hexponent : ∀ j, ‖exponent j‖ ≤ ρ := centered_imaginaryExponents_norm_le frequency a hdiam
  have hfzero : (fun x : ℝ => f (x : ℂ)) ≠ 0 := by
    intro hz
    apply hzero
    funext x
    apply norm_eq_zero.mp
    rw [← norm_exponentialSum_frequency_sub frequency c (frequency a) x,
      ← complexExponentialSum_imaginary]
    change ‖f (x : ℂ)‖ = 0
    rw [congrFun hz x]
    simp
  obtain ⟨M,w,hM,hw,hbound,hgrowth⟩ :=
    complexExponentialSum_exists_disk_growth_data hn exponent c hρ.le hexponent hfzero
  have hlog0 : 0 ≤ Real.log (16*Real.exp 1) := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    exact Real.log_nonneg (by linarith)
  have hlog : Real.log (16*Real.exp 1) ≤ 16 := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 16)
    linarith
  have hS : 0 < turanDiskGrowthBudget n ρ := by
    unfold turanDiskGrowthBudget
    have hnn : 0 ≤ ((n-1 : ℕ) : ℝ)*Real.log (16*Real.exp 1) :=
      mul_nonneg (Nat.cast_nonneg _) hlog0
    positivity
  have hSbound : turanDiskGrowthBudget n ρ ≤ 20*ρ := by
    have hdegree : ((n-1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (n-1))
    unfold turanDiskGrowthBudget
    nlinarith
  have hweak := analytic_logDerivative_weak_bound_of_growth
    ((analyticOnNhd_complexExponentialSum exponent c).mono (subset_univ _)) hM hS
    (fun z hz => hbound z (sphere_subset_closedBall hz)) hw hgrowth (mul_pos hu hρ)
  have hsub : {t | t ∈ E ∧ ExponentialSumEstimates.exponentialSum frequency c t ≠ 0 ∧
      u*‖ExponentialSumEstimates.exponentialSum frequency c t‖ <
        ‖prunedExponentialSum frequency c a ρ t‖} ⊆
      {t : ℝ | t ∈ Icc (-1/2 : ℝ) (1/2) ∧ u*ρ < ‖deriv f (t : ℂ)/f (t : ℂ)‖} := by
    intro t ht
    refine ⟨hEsub ht.1,?_⟩
    have hq : u < ‖prunedExponentialSum frequency c a ρ t /
        ExponentialSumEstimates.exponentialSum frequency c t‖ := by
      rw [norm_div]
      exact (lt_div_iff₀ (norm_pos_iff.mpr ht.2.1)).2 ht.2.2
    rw [norm_pruned_quotient_eq frequency c a hρ t] at hq
    exact (lt_div_iff₀ hρ).mp hq
  have hcoef : logarithmicDerivativeWeakConstant*turanDiskGrowthBudget n ρ/(u*ρ) ≤
      oneDimensionalPruningWeakConstant/u := by
    calc
      _ ≤ logarithmicDerivativeWeakConstant*(20*ρ)/(u*ρ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSbound logarithmicDerivativeWeakConstant_pos.le)
          (mul_nonneg hu.le hρ.le)
      _ = (20*logarithmicDerivativeWeakConstant)/u := by
        field_simp
        <;> ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hu.le
        unfold oneDimensionalPruningWeakConstant
        linarith
  exact (measure_mono hsub).trans (hweak.trans (ENNReal.ofReal_le_ofReal hcoef))

/-- The full measurable geometric-mean Turan inequality on the unit interval.
This has no analytic estimate or regularity premise. -/
theorem exponentialSum_unit_geometric_turan {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) (E : Set ℝ) (hE : MeasurableSet E)
    (hEsub : E ⊆ Icc (-1/2 : ℝ) (1/2)) (hEpos : 0 < volume E)
    (t : ℝ) (ht : t ∈ Icc (-1/2 : ℝ) (1/2)) :
    ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ≤
      (oneDimensionalTuranConstant/(volume E).toReal)^(n-1)*
        geometricMean E (ExponentialSumEstimates.exponentialSum frequency c) := by
  have hEfin := finite_volume_unit_subset hEsub
  have hα : 0 < (volume E).toReal := ENNReal.toReal_pos (ne_of_gt hEpos) hEfin.ne
  have hαK : (volume E).toReal ≤ oneDimensionalPruningWeakConstant := by
    apply (real_volume_unit_subset_le_one hEsub).trans
    unfold oneDimensionalPruningWeakConstant
    have h := logarithmicDerivativeWeakConstant_pos
    linarith
  have hCK : 2*Real.exp 1*oneDimensionalPruningWeakConstant ≤ oneDimensionalTuranConstant := by
    unfold oneDimensionalTuranConstant
    linarith [Real.exp_pos (1000000:ℝ)]
  have hregular : ∀ (m : ℕ), 0 < m → ∀ (ω : Fin m → ℝ) (z : Fin m → ℂ),
      ExponentialSumEstimates.exponentialSum ω z ≠ 0 →
        LogRegular (volume.restrict E) (ExponentialSumEstimates.exponentialSum ω z) := by
    intro m hm ω z hz
    exact exponentialSum_unit_logRegular hm ω z hz E hE hEsub
  have hsmall : ∀ (m : ℕ), 0 < m → ∀ (ω : Fin m → ℝ) (z : Fin m → ℂ),
      (∀ a b, |ω b-ω a| ≤ (1:ℝ)*m) → ∀ x ∈ Icc (-1/2 : ℝ) (1/2),
        ‖ExponentialSumEstimates.exponentialSum ω z x‖ ≤
          (oneDimensionalTuranConstant/(volume E).toReal)^(m-1)*
            geometricMean E (ExponentialSumEstimates.exponentialSum ω z) := by
    intro m hm ω z hdiam x hx
    by_cases hm1 : m = 1
    · subst m
      rw [norm_exponentialSum_one,geometricMean_exponentialSum_one hEfin hEpos ω z]
      simp
    have hm2 : 2 ≤ m := by omega
    let a : Fin m := ⟨0,hm⟩
    let shifted : Fin m → ℝ := fun j => ω j-ω a
    have hexponent : ∀ j, ‖imaginaryExponents shifted j‖ ≤ (m : ℝ) := by
      intro j
      rw [norm_imaginaryExponents]
      simpa only [one_mul] using hdiam a j
    have h := complexExponentialSum_geometric_bound_unit hm
      (imaginaryExponents shifted) z (Nat.cast_nonneg m) hexponent E hE hEsub hEpos x hx
    simp_rw [complexExponentialSum_imaginary] at h
    change ‖ExponentialSumEstimates.exponentialSum shifted z x‖ ≤
      Real.exp (10000*((m : ℝ)+m))*(1/(volume E).toReal)^(m-1)*
        geometricMean E (ExponentialSumEstimates.exponentialSum shifted z) at h
    rw [norm_exponentialSum_frequency_sub,geometricMean_frequency_sub] at h
    have hbase : Real.exp (1000000:ℝ) ≤ oneDimensionalTuranConstant := by
      unfold oneDimensionalTuranConstant
      have hp := oneDimensionalPruningWeakConstant_pos
      exact le_add_of_nonneg_right (by positivity)
    have hexp := (bounded_spectrum_exp_loss_le hm2 (le_rfl : (m:ℝ) ≤ m)).trans
      (pow_le_pow_left₀ (Real.exp_pos _).le hbase (m-1))
    have hfactor : Real.exp (10000*((m:ℝ)+m))*(1/(volume E).toReal)^(m-1) ≤
        (oneDimensionalTuranConstant/(volume E).toReal)^(m-1) := by
      calc
        _ ≤ oneDimensionalTuranConstant^(m-1)*(1/(volume E).toReal)^(m-1) :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
        _ = _ := by rw [← mul_pow]; congr 1; ring
    exact h.trans (mul_le_mul_of_nonneg_right hfactor (geometricMean_nonneg _ _))
  have hweak : ∀ (m : ℕ), 2 ≤ m → ∀ (ω : Fin m → ℝ) (z : Fin m → ℂ),
      ExponentialSumEstimates.exponentialSum ω z ≠ 0 → ∀ (a : Fin m) (ρ : ℝ),
      (1:ℝ)*m < ρ → (∀ i j, |ω j-ω i| ≤ ρ) →
      ∀ u > 0, volume {s | s ∈ E ∧ ExponentialSumEstimates.exponentialSum ω z s ≠ 0 ∧
        u*‖ExponentialSumEstimates.exponentialSum ω z s‖ <
          ‖prunedExponentialSum ω z a ρ s‖} ≤ ENNReal.ofReal (oneDimensionalPruningWeakConstant/u) := by
    intro m hm ω z hz a ρ hlarge hdiam u hu
    exact prunedExponentialSum_unit_weak_bound (by omega) ω z hz a
      (by simpa only [one_mul] using hlarge) hdiam hEsub hu
  exact exponentialSum_geometric_bound_of_pruning hE hEfin hEpos
    (by norm_num : (0:ℝ) ≤ 1) oneDimensionalTuranConstant_pos hαK hCK
    hregular hsmall hweak n hn frequency c t ht

/-- The actual point-bound form on a measurable subset, including `M=0`. -/
theorem exponentialSum_unit_norm_le_of_bound {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) (E : Set ℝ) (hE : MeasurableSet E)
    (hEsub : E ⊆ Icc (-1/2 : ℝ) (1/2)) (hEpos : 0 < volume E)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x ∈ E, ‖ExponentialSumEstimates.exponentialSum frequency c x‖ ≤ M)
    (t : ℝ) (ht : t ∈ Icc (-1/2 : ℝ) (1/2)) :
    ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ≤
      M*(oneDimensionalTuranConstant/(volume E).toReal)^(n-1) := by
  have hg := geometricMean_le_of_bound hE (finite_volume_unit_subset hEsub) hEpos
    (fun hz => exponentialSum_unit_logRegular hn frequency c hz E hE hEsub) hM hbound
  have h := exponentialSum_unit_geometric_turan hn frequency c E hE hEsub hEpos t ht
  exact h.trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hg
      (pow_nonneg (div_pos oneDimensionalTuranConstant_pos
        (ENNReal.toReal_pos (ne_of_gt hEpos) (finite_volume_unit_subset hEsub).ne)).le _))

end
end LeanNumDetect.MultiTuran
