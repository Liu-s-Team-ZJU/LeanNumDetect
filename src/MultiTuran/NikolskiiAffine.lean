import General.Fourier.ExponentialSums
import Mathlib.Tactic

/-! # From endpoint bounds to a uniform Nikolskii bound

The two intervals on either side of a point are rescaled independently and
then added. Their lengths sum to one, so this conversion loses no factor.
The endpoint bound is an explicit premise here; the filter construction
supplies it separately.
-/

set_option autoImplicit false
open scoped BigOperators
open Set MeasureTheory

namespace LeanNumDetect.ExponentialSumEstimates
noncomputable section

/-- Translation and dilation preserve the number of exponential terms. -/
theorem exponentialSum_affine {n : ℕ} (frequency : Fin n → ℝ)
    (c : Fin n → ℂ) (a b u : ℝ) :
    exponentialSum (fun j => b * frequency j)
      (fun j => c j * Complex.exp (Complex.I * ((a * frequency j : ℝ) : ℂ))) u =
        exponentialSum frequency c (b * u + a) := by
  unfold exponentialSum
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- An endpoint energy bound for all `n`-term sums controls each point of the
unit interval with the same coefficient. -/
theorem pointwise_energy_bound_of_endpoint {n : ℕ} {K : ℝ}
    (hEndpoint : ∀ (frequency : Fin n → ℝ) (c : Fin n → ℂ),
      ‖exponentialSum frequency c 0‖ ^ 2 ≤
        K ^ 2 * unitEnergy (exponentialSum frequency c))
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖exponentialSum frequency c t‖ ^ 2 ≤
      K ^ 2 * unitEnergy (exponentialSum frequency c) := by
  let f := exponentialSum frequency c
  let shifted := fun j => c j * Complex.exp (Complex.I * ((t * frequency j : ℝ) : ℂ))
  have hright := hEndpoint (fun j => (1 - t) * frequency j) shifted
  have hleft := hEndpoint (fun j => (-t) * frequency j) shifted
  dsimp only [shifted] at hright hleft
  simp only [unitEnergy, exponentialSum_affine, mul_zero, zero_add] at hright hleft
  have hrightScaled := mul_le_mul_of_nonneg_left hright (sub_nonneg.mpr ht.2)
  have hleftScaled := mul_le_mul_of_nonneg_left hleft ht.1
  have hrightChange :
      (1 - t) * (∫ u in (0 : ℝ)..1, ‖f ((1 - t) * u + t)‖ ^ 2) =
        ∫ u in t..1, ‖f u‖ ^ 2 := by
    simpa only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] using
      (intervalIntegral.smul_integral_comp_mul_add
        (fun u => ‖f u‖ ^ 2) (a := 0) (b := 1) (1 - t) t)
  have hleftChange :
      t * (∫ u in (0 : ℝ)..1, ‖f (-t * u + t)‖ ^ 2) =
        ∫ u in (0 : ℝ)..t, ‖f u‖ ^ 2 := by
    have he := intervalIntegral.smul_integral_comp_mul_add
      (fun u => ‖f u‖ ^ 2) (a := 0) (b := 1) (-t) t
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one, neg_add_cancel] at he
    rw [intervalIntegral.integral_symm (f := fun u => ‖f u‖ ^ 2) 0 t] at he
    linarith
  have hrightFinal : (1 - t) * ‖f t‖ ^ 2 ≤ K ^ 2 *
      (∫ u in t..1, ‖f u‖ ^ 2) := by
    calc
      _ ≤ (1 - t) * (K ^ 2 *
          (∫ u in (0 : ℝ)..1, ‖f ((1 - t) * u + t)‖ ^ 2)) := hrightScaled
      _ = K ^ 2 * ((1 - t) *
          (∫ u in (0 : ℝ)..1, ‖f ((1 - t) * u + t)‖ ^ 2)) := by ring
      _ = _ := by rw [hrightChange]
  have hleftFinal : t * ‖f t‖ ^ 2 ≤ K ^ 2 *
      (∫ u in (0 : ℝ)..t, ‖f u‖ ^ 2) := by
    calc
      _ ≤ t * (K ^ 2 *
          (∫ u in (0 : ℝ)..1, ‖f (-t * u + t)‖ ^ 2)) := hleftScaled
      _ = K ^ 2 * (t *
          (∫ u in (0 : ℝ)..1, ‖f (-t * u + t)‖ ^ 2)) := by ring
      _ = _ := by rw [hleftChange]
  have hf : Continuous (fun u => ‖f u‖ ^ 2) :=
    (continuous_exponentialSum frequency c).norm.pow 2
  have hpartition := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 t) (hf.intervalIntegrable t 1)
  change ‖f t‖ ^ 2 ≤ K ^ 2 * (∫ u in (0 : ℝ)..1, ‖f u‖ ^ 2)
  rw [← hpartition]
  nlinarith

/-- The actual closed-interval supremum obeys exactly the endpoint bound. -/
theorem unitSupNorm_sq_le_of_endpoint {n : ℕ} {K : ℝ}
    (hEndpoint : ∀ (frequency : Fin n → ℝ) (c : Fin n → ℂ),
      ‖exponentialSum frequency c 0‖ ^ 2 ≤
        K ^ 2 * unitEnergy (exponentialSum frequency c))
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) :
    unitSupNorm (exponentialSum frequency c) ^ 2 ≤
      K ^ 2 * unitEnergy (exponentialSum frequency c) := by
  have hf := continuous_exponentialSum frequency c
  obtain ⟨t,ht,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0,by simp⟩) hf.norm.continuousOn
  have hsup : unitSupNorm (exponentialSum frequency c) =
      ‖exponentialSum frequency c t‖ :=
    le_antisymm (unitSupNorm_le hf hmax) (norm_le_unitSupNorm hf ht)
  rw [hsup]
  exact pointwise_energy_bound_of_endpoint hEndpoint frequency c ht

/-- Unsquared `L²`--`L∞` conversion, again with no change of coefficient. -/
theorem unitSupNorm_le_of_endpoint {n : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hEndpoint : ∀ (frequency : Fin n → ℝ) (c : Fin n → ℂ),
      ‖exponentialSum frequency c 0‖ ^ 2 ≤
        K ^ 2 * unitEnergy (exponentialSum frequency c))
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) :
    unitSupNorm (exponentialSum frequency c) ≤
      K * Real.sqrt (unitEnergy (exponentialSum frequency c)) := by
  apply (sq_le_sq₀ (unitSupNorm_nonneg (continuous_exponentialSum frequency c))
    (mul_nonneg hK (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (unitEnergy_nonneg _)]
  exact unitSupNorm_sq_le_of_endpoint hEndpoint frequency c

end
end LeanNumDetect.ExponentialSumEstimates
