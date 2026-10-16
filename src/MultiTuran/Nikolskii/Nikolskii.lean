import MultiTuran.Nikolskii.NikolskiiSampling
import MultiTuran.Nikolskii.NikolskiiLimit
import MultiTuran.Preliminaries.RightRiemann
import MultiTuran.Nikolskii.NikolskiiAffine

/-! # The exact endpoint Nikolskii inequality

The finite annihilating filters give an endpoint estimate on every mesh of
size `n*m`. Their coefficient loss has sharp majorant `π²*n²/4`, while the
sampled energy tends to the actual unit-interval integral.

Source statement: T. Erdélyi, *Inequalities for exponential sums*,
arXiv:1602.02315, Theorem 2.3 (and the `p = ∞`, `q = 2` case of
Theorem 2.5). The proof here constructs its polynomial filters explicitly;
no extremal-polynomial theorem is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped BigOperators Topology

namespace LeanNumDetect.MultiTuran
open ExponentialSumEstimates NikolskiiSampling NikolskiiFilter NikolskiiLimit
noncomputable section

/-- The squared endpoint estimate, with its exact frequency-independent
coefficient and the genuine Lebesgue interval energy. -/
theorem exponentialSum_endpoint_norm_sq_le {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) :
    ‖exponentialSum frequency c 0‖ ^ 2 ≤
      (Real.pi ^ 2 * (n : ℝ) ^ 2 / 4) * unitEnergy (exponentialSum frequency c) := by
  let g : ℝ → ℝ := fun t => ‖exponentialSum frequency c t‖ ^ 2
  have hg : Continuous g := (continuous_exponentialSum frequency c).norm.pow 2
  have hfinite (m : ℕ) (hm : 0 < m) :
      ‖exponentialSum frequency c 0‖ ^ 2 ≤
        filterMajorant n m * rightRiemannSum g (n * m) := by
    have hM : (0 : ℝ) < (n : ℝ) * m := by
      exact mul_pos (by exact_mod_cast hn) (by exact_mod_cast hm)
    have h := endpoint_sample_bound_of_filter (filterPolynomial m)
      (filterPolynomial_eval_zero hm) (filterPolynomial_eval_one m)
      (filterPolynomial_natDegree m) (filterPolynomial_circle_norm_le hm)
      (1 / ((n : ℝ) * m)) frequency c
    rw [filter_bound_power] at h
    have hsample :
        (∑ k : Fin (n * m), ‖exponentialSum frequency c
          (((k.val : ℝ) + 1) * (1 / ((n : ℝ) * m)))‖ ^ 2) =
        ∑ k : Fin (n * m), g (((k.val : ℝ) + 1) / ((n : ℝ) * m)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [g, div_eq_mul_inv, one_mul]
    rw [hsample] at h
    have hR : 0 ≤ rightRiemannSum g (n * m) := by
      unfold rightRiemannSum g
      positivity
    calc
      _ ≤ (1 / filterPower n m - 1) *
          ∑ k : Fin (n * m), g (((k.val : ℝ) + 1) / ((n : ℝ) * m)) := h
      _ = (((n : ℝ) * m) * (1 / filterPower n m - 1)) *
          rightRiemannSum g (n * m) := by
        unfold rightRiemannSum
        push_cast
        field_simp
      _ ≤ filterMajorant n m * rightRiemannSum g (n * m) :=
        mul_le_mul_of_nonneg_right (sampled_filter_loss_le_majorant n m hm) hR
  have hlimit := (tendsto_filterMajorant n).mul (tendsto_rightRiemannSum_mul hg hn)
  have hbound : ∀ᶠ m : ℕ in atTop,
      ‖exponentialSum frequency c 0‖ ^ 2 ≤
        filterMajorant n m * rightRiemannSum g (n * m) := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    exact hfinite m hm
  exact ge_of_tendsto hlimit hbound

/-- Exact squared unit-interval `L²`--`L∞` estimate. -/
theorem exponentialSum_unitSupNorm_sq_le {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) :
    unitSupNorm (exponentialSum frequency c) ^ 2 ≤
      (Real.pi * n / 2) ^ 2 * unitEnergy (exponentialSum frequency c) := by
  apply unitSupNorm_sq_le_of_endpoint
  intro frequency c
  convert exponentialSum_endpoint_norm_sq_le hn frequency c using 1
  ring

/-- Manuscript `lem:nikolskii-unit`, with exactly the coefficient `π*n/2`
for arbitrary angular frequencies, including repeated ones. -/
theorem exponentialSum_unitSupNorm_le {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) :
    unitSupNorm (exponentialSum frequency c) ≤
      (Real.pi * n / 2) * Real.sqrt (unitEnergy (exponentialSum frequency c)) := by
  apply unitSupNorm_le_of_endpoint (by positivity)
  intro frequency c
  convert exponentialSum_endpoint_norm_sq_le hn frequency c using 1
  ring

end
end LeanNumDetect.MultiTuran
