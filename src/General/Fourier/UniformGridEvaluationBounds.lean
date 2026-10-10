import General.Fourier.ExponentialSums
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Evaluation and energy bounds on the uniform unit grid

The continuum-to-grid conversion is purely analytic. It uses a supremum
energy bound and a relative derivative bound, with no exponential-sum or
frequency-separation assumptions.
-/

set_option autoImplicit false
open scoped BigOperators
open Set MeasureTheory
namespace LeanNumDetect.UniformGridEvaluationBounds
open ExponentialSumEstimates
noncomputable section

theorem integral_le_leftRiemannSum_add_error {F : ℝ → ℝ} (hF : Continuous F)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      F t ≤ F u + L * |t - u|)
    {M : ℕ} (hM : 0 < M) :
    (∫ t in (0 : ℝ)..1, F t) ≤
      (∑ k ∈ Finset.range M, F ((k : ℝ) / M)) / M + L / M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hMR
  let a : ℕ → ℝ := fun k => (k : ℝ) / M
  have ha0 : a 0 = 0 := by simp [a]
  have haM : a M = 1 := by simp [a, hM0]
  have hstep (k : ℕ) : a (k + 1) - a k = 1 / (M : ℝ) := by
    dsimp [a]
    push_cast
    ring
  have hcell (k : ℕ) (hk : k < M) :
      (∫ t in a k..a (k + 1), F t) ≤
        (1 / (M : ℝ)) * (F (a k) + L / M) := by
    have hak : 0 ≤ a k := by dsimp [a]; positivity
    have hab : a k ≤ a (k + 1) := by
      have := hstep k
      have : 0 < 1 / (M : ℝ) := by positivity
      linarith [hstep k]
    have hab1 : a (k + 1) ≤ 1 := by
      dsimp [a]
      rw [div_le_one hMR]
      exact_mod_cast (show k + 1 ≤ M by omega)
    have hau : a k ∈ Icc (0 : ℝ) 1 := ⟨hak, hab.trans hab1⟩
    have hh := intervalIntegral.integral_mono_on (μ := volume) hab
      (hF.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (g := fun _ => F (a k) + L / M) (fun t ht => by
        have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hak.trans ht.1, ht.2.trans hab1⟩
        have hdist : |t - a k| ≤ 1 / (M : ℝ) := by
          rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
          linarith [hstep k, ht.2]
        have hh := hLip (a k) hau t ht01
        have hmul : L * |t - a k| ≤ L / M := by
          simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hdist hL
        linarith)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, hstep,
      mul_comm] using hh
  have hpartition := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := a) (n := M) (fun k _ => hF.intervalIntegrable (a k) (a (k + 1)))
  rw [ha0, haM] at hpartition
  rw [← hpartition]
  calc
    _ ≤ ∑ k ∈ Finset.range M, (1 / (M : ℝ)) * (F (a k) + L / M) :=
      Finset.sum_le_sum (fun k hk => hcell k (Finset.mem_range.mp hk))
    _ = (∑ k ∈ Finset.range M, F ((k : ℝ) / M)) / M + L / M := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, a]
      field_simp [hM0]

theorem norm_sq_lipschitz_of_derivative_bound {f : ℝ → ℂ}
    (hf : Continuous f) (hfdiff : Differentiable ℝ f) {D : ℝ}
    (hder : ∀ x ∈ Icc (0 : ℝ) 1, ‖deriv f x‖ ≤ D * unitSupNorm f)
    {u t : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖f t‖^2 ≤ ‖f u‖^2 + (2 * D * unitSupNorm f^2) * |t - u| := by
  let S := unitSupNorm f
  have hS : 0 ≤ S := unitSupNorm_nonneg hf
  have ha : ‖f t‖ ≤ S := norm_le_unitSupNorm hf ht
  have hb : ‖f u‖ ≤ S := norm_le_unitSupNorm hf hu
  have hdiff := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Icc (0 : ℝ) 1) (x := u) (y := t)
    (fun x _ => hfdiff x) hder (convex_Icc 0 1) hu ht
  have hdiff' : ‖f t - f u‖ ≤ D * S * |t - u| := by
    simpa only [Real.norm_eq_abs] using hdiff
  have hsub := (le_abs_self (‖f t‖ - ‖f u‖)).trans (abs_norm_sub_norm_le (f t) (f u))
  have hsum : ‖f t‖ + ‖f u‖ ≤ 2 * S := by linarith
  have hfirst := mul_le_mul_of_nonneg_right hsub
    (add_nonneg (norm_nonneg (f t)) (norm_nonneg (f u)))
  have hsecond := mul_le_mul_of_nonneg_left hsum (norm_nonneg (f t - f u))
  have hthird := mul_le_mul_of_nonneg_right hdiff' (by positivity : 0 ≤ 2 * S)
  change ‖f t‖^2 ≤ ‖f u‖^2 + (2 * D * S^2) * |t - u|
  nlinarith

theorem unitEnergy_mul_gridSize_le {f : ℝ → ℂ}
    (hf : Continuous f) (hfdiff : Differentiable ℝ f)
    {D q : ℝ} (hD : 0 ≤ D) (_hq : 0 ≤ q)
    (hsup : unitSupNorm f^2 ≤ q * unitEnergy f)
    (hder : ∀ x ∈ Icc (0 : ℝ) 1, ‖deriv f x‖ ≤ D * unitSupNorm f)
    {M : ℕ} (hM : 0 < M) (hsize : 4 * D * q ≤ (M : ℝ)) :
    unitEnergy f * (M : ℝ) ≤
      2 * ∑ l ∈ Finset.range (M + 1), ‖f ((l : ℝ) / M)‖^2 := by
  let S := unitSupNorm f
  let I := unitEnergy f
  let Q := ∑ l ∈ Finset.range (M + 1), ‖f ((l : ℝ) / M)‖^2
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hI : 0 ≤ I := unitEnergy_nonneg f
  have hR := integral_le_leftRiemannSum_add_error (hf.norm.pow 2)
    (by positivity : 0 ≤ 2 * D * S^2)
    (fun u hu t ht => norm_sq_lipschitz_of_derivative_bound hf hfdiff hder hu ht) hM
  change I ≤ (∑ l ∈ Finset.range M, ‖f ((l : ℝ) / M)‖^2) / M +
    2 * D * S^2 / M at hR
  have hleft : (∑ l ∈ Finset.range M, ‖f ((l : ℝ) / M)‖^2) ≤ Q := by
    dsimp [Q]
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hR' : I * (M : ℝ) ≤ Q + 2 * D * S^2 := by
    have hmul := (le_div_iff₀ hMR).mp (by simpa only [← add_div] using hR)
    exact hmul.trans (by linarith)
  have hupper : 2 * D * S^2 ≤ 2 * D * q * I := by
    have h := mul_le_mul_of_nonneg_left hsup (by positivity : 0 ≤ 2 * D)
    nlinarith
  have hresolution := mul_le_mul_of_nonneg_right hsize hI
  change I * (M : ℝ) ≤ 2 * Q
  nlinarith

theorem uniformGrid_row_bound {f : ℝ → ℂ}
    (hf : Continuous f) (hfdiff : Differentiable ℝ f)
    {D q : ℝ} (hD : 0 ≤ D) (hq : 0 ≤ q)
    (hsup : unitSupNorm f^2 ≤ q * unitEnergy f)
    (hder : ∀ x ∈ Icc (0 : ℝ) 1, ‖deriv f x‖ ≤ D * unitSupNorm f)
    {M : ℕ} (hM : 0 < M) (hsize : 4 * D * q ≤ (M : ℝ))
    {k : ℕ} (hk : k ≤ M) :
    ((M : ℝ) + 1) * ‖f ((k : ℝ) / M)‖^2 ≤
      4 * q * ∑ l ∈ Finset.range (M + 1), ‖f ((l : ℝ) / M)‖^2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hgrid := unitEnergy_mul_gridSize_le hf hfdiff hD hq hsup hder hM hsize
  have hpoint : (k : ℝ) / M ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hMR]
      exact_mod_cast hk
  have hnorm : ‖f ((k : ℝ) / M)‖^2 ≤ unitSupNorm f^2 :=
    (sq_le_sq₀ (norm_nonneg _) (unitSupNorm_nonneg hf)).2
      (norm_le_unitSupNorm hf hpoint)
  have hnorm' := mul_le_mul_of_nonneg_right (hnorm.trans hsup) hMR.le
  have hgrid' := mul_le_mul_of_nonneg_left hgrid hq
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [sq_nonneg ‖f ((k : ℝ) / M)‖]

theorem uniformGrid_coefficient_energy_lower {s : ℕ} (a : Fin s → ℂ)
    {f : ℝ → ℂ} (hf : Continuous f) (hfdiff : Differentiable ℝ f)
    {c D q : ℝ} (hc : 0 ≤ c) (hD : 0 ≤ D) (hq : 0 ≤ q)
    (hcoeff : c * ‖a‖^2 ≤ unitEnergy f)
    (hsup : unitSupNorm f^2 ≤ q * unitEnergy f)
    (hder : ∀ x ∈ Icc (0 : ℝ) 1, ‖deriv f x‖ ≤ D * unitSupNorm f)
    {M : ℕ} (hM : 0 < M) (hsize : 4 * D * q ≤ (M : ℝ)) :
    (c / 4) * ‖a‖^2 ≤
      (∑ l ∈ Finset.range (M + 1), ‖f ((l : ℝ) / M)‖^2) / ((M : ℝ) + 1) := by
  have hgrid := unitEnergy_mul_gridSize_le hf hfdiff hD hq hsup hder hM hsize
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hcoeffM := mul_le_mul_of_nonneg_right hcoeff hMR.le
  have haux := mul_nonneg (by positivity : 0 ≤ c * ‖a‖^2)
    (show 0 ≤ (M : ℝ) - 1 by linarith)
  apply (le_div_iff₀ (by positivity : 0 < (M : ℝ) + 1)).2
  nlinarith

end
end LeanNumDetect.UniformGridEvaluationBounds
