import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
The Lie--Trotter product formula for real Banach algebras. The proof compares
the two one-step maps through their common derivative at zero and controls
the accumulated error by a noncommutative telescoping estimate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology BigOperators

namespace LeanNumDetect

section BanachAlgebra

variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E]
  [CompleteSpace E] [NormOneClass E]

omit [CompleteSpace E] in
/-- The exponential has its usual scalar exponential bound in a Banach algebra. -/
theorem norm_algebra_exp_le (x : E) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have hsum := NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) x
  have hreal := NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖x‖
  rw [NormedSpace.exp_eq_tsum ℝ]
  calc
    ‖∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • x ^ n‖ ≤
        ∑' n : ℕ, ‖((n.factorial : ℝ)⁻¹) • x ^ n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) * ‖x‖ ^ n := by
      apply Summable.tsum_le_tsum _ hsum (by simpa only [smul_eq_mul] using hreal)
      intro n
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (norm_pow_le x n) (by positivity)
    _ = Real.exp ‖x‖ := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
      simp only [smul_eq_mul]

omit [NormedAlgebra ℝ E] [CompleteSpace E] in
/-- A power perturbation bound valid without commutation of the two factors. -/
theorem norm_pow_sub_pow_le_of_norm_le (x y : E) {K : ℝ}
    (hK : 1 ≤ K) (hx : ‖x‖ ≤ K) (hy : ‖y‖ ≤ K) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ (n : ℝ) * ‖x - y‖ * K ^ n := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  induction n with
  | zero => simp
  | succ n ih =>
    have hypow : ‖y ^ n‖ ≤ K ^ n :=
      (norm_pow_le y n).trans (pow_le_pow_left₀ (norm_nonneg y) hy n)
    calc
      ‖x ^ (n + 1) - y ^ (n + 1)‖ =
          ‖(x ^ n - y ^ n) * x + y ^ n * (x - y)‖ := by
        congr 1
        simp only [pow_succ]
        noncomm_ring
      _ ≤ ‖(x ^ n - y ^ n) * x‖ + ‖y ^ n * (x - y)‖ := norm_add_le _ _
      _ ≤ ‖x ^ n - y ^ n‖ * ‖x‖ + ‖y ^ n‖ * ‖x - y‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ((n : ℝ) * ‖x - y‖ * K ^ n) * K + K ^ n * ‖x - y‖ := by
        gcongr
      _ ≤ ((n : ℝ) * ‖x - y‖ * K ^ n) * K + (K ^ n * K) * ‖x - y‖ := by
        gcongr
        exact le_mul_of_one_le_right (pow_nonneg hK0 _) hK
      _ = ((n + 1 : ℕ) : ℝ) * ‖x - y‖ * K ^ (n + 1) := by
        rw [pow_succ]
        push_cast
        ring

omit [NormOneClass E] in
/-- The one-step product error is smaller than its time step. -/
theorem tendsto_nat_mul_norm_exp_product_error (A B : E) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ‖NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B) -
        NormedSpace.exp ((n : ℝ)⁻¹ • (A + B))‖) atTop (𝓝 0) := by
  let f : ℝ → E := fun t => NormedSpace.exp (t • A) * NormedSpace.exp (t • B) -
    NormedSpace.exp (t • (A + B))
  have hf : HasDerivAt f 0 0 := by
    have hA := hasDerivAt_exp_smul_const A (0 : ℝ)
    have hB := hasDerivAt_exp_smul_const B (0 : ℝ)
    have hAB := hasDerivAt_exp_smul_const (A + B) (0 : ℝ)
    simpa only [f, Pi.mul_def, Pi.sub_def, zero_smul, NormedSpace.exp_zero,
      one_mul, mul_one, sub_self] using (hA.mul hB).sub hAB
  have ht : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa using inv_ne_zero (Nat.cast_ne_zero.mpr (by omega : n ≠ 0) : (n : ℝ) ≠ 0)
  have hs := (hf.tendsto_slope_zero.comp ht).norm
  have hf0 : f 0 = 0 := by simp [f]
  simpa only [Function.comp_def, zero_add, hf0, sub_zero, inv_inv, norm_smul,
    Real.norm_natCast, norm_zero, f] using hs

/-- Lie--Trotter's product formula along all positive integer subdivisions. -/
theorem tendsto_exp_mul_exp_pow (A B : E) :
    Tendsto (fun n : ℕ =>
      (NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B)) ^ n)
      atTop (𝓝 (NormedSpace.exp (A + B))) := by
  let C := ‖A‖ + ‖B‖
  have hC : 0 ≤ C := add_nonneg (norm_nonneg A) (norm_nonneg B)
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖(NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B)) ^ n -
          NormedSpace.exp (A + B)‖ ≤
        ((n : ℝ) * ‖NormedSpace.exp ((n : ℝ)⁻¹ • A) *
          NormedSpace.exp ((n : ℝ)⁻¹ • B) -
            NormedSpace.exp ((n : ℝ)⁻¹ • (A + B))‖) * Real.exp C := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : n ≠ 0)
    have ht : 0 ≤ (n : ℝ)⁻¹ := by positivity
    have hK : 1 ≤ Real.exp ((n : ℝ)⁻¹ * C) :=
      Real.one_le_exp_iff.mpr (mul_nonneg ht hC)
    have hx : ‖NormedSpace.exp ((n : ℝ)⁻¹ • A) *
        NormedSpace.exp ((n : ℝ)⁻¹ • B)‖ ≤ Real.exp ((n : ℝ)⁻¹ * C) := by
      calc
        _ ≤ ‖NormedSpace.exp ((n : ℝ)⁻¹ • A)‖ *
            ‖NormedSpace.exp ((n : ℝ)⁻¹ • B)‖ := norm_mul_le _ _
        _ ≤ Real.exp ‖(n : ℝ)⁻¹ • A‖ * Real.exp ‖(n : ℝ)⁻¹ • B‖ := by
          gcongr <;> apply norm_algebra_exp_le
        _ = Real.exp ((n : ℝ)⁻¹ * C) := by
          rw [← Real.exp_add]
          congr 1
          simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, C]
          ring
    have hy : ‖NormedSpace.exp ((n : ℝ)⁻¹ • (A + B))‖ ≤
        Real.exp ((n : ℝ)⁻¹ * C) := by
      apply (norm_algebra_exp_le _).trans
      apply Real.exp_le_exp.mpr
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left (norm_add_le A B) ht
    have hpow : NormedSpace.exp ((n : ℝ)⁻¹ • (A + B)) ^ n =
        NormedSpace.exp (A + B) := by
      letI : NormedAlgebra ℚ E := .restrictScalars ℚ ℝ E
      rw [← NormedSpace.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        mul_inv_cancel₀ hn0, one_smul]
    have hscalar : (Real.exp ((n : ℝ)⁻¹ * C)) ^ n = Real.exp C := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    simpa only [hpow, hscalar] using norm_pow_sub_pow_le_of_norm_le
      (NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B))
      (NormedSpace.exp ((n : ℝ)⁻¹ • (A + B))) hK hx hy n
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound
  simpa only [zero_mul] using (tendsto_nat_mul_norm_exp_product_error A B).mul_const (Real.exp C)

/-- The dyadic form of Lie--Trotter's product formula. -/
theorem tendsto_exp_mul_exp_pow_two (A B : E) :
    Tendsto (fun n : ℕ =>
      (NormedSpace.exp (((2 ^ n : ℕ) : ℝ)⁻¹ • A) *
        NormedSpace.exp (((2 ^ n : ℕ) : ℝ)⁻¹ • B)) ^ (2 ^ n))
      atTop (𝓝 (NormedSpace.exp (A + B))) :=
  (tendsto_exp_mul_exp_pow A B).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))

end BanachAlgebra

end LeanNumDetect
