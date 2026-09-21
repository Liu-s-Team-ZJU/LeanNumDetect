/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
import MathExtras.NumberTheory.Analysis.VaalerGCesMemLp
import MathExtras.NumberTheory.Analysis.VaalerPoUCancellation
import MathExtras.NumberTheory.Analysis.VaalerGRegularityProof
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Vaaler Theorem 6: unconditional per-`M` `L²` membership of `gCes` — fully discharged

This NEW leaf proves OUTRIGHT (axiom/sorry-free):

  `memLp_gCes_two_all : ∀ M, MemLp (gCes M) 2 volume`.

`gCes M x = (½·(cesaroCore M)′ + ½·tailFn′ : ℂ)` is already PROVEN continuous
(`continuous_gCes`).  The subtle point is that `gCes M` is **NOT** in `L¹` and is **NOT**
dominated by `C·(1+x²)⁻¹`: the tail derivative `tailFn′ x = 2·fejerK x + 2x·(deriv fejerK x)`
carries an oscillating `O(1/x)` summand `2x·(deriv fejerK x)` (e.g. `~ sin(2πx)/(πx)`), which
is square-integrable but neither integrable nor `O(1/x²)`.  Hence we use the genuine `L²`
envelope `|gReal M x| ≤ A·(1+|x|)⁻¹` (giving `‖f x‖² ≤ A²·(1+x²)⁻¹`, integrable), not the
stronger `(1+x²)⁻¹` envelope used by `VaalerGCesMemLp`.

## Route
* `memLp_two_of_continuous_decay_one` — **reusable bridge (proved here)**: a continuous
  `f : ℝ → ℂ` with `∀ x, ‖f x‖ ≤ A·(1+|x|)⁻¹` lies in `MemLp 2`.  Proof: `‖f x‖² ≤
  A²·(1+|x|)⁻² ≤ A²·(1+x²)⁻¹`, dominate `‖f·‖²` by the integrable `A²·(1+x²)⁻¹`, then
  `memLp_two_iff_integrable_sq_norm`.
* `decay_one_of_large_compact` — **reusable bridge (proved here)**: continuity on a centred
  compact box plus a large-`|x|` bound `|h x| ≤ C·(|x|)⁻¹` (for `|x| ≥ R`, `R ≥ 1`) yields a
  global `|h x| ≤ A·(1+|x|)⁻¹`.
* The large-`|x|` bound for `gReal M` is assembled from `abs_deriv_fejerK_le`
  (shifted-Fejér `O(1/x²)` for `|·| ≥ 1`) and `fejerK_le_inv_sq`, via the explicit
  `HasDerivAt` of `cesaroCore M` and `tailFn` (`tailFn = 2·z·fejerK z`).

## Book
Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6.
-/

noncomputable section

open MeasureTheory Complex Real

namespace MathExtras.NumberTheory.Analysis.VaalerGCesMemLpDischarge

open MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerGRegularityProof
open MathExtras.NumberTheory.Analysis.VaalerPoUCancellation

/-! ## §1 — Reusable `L²` bridge from a `(1+|x|)⁻¹` envelope -/

/-- `(1+|x|)⁻² ≤ (1+x²)⁻¹`: from `(1+|x|)² = 1 + 2|x| + x² ≥ 1 + x²`. -/
theorem inv_one_add_abs_sq_le (x : ℝ) : (1 + |x|)⁻¹ ^ 2 ≤ (1 + x ^ 2)⁻¹ := by
  have hax : (0 : ℝ) ≤ |x| := abs_nonneg x
  have h1 : (0 : ℝ) < 1 + |x| := by positivity
  have h2 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hkey : (1 : ℝ) + x ^ 2 ≤ (1 + |x|) ^ 2 := by
    have : (1 + |x|) ^ 2 = 1 + 2 * |x| + |x| ^ 2 := by ring
    rw [this, sq_abs]; nlinarith [hax]
  rw [inv_pow]
  rw [inv_le_inv₀ (by positivity) h2]
  -- goal : 1 + x^2 ≤ (1 + |x|)^2
  exact hkey

/-- **PROVEN, reusable.**  A continuous `f : ℝ → ℂ` dominated by `A·(1+|x|)⁻¹` is in `L²`. -/
theorem memLp_two_of_continuous_decay_one {f : ℝ → ℂ} {A : ℝ} (hcont : Continuous f)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ A * (1 + |x|)⁻¹) : MemLp f 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  -- dominate ‖f x‖² by A² (1+x²)⁻¹
  have hmaj : Integrable (fun x : ℝ => A ^ 2 * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (A ^ 2)
  refine hmaj.mono' ?_ ?_
  · exact (hcont.norm.pow 2).aestronglyMeasurable
  · filter_upwards with x
    have hax : (0 : ℝ) ≤ |x| := abs_nonneg x
    have h1 : (0 : ℝ) < 1 + |x| := by positivity
    have hnn : (0 : ℝ) ≤ ‖f x‖ := norm_nonneg _
    have hAnn : 0 ≤ A := by
      have := hf 0; simp only [abs_zero, add_zero, inv_one, mul_one] at this
      exact le_trans (norm_nonneg _) this
    -- ‖ ‖f x‖² ‖ = ‖f x‖²
    have hnormsq : ‖‖f x‖ ^ 2‖ = ‖f x‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnormsq]
    calc ‖f x‖ ^ 2 ≤ (A * (1 + |x|)⁻¹) ^ 2 := by
            apply pow_le_pow_left₀ hnn (hf x)
      _ = A ^ 2 * (1 + |x|)⁻¹ ^ 2 := by ring
      _ ≤ A ^ 2 * (1 + x ^ 2)⁻¹ := by
            apply mul_le_mul_of_nonneg_left (inv_one_add_abs_sq_le x) (by positivity)

/-! ## §2 — `(1+|x|)⁻¹` envelope from a large-`|x|` `1/|x|` bound + compact continuity -/

/-- **PROVEN, reusable.**  If `h` is continuous, and `|h x| ≤ C·|x|⁻¹` for `|x| ≥ R`
(with `R ≥ 1`, `C ≥ 0`), then globally `|h x| ≤ A·(1+|x|)⁻¹` for a suitable `A ≥ 0`.

For `|x| ≥ R`: `|x|⁻¹ ≤ 2(1+|x|)⁻¹` (since `1+|x| ≤ 2|x|`), so `|h x| ≤ 2C(1+|x|)⁻¹`.
For `|x| ≤ R`: `h` is bounded by `B` on the compact `[-R,R]`, and `(1+|x|)⁻¹ ≥ (1+R)⁻¹`,
so `|h x| ≤ B = B(1+R)·(1+R)⁻¹ ≤ B(1+R)·(1+|x|)⁻¹`. -/
theorem decay_one_of_large_compact {h : ℝ → ℝ} {C R : ℝ} (hcont : Continuous h)
    (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hlarge : ∀ x : ℝ, R ≤ |x| → |h x| ≤ C * |x|⁻¹) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, |h x| ≤ A * (1 + |x|)⁻¹ := by
  -- compact bound on [-R, R]
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hcont.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (h 0)) (hB 0 (by
    constructor <;> [linarith; linarith]))
  refine ⟨2 * C + B * (1 + R), by positivity, fun x => ?_⟩
  have hax : (0 : ℝ) ≤ |x| := abs_nonneg x
  have h1 : (0 : ℝ) < 1 + |x| := by positivity
  have hinv_nonneg : (0 : ℝ) ≤ (1 + |x|)⁻¹ := le_of_lt (inv_pos.mpr h1)
  by_cases hx : R ≤ |x|
  · -- large regime
    have hxpos : (0 : ℝ) < |x| := lt_of_lt_of_le (by linarith) hx
    -- |x|⁻¹ ≤ 2 (1+|x|)⁻¹
    have hkey : |x|⁻¹ ≤ 2 * (1 + |x|)⁻¹ := by
      rw [inv_eq_one_div, show 2 * (1 + |x|)⁻¹ = 2 / (1 + |x|) by rw [div_eq_mul_inv],
        div_le_div_iff₀ hxpos h1]
      nlinarith [hx, hR]
    calc |h x| ≤ C * |x|⁻¹ := hlarge x hx
      _ ≤ C * (2 * (1 + |x|)⁻¹) := mul_le_mul_of_nonneg_left hkey hC
      _ = (2 * C) * (1 + |x|)⁻¹ := by ring
      _ ≤ (2 * C + B * (1 + R)) * (1 + |x|)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ hinv_nonneg
          nlinarith [hB0, hR]
  · -- small regime |x| < R
    have hxle : |x| ≤ R := le_of_not_ge hx
    have hmem : x ∈ Set.Icc (-R) R := by
      rw [Set.mem_Icc]
      refine ⟨?_, le_trans (le_abs_self x) hxle⟩
      have := neg_abs_le x
      linarith
    have hhB : |h x| ≤ B := by
      have := hB x hmem; rwa [Real.norm_eq_abs] at this
    -- (1+|x|)⁻¹ ≥ (1+R)⁻¹
    have hinv_ge : (1 + R)⁻¹ ≤ (1 + |x|)⁻¹ := by
      apply inv_anti₀ h1; linarith
    have hRpos : (0 : ℝ) < 1 + R := by linarith
    calc |h x| ≤ B := hhB
      _ = B * (1 + R) * (1 + R)⁻¹ := by field_simp
      _ ≤ B * (1 + R) * (1 + |x|)⁻¹ := by
          apply mul_le_mul_of_nonneg_left hinv_ge (by positivity)
      _ ≤ (2 * C + B * (1 + R)) * (1 + |x|)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ hinv_nonneg
          nlinarith [hC]

/-! ## §3 — Explicit derivative of `cesaroCore M` as a finite shifted-Fejér sum -/

/-- `HasDerivAt fejerK (deriv fejerK y) y` everywhere (`fejerK` is `C∞`). -/
theorem hasDerivAt_fejerK (y : ℝ) : HasDerivAt fejerK (deriv fejerK y) y :=
  (contDiff_fejerK.differentiable (by simp)).differentiableAt.hasDerivAt

/-- The single shifted-difference summand of `cesaroCore` has the expected derivative. -/
theorem hasDerivAt_cesaro_summand (M m : ℕ) (x : ℝ) :
    HasDerivAt (fun z : ℝ => (1 - ((m : ℝ) + 1) / (M : ℝ)) *
        (fejerK (z - ((m : ℝ) + 1)) - fejerK (z + ((m : ℝ) + 1))))
      ((1 - ((m : ℝ) + 1) / (M : ℝ)) *
        (deriv fejerK (x - ((m : ℝ) + 1)) - deriv fejerK (x + ((m : ℝ) + 1)))) x := by
  have hsub : HasDerivAt (fun z : ℝ => fejerK (z - ((m : ℝ) + 1)))
      (deriv fejerK (x - ((m : ℝ) + 1))) x :=
    (hasDerivAt_fejerK (x - ((m : ℝ) + 1))).comp_sub_const x ((m : ℝ) + 1)
  have hadd : HasDerivAt (fun z : ℝ => fejerK (z + ((m : ℝ) + 1)))
      (deriv fejerK (x + ((m : ℝ) + 1))) x :=
    (hasDerivAt_fejerK (x + ((m : ℝ) + 1))).comp_add_const x ((m : ℝ) + 1)
  exact (hsub.sub hadd).const_mul _

/-- **Explicit derivative of `cesaroCore M`** as a finite sum of shifted-Fejér derivatives. -/
theorem deriv_cesaroCore (M : ℕ) (x : ℝ) :
    deriv (cesaroCore M) x =
      ∑ m ∈ Finset.range M, (1 - ((m : ℝ) + 1) / (M : ℝ)) *
        (deriv fejerK (x - ((m : ℝ) + 1)) - deriv fejerK (x + ((m : ℝ) + 1))) := by
  have hsum : HasDerivAt (cesaroCore M)
      (∑ m ∈ Finset.range M, (1 - ((m : ℝ) + 1) / (M : ℝ)) *
        (deriv fejerK (x - ((m : ℝ) + 1)) - deriv fejerK (x + ((m : ℝ) + 1)))) x := by
    have := HasDerivAt.sum (u := Finset.range M)
      (A := fun m z => (1 - ((m : ℝ) + 1) / (M : ℝ)) *
        (fejerK (z - ((m : ℝ) + 1)) - fejerK (z + ((m : ℝ) + 1))))
      (A' := fun m => (1 - ((m : ℝ) + 1) / (M : ℝ)) *
        (deriv fejerK (x - ((m : ℝ) + 1)) - deriv fejerK (x + ((m : ℝ) + 1))))
      (fun m _ => hasDerivAt_cesaro_summand M m x)
    -- the summed function is `cesaroCore M` (by `cesaroCore_apply`)
    have hfun : (∑ i ∈ Finset.range M, (fun m (z : ℝ) =>
        (1 - ((m : ℝ) + 1) / (M : ℝ)) *
          (fejerK (z - ((m : ℝ) + 1)) - fejerK (z + ((m : ℝ) + 1)))) i) = cesaroCore M := by
      funext z; rw [cesaroCore_apply, Finset.sum_apply]
    rwa [hfun] at this
  exact hsum.deriv

/-! ## §4 — Explicit derivative of `tailFn` and its large-`|x|` bound -/

/-- **Explicit derivative of `tailFn = 2·z·fejerK z`.** -/
theorem deriv_tailFn (x : ℝ) :
    deriv tailFn x = 2 * fejerK x + 2 * x * deriv fejerK x := by
  have hfej : HasDerivAt fejerK (deriv fejerK x) x := hasDerivAt_fejerK x
  have hid : HasDerivAt (fun z : ℝ => 2 * z) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hprod : HasDerivAt (fun z : ℝ => 2 * z * fejerK z)
      (2 * fejerK x + 2 * x * deriv fejerK x) x := by
    refine ((hid.mul hfej).congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards with z
    rfl
  rw [tailFn_eq_two_mul_id_fejerK]
  exact hprod.deriv

/-! ## §5 — Large-`|x|` `1/|x|` bound for `gReal M` -/

/-- The real part of `gCes M`: `gReal M x = ½·(cesaroCore M)′ x + ½·tailFn′ x`. -/
def gReal (M : ℕ) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * deriv (cesaroCore M) x + (1 / 2 : ℝ) * deriv tailFn x

theorem gCes_norm_eq (M : ℕ) (x : ℝ) : ‖gCes M x‖ = |gReal M x| := by
  rw [gCes_apply, gReal, Complex.norm_real, Real.norm_eq_abs]

theorem continuous_gReal (M : ℕ) : Continuous (gReal M) := by
  have h1 : Continuous (deriv (cesaroCore M)) :=
    (contDiff_cesaroCore M).continuous_deriv (by simp)
  have h2 : Continuous (deriv tailFn) := contDiff_tailFn.continuous_deriv (by simp)
  unfold gReal; fun_prop

/-- `K := 2/π + 2/π²`, the shifted-Fejér derivative constant.  Numerically `≈ 0.8393`. -/
theorem fejerK_const_pos : (0 : ℝ) < 2 / π + 2 / π ^ 2 := by positivity

/-- **Large-`|x|` bound on `deriv tailFn`.**  For `|x| ≥ 1`,
`|deriv tailFn x| ≤ (2 + 2·(2/π + 2/π²))·|x|⁻¹`. -/
theorem abs_deriv_tailFn_le {x : ℝ} (hx : 1 ≤ |x|) :
    |deriv tailFn x| ≤ (2 + 2 * (2 / π + 2 / π ^ 2)) * |x|⁻¹ := by
  set K : ℝ := 2 / π + 2 / π ^ 2 with hKdef
  have hK0 : (0 : ℝ) ≤ K := le_of_lt fejerK_const_pos
  have hx0 : x ≠ 0 := by intro h; rw [h] at hx; simp at hx; linarith
  have hxpos : (0 : ℝ) < |x| := lt_of_lt_of_le one_pos hx
  have hxsq_pos : (0 : ℝ) < x ^ 2 := by positivity
  -- (x²)⁻¹ ≤ |x|⁻¹  for |x| ≥ 1
  have hsq_le : (x ^ 2)⁻¹ ≤ |x|⁻¹ := by
    rw [show x ^ 2 = |x| ^ 2 by rw [sq_abs]]
    rw [inv_le_inv₀ (by positivity) hxpos]
    nlinarith [hx]
  rw [deriv_tailFn]
  -- |2 fejerK x + 2 x (deriv fejerK x)| ≤ 2 |fejerK x| + 2 |x| |deriv fejerK x|
  have hfej : |fejerK x| ≤ (x ^ 2)⁻¹ := by
    rw [abs_of_nonneg (by
      rw [fejerK, if_neg hx0]; positivity)]
    exact fejerK_le_inv_sq hx0
  have hdfej : |deriv fejerK x| ≤ K * (x ^ 2)⁻¹ := by rw [hKdef]; exact abs_deriv_fejerK_le hx
  calc |2 * fejerK x + 2 * x * deriv fejerK x|
      ≤ |2 * fejerK x| + |2 * x * deriv fejerK x| := abs_add_le _ _
    _ = 2 * |fejerK x| + 2 * |x| * |deriv fejerK x| := by
        rw [abs_mul, abs_mul, abs_mul]
        norm_num
    _ ≤ 2 * (x ^ 2)⁻¹ + 2 * |x| * (K * (x ^ 2)⁻¹) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hfej (by norm_num)
        · apply mul_le_mul_of_nonneg_left hdfej (by positivity)
    _ ≤ 2 * |x|⁻¹ + 2 * K * |x|⁻¹ := by
        have hxabs : 2 * |x| * (K * (x ^ 2)⁻¹) = 2 * K * |x|⁻¹ := by
          have h2 : |x| * (x ^ 2)⁻¹ = |x|⁻¹ := by
            rw [show x ^ 2 = |x| ^ 2 by rw [sq_abs]]; field_simp
          calc 2 * |x| * (K * (x ^ 2)⁻¹)
              = 2 * K * (|x| * (x ^ 2)⁻¹) := by ring
            _ = 2 * K * |x|⁻¹ := by rw [h2]
        rw [hxabs]
        gcongr
    _ = (2 + 2 * K) * |x|⁻¹ := by ring

/-! ## §6 — Large-`|x|` `1/x²` bound for `deriv (cesaroCore M)` -/

/-- Per-shift bound: for `|x| ≥ 2(M+1)` and `m < M`, the shifted point `x ∓ (m+1)` satisfies
`|x ∓ (m+1)| ≥ |x|/2 ≥ 1`, so `|deriv fejerK (x ∓ (m+1))| ≤ K·(x∓(m+1))⁻² ≤ 4K·(x²)⁻¹`. -/
theorem abs_deriv_fejerK_shift_le {M m : ℕ} (hm : m < M) {x : ℝ}
    (hx : 2 * ((M : ℝ) + 1) ≤ |x|) {s : ℝ} (hs : s = ((m : ℝ) + 1) ∨ s = -((m : ℝ) + 1)) :
    |deriv fejerK (x + s)| ≤ 4 * (2 / π + 2 / π ^ 2) * (x ^ 2)⁻¹ := by
  set K : ℝ := 2 / π + 2 / π ^ 2 with hKdef
  have hK0 : (0 : ℝ) ≤ K := le_of_lt fejerK_const_pos
  have hMpos : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  -- |s| = m+1 ≤ M
  have hm1 : (m : ℝ) + 1 ≤ (M : ℝ) := by
    have : (m + 1 : ℕ) ≤ M := hm
    have := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at this; linarith
  have hsle : |s| ≤ (M : ℝ) := by
    rcases hs with h | h <;> rw [h]
    · rw [abs_of_nonneg (by positivity)]; exact hm1
    · rw [abs_neg, abs_of_nonneg (by positivity)]; exact hm1
  -- |x| ≥ 2(M+1) ≥ 2
  have hxge2 : (2 : ℝ) ≤ |x| := by
    have : (2 : ℝ) ≤ 2 * ((M : ℝ) + 1) := by nlinarith [hMpos]
    linarith
  -- |x + s| ≥ |x| - |s| ≥ |x| - M ≥ |x|/2
  have hxs_lb : |x| / 2 ≤ |x + s| := by
    have htri : |x| - |s| ≤ |x + s| := by
      have := abs_sub_abs_le_abs_sub x (-s)
      simp only [abs_neg, sub_neg_eq_add] at this
      linarith [this]
    -- |x| - M ≥ |x|/2  since |x| ≥ 2M
    have hxM : (M : ℝ) ≤ |x| / 2 := by
      have : 2 * (M : ℝ) ≤ |x| := by nlinarith [hx, hMpos]
      linarith
    linarith [hsle]
  have hxs_ge1 : (1 : ℝ) ≤ |x + s| := by
    have : (1 : ℝ) ≤ |x| / 2 := by linarith [hxge2]
    linarith [hxs_lb]
  -- apply the committed shifted bound at the point (x + s)
  have hbound : |deriv fejerK (x + s)| ≤ K * ((x + s) ^ 2)⁻¹ := by
    rw [hKdef]; exact abs_deriv_fejerK_le hxs_ge1
  -- ((x+s)²)⁻¹ ≤ 4 (x²)⁻¹   since (x+s)² ≥ (|x|/2)² = x²/4
  have hsq_lb : x ^ 2 / 4 ≤ (x + s) ^ 2 := by
    have h0 : (0 : ℝ) ≤ |x| / 2 := by positivity
    have h1 : (|x| / 2) ^ 2 ≤ (x + s) ^ 2 := by
      have := pow_le_pow_left₀ h0 hxs_lb 2
      rwa [sq_abs] at this
    have hxx : (|x| / 2) ^ 2 = x ^ 2 / 4 := by rw [div_pow, sq_abs]; ring
    linarith [h1, hxx.ge, hxx.le]
  have hxsq_pos : (0 : ℝ) < x ^ 2 := by nlinarith [hxge2, sq_abs x]
  have hxs_sq_pos : (0 : ℝ) < (x + s) ^ 2 := by nlinarith [hsq_lb, hxsq_pos]
  have hinv_le : ((x + s) ^ 2)⁻¹ ≤ 4 * (x ^ 2)⁻¹ := by
    rw [show (4 : ℝ) * (x ^ 2)⁻¹ = 4 / x ^ 2 by rw [div_eq_mul_inv],
      inv_eq_one_div, div_le_div_iff₀ hxs_sq_pos hxsq_pos]
    nlinarith [hsq_lb]
  calc |deriv fejerK (x + s)| ≤ K * ((x + s) ^ 2)⁻¹ := hbound
    _ ≤ K * (4 * (x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hinv_le hK0
    _ = 4 * K * (x ^ 2)⁻¹ := by ring

/-- **Large-`|x|` bound on `deriv (cesaroCore M)`.**  For `|x| ≥ 2(M+1)`,
`|deriv (cesaroCore M) x| ≤ (8·M·K)·(x²)⁻¹` with `K = 2/π + 2/π²`. -/
theorem abs_deriv_cesaroCore_le {M : ℕ} {x : ℝ} (hx : 2 * ((M : ℝ) + 1) ≤ |x|) :
    |deriv (cesaroCore M) x| ≤ (8 * (M : ℝ) * (2 / π + 2 / π ^ 2)) * (x ^ 2)⁻¹ := by
  set K : ℝ := 2 / π + 2 / π ^ 2 with hKdef
  have hK0 : (0 : ℝ) ≤ K := le_of_lt fejerK_const_pos
  have hxsq_nonneg : (0 : ℝ) ≤ (x ^ 2)⁻¹ := by positivity
  rw [deriv_cesaroCore]
  -- bound each summand by 8K (x²)⁻¹
  have hterm : ∀ m ∈ Finset.range M,
      |(1 - ((m : ℝ) + 1) / (M : ℝ)) *
        (deriv fejerK (x - ((m : ℝ) + 1)) - deriv fejerK (x + ((m : ℝ) + 1)))|
      ≤ 8 * K * (x ^ 2)⁻¹ := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hMpos : 0 < M := by omega
    -- weight in [-1,1] → |weight| ≤ 1
    have hwt : |1 - ((m : ℝ) + 1) / (M : ℝ)| ≤ 1 := by
      rw [abs_le]
      have hMcast : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
      have hfrac_nonneg : (0 : ℝ) ≤ ((m : ℝ) + 1) / (M : ℝ) := by positivity
      have hfrac_le1 : ((m : ℝ) + 1) / (M : ℝ) ≤ 1 := by
        rw [div_le_one hMcast]
        have h2 : (m + 1 : ℕ) ≤ M := hm
        have := (Nat.cast_le (α := ℝ)).mpr h2
        push_cast at this; linarith
      constructor <;> linarith
    -- the two shifted derivs
    have hd1 : |deriv fejerK (x - ((m : ℝ) + 1))| ≤ 4 * K * (x ^ 2)⁻¹ := by
      have := abs_deriv_fejerK_shift_le hm hx (s := -((m : ℝ) + 1)) (Or.inr rfl)
      rw [hKdef]; rw [show x + -((m : ℝ) + 1) = x - ((m : ℝ) + 1) by ring] at this
      exact this
    have hd2 : |deriv fejerK (x + ((m : ℝ) + 1))| ≤ 4 * K * (x ^ 2)⁻¹ := by
      have := abs_deriv_fejerK_shift_le hm hx (s := ((m : ℝ) + 1)) (Or.inl rfl)
      rw [hKdef]; exact this
    calc |(1 - ((m : ℝ) + 1) / (M : ℝ)) *
            (deriv fejerK (x - ((m : ℝ) + 1)) - deriv fejerK (x + ((m : ℝ) + 1)))|
        = |1 - ((m : ℝ) + 1) / (M : ℝ)| *
            |deriv fejerK (x - ((m : ℝ) + 1)) - deriv fejerK (x + ((m : ℝ) + 1))| := by
          rw [abs_mul]
      _ ≤ 1 * (|deriv fejerK (x - ((m : ℝ) + 1))| + |deriv fejerK (x + ((m : ℝ) + 1))|) := by
          apply mul_le_mul hwt (abs_sub _ _) (abs_nonneg _) (by norm_num)
      _ ≤ 1 * (4 * K * (x ^ 2)⁻¹ + 4 * K * (x ^ 2)⁻¹) := by
          apply mul_le_mul_of_nonneg_left (add_le_add hd1 hd2) (by norm_num)
      _ = 8 * K * (x ^ 2)⁻¹ := by ring
  calc |∑ m ∈ Finset.range M, (1 - ((m : ℝ) + 1) / (M : ℝ)) *
          (deriv fejerK (x - ((m : ℝ) + 1)) - deriv fejerK (x + ((m : ℝ) + 1)))|
      ≤ ∑ m ∈ Finset.range M,
          |(1 - ((m : ℝ) + 1) / (M : ℝ)) *
            (deriv fejerK (x - ((m : ℝ) + 1)) - deriv fejerK (x + ((m : ℝ) + 1)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Finset.range M, 8 * K * (x ^ 2)⁻¹ := Finset.sum_le_sum hterm
    _ = (M : ℝ) * (8 * K * (x ^ 2)⁻¹) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (8 * (M : ℝ) * K) * (x ^ 2)⁻¹ := by ring

/-! ## §7 — The large-`|x|` `1/|x|` bound for `gReal M`, and the `L²` membership -/

/-- **Large-`|x|` `1/|x|` bound for `gReal M`.**  For `|x| ≥ 2(M+1)`,
`|gReal M x| ≤ (4·M·K + 1 + K)·|x|⁻¹` with `K = 2/π + 2/π²`. -/
theorem abs_gReal_le {M : ℕ} {x : ℝ} (hx : 2 * ((M : ℝ) + 1) ≤ |x|) :
    |gReal M x| ≤
      (4 * (M : ℝ) * (2 / π + 2 / π ^ 2) + 1 + (2 / π + 2 / π ^ 2)) * |x|⁻¹ := by
  set K : ℝ := 2 / π + 2 / π ^ 2 with hKdef
  have hK0 : (0 : ℝ) ≤ K := le_of_lt fejerK_const_pos
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hxge1 : (1 : ℝ) ≤ |x| := by nlinarith [hMnn, hx]
  have hxpos : (0 : ℝ) < |x| := lt_of_lt_of_le one_pos hxge1
  have hx0 : x ≠ 0 := fun h => by rw [h] at hxpos; simp at hxpos
  -- (x²)⁻¹ ≤ |x|⁻¹
  have hsq_le : (x ^ 2)⁻¹ ≤ |x|⁻¹ := by
    rw [show x ^ 2 = |x| ^ 2 by rw [sq_abs], inv_le_inv₀ (by positivity) hxpos]
    nlinarith [hxge1]
  have hces : |deriv (cesaroCore M) x| ≤ (8 * (M : ℝ) * K) * |x|⁻¹ := by
    refine le_trans (abs_deriv_cesaroCore_le hx) ?_
    rw [hKdef] at *
    exact mul_le_mul_of_nonneg_left hsq_le (by positivity)
  have htail : |deriv tailFn x| ≤ (2 + 2 * K) * |x|⁻¹ := by rw [hKdef]; exact abs_deriv_tailFn_le hxge1
  have hinv_nonneg : (0 : ℝ) ≤ |x|⁻¹ := le_of_lt (inv_pos.mpr hxpos)
  calc |gReal M x|
      = |(1 / 2 : ℝ) * deriv (cesaroCore M) x + (1 / 2 : ℝ) * deriv tailFn x| := rfl
    _ ≤ |(1 / 2 : ℝ) * deriv (cesaroCore M) x| + |(1 / 2 : ℝ) * deriv tailFn x| := abs_add_le _ _
    _ = (1 / 2 : ℝ) * |deriv (cesaroCore M) x| + (1 / 2 : ℝ) * |deriv tailFn x| := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    _ ≤ (1 / 2 : ℝ) * ((8 * (M : ℝ) * K) * |x|⁻¹) + (1 / 2 : ℝ) * ((2 + 2 * K) * |x|⁻¹) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hces (by norm_num)
        · exact mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = (4 * (M : ℝ) * K + 1 + K) * |x|⁻¹ := by ring

/-- **MAIN — per-`M` `L²` membership of the Cesàro family `gCes`, axiom/sorry-free.** -/
theorem memLp_gCes_two_all : ∀ M : ℕ, MemLp (gCes M) 2 (volume : Measure ℝ) := by
  intro M
  set K : ℝ := 2 / π + 2 / π ^ 2 with hKdef
  -- global (1+|x|)⁻¹ envelope on gReal M, via decay_one_of_large_compact
  obtain ⟨A, hA0, hAle⟩ := decay_one_of_large_compact (h := gReal M)
    (C := 4 * (M : ℝ) * K + 1 + K) (R := 2 * ((M : ℝ) + 1))
    (continuous_gReal M)
    (by have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M; nlinarith)
    (by have hK0 : (0 : ℝ) ≤ K := le_of_lt fejerK_const_pos
        have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M; positivity)
    (fun x hxR => by rw [hKdef]; exact abs_gReal_le hxR)
  -- transfer to ‖gCes M ·‖ and apply the L² bridge
  apply memLp_two_of_continuous_decay_one (continuous_gCes M) (A := A)
  intro x
  rw [gCes_norm_eq]
  exact hAle x

#print axioms memLp_gCes_two_all

end MathExtras.NumberTheory.Analysis.VaalerGCesMemLpDischarge
