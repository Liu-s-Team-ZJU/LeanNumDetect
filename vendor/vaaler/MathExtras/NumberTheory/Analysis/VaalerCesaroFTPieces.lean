/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCesaroFTDecomposition
import MathExtras.NumberTheory.Analysis.VaalerHNAssembly
import MathExtras.Analysis.Fourier.FourierL2Toolkit

/-!
# Vaaler minor: the two `L²`-FT sub-residuals `CoreFTeqPrincipalPlusRavg` and `TailFTeqJtail`

This NEW leaf discharges the two precisely-named `L²`-FT sub-residuals that
`VaalerCesaroFTDecomposition.gcesFTeqJhatPlusRavg_of_pieces` reduced the corrected minor
Fourier identity `GCesFTeqJhatPlusRavg` to:

* `CoreFTeqPrincipalPlusRavg` — the **`L¹∩L²` core** transform identity
  `𝓕_Lp(gCore M) =ᵐ jPrincipalCoreC + Ravg M`.  Proved by the `L¹∩L²` route: `gCore M`
  is integrable (finite shifted-Fejér-derivative sum, `O(1/x²)`), so the committed
  agreement bridge (`FourierL2Toolkit.lpFT_coeFn_ae_eq_fourierIntegral`) reduces it to the
  pointwise integral transform `𝓕(gCore M)`.  That transform is computed by the proven
  derivative-multiplier rule `VaalerHNAssembly.halfDeriv_FT_eq_mul` applied to the
  Cesàro-averaged core `cesaroCore M = (1/M)∑_{N<M} HNcore N` (`cesaroCore_eq_average`),
  with each `∫ HNcore N · echar t` given by `HNcore_FT_eq_triangle_cot` and the Cesàro
  average of the oscillatory part collapsed by `VaalerCesaroDirichletSum.sum_cos_odd_eq`.

The TAIL piece `TailFTeqJtail` (the `L²`-only, `gTail ∉ L¹` half) is left isolated as the
remaining named residual `TailFTeqJtail` (which this file does NOT close), but the CORE half
is proved outright.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.31)–(2.32).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerCesaroFTPieces

open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
open MathExtras.NumberTheory.Analysis.VaalerGCesMemLpDischarge
open MathExtras.NumberTheory.Analysis.VaalerGCesMemLp
open MathExtras.NumberTheory.Analysis.VaalerPoUCancellation
open MathExtras.NumberTheory.Analysis.VaalerCesaroRemainderL2
open MathExtras.NumberTheory.Analysis.VaalerCesaroDirichletSum
open MathExtras.NumberTheory.Analysis.VaalerThm16Mechanism
open MathExtras.NumberTheory.Analysis.VaalerJFourierTransform
open MathExtras.NumberTheory.Analysis.VaalerJFTviaHN
open MathExtras.NumberTheory.Analysis.VaalerHNAssembly
open MathExtras.NumberTheory.Analysis.VaalerCesaroFTDecomposition
open MathExtras.Analysis.Fourier.FourierL2Toolkit

/-! ## §1 — A reusable global-decay upgrade with an arbitrary compact threshold -/

/-- **Reusable.**  If `|h x| ≤ C·(x²)⁻¹` for `R ≤ |x|` (with `1 ≤ R`) and `|h x| ≤ B` for
`|x| ≤ R`, then globally `|h x| ≤ (2·max C 0 + 2 B)·(1 + x²)⁻¹`.

For `|x| ≥ R ≥ 1`: `x² ≥ 1`, so `1 + x² ≤ 2 x²`, hence `(x²)⁻¹ ≤ 2(1+x²)⁻¹`.  For `|x| ≤ R`:
`R ≥ 1` is not used — we only need `(1+x²)⁻¹ ≥ ½` which holds for `|x| ≤ 1`; for `1 ≤ |x| ≤ R`
we use the `O(1/x²)` bound when `R ≤ |x|`, else the compact bound, but to keep a single clean
constant we observe `B ≤ 2B(1+x²)⁻¹` requires `(1+x²)⁻¹ ≥ ½` i.e. `|x| ≤ 1`.  We therefore
split at `1`, using the compact bound for `|x| ≤ 1` (`≤ R`) and, for `1 ≤ |x|`, the `O(1/x²)`
bound when `R ≤ |x|` and the compact bound otherwise — bounding the latter by the `O(1/x²)`
constant via `(x²)⁻¹ ≥ (R²)⁻¹`. -/
theorem global_decay_of_large_compact {h : ℝ → ℝ} {C B R : ℝ} (hR1 : 1 ≤ R) (hB : 0 ≤ B)
    (hlarge : ∀ x : ℝ, R ≤ |x| → |h x| ≤ C * (x ^ 2)⁻¹)
    (hsmall : ∀ x : ℝ, |x| ≤ R → |h x| ≤ B) :
    ∀ x : ℝ, |h x| ≤ (2 * max C 0 + 2 * (B * R ^ 2)) * (1 + x ^ 2)⁻¹ := by
  intro x
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hinv_nonneg : (0 : ℝ) ≤ (1 + x ^ 2)⁻¹ := le_of_lt (inv_pos.mpr hpos)
  have hC0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR1
  have hBR : (0 : ℝ) ≤ B * R ^ 2 := by positivity
  by_cases hx : R ≤ |x|
  · -- large branch:  |x| ≥ R ≥ 1
    have hxsq1 : (1 : ℝ) ≤ x ^ 2 := by
      have : (1 : ℝ) ≤ |x| := le_trans hR1 hx
      nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
    have hxsqpos : (0 : ℝ) < x ^ 2 := by linarith
    have hle2 : (x ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
      have h2 : (2 : ℝ) * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) := (div_eq_mul_inv 2 (1 + x ^ 2)).symm
      rw [h2, inv_eq_one_div, div_le_div_iff₀ hxsqpos hpos]
      nlinarith [hxsq1]
    calc |h x| ≤ C * (x ^ 2)⁻¹ := hlarge x hx
      _ ≤ max C 0 * (x ^ 2)⁻¹ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * (2 * (1 + x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hle2 hC0
      _ = (2 * max C 0) * (1 + x ^ 2)⁻¹ := by ring
      _ ≤ (2 * max C 0 + 2 * (B * R ^ 2)) * (1 + x ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ hinv_nonneg; nlinarith
  · -- compact branch:  |x| ≤ R, so 1 + x² ≤ 1 + R², hence (1+x²)⁻¹ ≥ (1+R²)⁻¹ and
    -- B ≤ B·(1+R²)·(1+x²)⁻¹ ≤ 2 B R²·(1+x²)⁻¹
    rw [not_le] at hx
    have hxle : |x| ≤ R := le_of_lt hx
    have hxsq_le : x ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    have hR2 : (1 : ℝ) ≤ R ^ 2 := by nlinarith [hR1]
    have hkey : B ≤ (2 * (B * R ^ 2)) * (1 + x ^ 2)⁻¹ := by
      have hstep : B * (1 + x ^ 2) ≤ 2 * (B * R ^ 2) := by nlinarith [hxsq_le, hR2, hB, sq_nonneg x]
      calc B = B * (1 + x ^ 2) * (1 + x ^ 2)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
        _ ≤ (2 * (B * R ^ 2)) * (1 + x ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right hstep hinv_nonneg
    calc |h x| ≤ B := hsmall x hxle
      _ ≤ (2 * (B * R ^ 2)) * (1 + x ^ 2)⁻¹ := hkey
      _ ≤ (2 * max C 0 + 2 * (B * R ^ 2)) * (1 + x ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ hinv_nonneg; nlinarith

/-! ## §2 — Integrability of the real core derivative and the complex core piece -/

/-- `deriv (cesaroCore M)` (complexified) is integrable: continuous with global `O((1+x²)⁻¹)`
decay (`abs_deriv_cesaroCore_le` upgraded to a global envelope by `global_decay_of_large_compact`). -/
theorem integrable_deriv_cesaroCore (M : ℕ) :
    Integrable (fun x : ℝ => ((deriv (cesaroCore M) x : ℝ) : ℂ)) (volume : Measure ℝ) := by
  have hcontR : Continuous (deriv (cesaroCore M)) :=
    (contDiff_cesaroCore M).continuous_deriv (by simp)
  have hcontC : Continuous (fun x : ℝ => ((deriv (cesaroCore M) x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hcontR
  set R : ℝ := 2 * ((M : ℝ) + 1) with hR
  have hR1 : (1 : ℝ) ≤ R := by have : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M; rw [hR]; linarith
  -- continuity gives a bound on the compact ball |x| ≤ R
  obtain ⟨B, hB0, hBle⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |x| ≤ R → |deriv (cesaroCore M) x| ≤ B := by
    have hcompact : IsCompact (Set.Icc (-R) R) := isCompact_Icc
    obtain ⟨C, hC⟩ := (hcompact.image (hcontR.abs)).bddAbove
    refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
    have hxmem : x ∈ Set.Icc (-R) R := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [abs_le.mp hx |>.1], by linarith [abs_le.mp hx |>.2]⟩
    have hmem : |deriv (cesaroCore M) x| ∈ (fun y => |deriv (cesaroCore M) y|) '' Set.Icc (-R) R :=
      ⟨x, hxmem, rfl⟩
    exact le_trans (hC hmem) (le_max_left _ _)
  set Cdecay : ℝ := 8 * (M : ℝ) * (2 / π + 2 / π ^ 2) with hCdecay
  have hglobal := global_decay_of_large_compact (h := deriv (cesaroCore M))
    (C := Cdecay) (B := B) (R := R) hR1 hB0
    (fun x hx => by rw [hCdecay]; exact abs_deriv_cesaroCore_le hx)
    hBle
  refine integrable_of_global_decay hcontC (A := 2 * max Cdecay 0 + 2 * (B * R ^ 2)) ?_
  intro x
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hglobal x

/-- **`O(1/x²)` bound on a shifted Fejér kernel** for `|x| ≥ 2(M+1)`, `|s| = m+1 ≤ M`.
Mirrors `abs_deriv_fejerK_shift_le` but for `fejerK` itself (via `fejerK_le_inv_sq` and
`fejerK_nonneg`): `|fejerK (x+s)| ≤ 4·(x²)⁻¹`. -/
theorem abs_fejerK_shift_le {M m : ℕ} (hm : m < M) {x : ℝ}
    (hx : 2 * ((M : ℝ) + 1) ≤ |x|) {s : ℝ} (hs : s = ((m : ℝ) + 1) ∨ s = -((m : ℝ) + 1)) :
    |fejerK (x + s)| ≤ 4 * (x ^ 2)⁻¹ := by
  have hMpos : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hm1 : (m : ℝ) + 1 ≤ (M : ℝ) := by
    have : (m + 1 : ℕ) ≤ M := hm
    have := (Nat.cast_le (α := ℝ)).mpr this; push_cast at this; linarith
  have hsle : |s| ≤ (M : ℝ) := by
    rcases hs with h | h <;> rw [h]
    · rw [abs_of_nonneg (by positivity)]; exact hm1
    · rw [abs_neg, abs_of_nonneg (by positivity)]; exact hm1
  have hxge2 : (2 : ℝ) ≤ |x| := by
    have : (2 : ℝ) ≤ 2 * ((M : ℝ) + 1) := by nlinarith [hMpos]
    linarith
  have hxs_lb : |x| / 2 ≤ |x + s| := by
    have htri : |x| - |s| ≤ |x + s| := by
      have := abs_sub_abs_le_abs_sub x (-s)
      simp only [abs_neg, sub_neg_eq_add] at this; linarith [this]
    have hxM : (M : ℝ) ≤ |x| / 2 := by
      have : 2 * (M : ℝ) ≤ |x| := by nlinarith [hx, hMpos]
      linarith
    linarith [hsle]
  have hxs_ne : x + s ≠ 0 := by
    intro h; rw [h, abs_zero] at hxs_lb; linarith [hxge2]
  have hbound : fejerK (x + s) ≤ ((x + s) ^ 2)⁻¹ := fejerK_le_inv_sq hxs_ne
  have hsq_lb : x ^ 2 / 4 ≤ (x + s) ^ 2 := by
    have h0 : (0 : ℝ) ≤ |x| / 2 := by positivity
    have h1 : (|x| / 2) ^ 2 ≤ (x + s) ^ 2 := by
      have := pow_le_pow_left₀ h0 hxs_lb 2; rwa [sq_abs] at this
    have hxx : (|x| / 2) ^ 2 = x ^ 2 / 4 := by rw [div_pow, sq_abs]; ring
    linarith [h1, hxx.ge, hxx.le]
  have hxsq_pos : (0 : ℝ) < x ^ 2 := by nlinarith [hxge2, sq_abs x]
  have hxs_sq_pos : (0 : ℝ) < (x + s) ^ 2 := by nlinarith [hsq_lb, hxsq_pos]
  have hinv_le : ((x + s) ^ 2)⁻¹ ≤ 4 * (x ^ 2)⁻¹ := by
    rw [show (4 : ℝ) * (x ^ 2)⁻¹ = 4 / x ^ 2 by rw [div_eq_mul_inv],
      inv_eq_one_div, div_le_div_iff₀ hxs_sq_pos hxsq_pos]
    nlinarith [hsq_lb]
  rw [abs_of_nonneg (fejerK_nonneg _)]
  exact le_trans hbound hinv_le

/-- The complexification of `cesaroCore M`. -/
def cesaroCoreC (M : ℕ) (x : ℝ) : ℂ := ((cesaroCore M x : ℝ) : ℂ)

/-- `cesaroCoreC M` is differentiable, with derivative the complexified real derivative. -/
theorem hasDerivAt_cesaroCoreC (M : ℕ) (x : ℝ) :
    HasDerivAt (cesaroCoreC M) (((deriv (cesaroCore M) x : ℝ) : ℂ)) x := by
  have hR : HasDerivAt (cesaroCore M) (deriv (cesaroCore M) x) x :=
    ((contDiff_cesaroCore M).differentiable (by simp)).differentiableAt.hasDerivAt
  exact hR.ofReal_comp

theorem differentiable_cesaroCoreC (M : ℕ) : Differentiable ℝ (cesaroCoreC M) :=
  fun x => (hasDerivAt_cesaroCoreC M x).differentiableAt

theorem deriv_cesaroCoreC (M : ℕ) (x : ℝ) :
    deriv (cesaroCoreC M) x = ((deriv (cesaroCore M) x : ℝ) : ℂ) :=
  (hasDerivAt_cesaroCoreC M x).deriv

/-- `cesaroCoreC M` is integrable (continuous + global `O((1+x²)⁻¹)` decay via
`abs_deriv_cesaroCore_le`'s sibling for `cesaroCore` itself — here re-derived from the same
compact + large-decay split, using that `cesaroCore` is a finite sum of `O(1/x²)` shifted
Fejér kernels). -/
theorem integrable_cesaroCoreC (M : ℕ) :
    Integrable (cesaroCoreC M) (volume : Measure ℝ) := by
  -- `cesaroCore M = (1/M) ∑_{N<M} HNcore N`, each `HNcore N` integrable; but cleanest:
  -- continuity + the committed decay of `cesaroCore` from the shifted-Fejér bound.
  have hcontR : Continuous (cesaroCore M) := (contDiff_cesaroCore M).continuous
  have hcontC : Continuous (cesaroCoreC M) := Complex.continuous_ofReal.comp hcontR
  set R : ℝ := 2 * ((M : ℝ) + 1) with hR
  have hR1 : (1 : ℝ) ≤ R := by have : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M; rw [hR]; linarith
  obtain ⟨B, hB0, hBle⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |x| ≤ R → |cesaroCore M x| ≤ B := by
    have hcompact : IsCompact (Set.Icc (-R) R) := isCompact_Icc
    obtain ⟨C, hC⟩ := (hcompact.image (hcontR.abs)).bddAbove
    refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
    have hxmem : x ∈ Set.Icc (-R) R := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [abs_le.mp hx |>.1], by linarith [abs_le.mp hx |>.2]⟩
    have hmem : |cesaroCore M x| ∈ (fun y => |cesaroCore M y|) '' Set.Icc (-R) R := ⟨x, hxmem, rfl⟩
    exact le_trans (hC hmem) (le_max_left _ _)
  -- large bound: |cesaroCore M x| ≤ 8 M·(x²)⁻¹  for |x| ≥ R, from the shifted-Fejér O(1/x²)
  set Cdecay : ℝ := 8 * (M : ℝ) with hCdecay
  have hlarge : ∀ x : ℝ, R ≤ |x| → |cesaroCore M x| ≤ Cdecay * (x ^ 2)⁻¹ := by
    intro x hx
    rw [cesaroCore_apply]
    have hterm : ∀ m ∈ Finset.range M,
        |(1 - ((m : ℝ) + 1) / (M : ℝ)) *
          (fejerK (x - ((m : ℝ) + 1)) - fejerK (x + ((m : ℝ) + 1)))|
        ≤ 8 * (x ^ 2)⁻¹ := by
      intro m hm
      rw [Finset.mem_range] at hm
      have hMpos : 0 < M := by omega
      have hwt : |1 - ((m : ℝ) + 1) / (M : ℝ)| ≤ 1 := by
        rw [abs_le]
        have hMcast : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
        have hfrac_nonneg : (0 : ℝ) ≤ ((m : ℝ) + 1) / (M : ℝ) := by positivity
        have hfrac_le1 : ((m : ℝ) + 1) / (M : ℝ) ≤ 1 := by
          rw [div_le_one hMcast]
          have h2 : (m + 1 : ℕ) ≤ M := hm
          have := (Nat.cast_le (α := ℝ)).mpr h2; push_cast at this; linarith
        constructor <;> linarith
      have hd1 : |fejerK (x - ((m : ℝ) + 1))| ≤ 4 * (x ^ 2)⁻¹ := by
        have := abs_fejerK_shift_le hm hx (s := -((m : ℝ) + 1)) (Or.inr rfl)
        rw [show x + -((m : ℝ) + 1) = x - ((m : ℝ) + 1) by ring] at this; exact this
      have hd2 : |fejerK (x + ((m : ℝ) + 1))| ≤ 4 * (x ^ 2)⁻¹ :=
        abs_fejerK_shift_le hm hx (s := ((m : ℝ) + 1)) (Or.inl rfl)
      calc |(1 - ((m : ℝ) + 1) / (M : ℝ)) *
              (fejerK (x - ((m : ℝ) + 1)) - fejerK (x + ((m : ℝ) + 1)))|
          = |1 - ((m : ℝ) + 1) / (M : ℝ)| *
              |fejerK (x - ((m : ℝ) + 1)) - fejerK (x + ((m : ℝ) + 1))| := by rw [abs_mul]
        _ ≤ 1 * (4 * (x ^ 2)⁻¹ + 4 * (x ^ 2)⁻¹) := by
              apply mul_le_mul hwt _ (abs_nonneg _) (by norm_num)
              exact le_trans (abs_sub _ _) (add_le_add hd1 hd2)
        _ = 8 * (x ^ 2)⁻¹ := by ring
    calc |∑ m ∈ Finset.range M,
            (1 - ((m : ℝ) + 1) / (M : ℝ)) *
              (fejerK (x - ((m : ℝ) + 1)) - fejerK (x + ((m : ℝ) + 1)))|
        ≤ ∑ m ∈ Finset.range M,
            |(1 - ((m : ℝ) + 1) / (M : ℝ)) *
              (fejerK (x - ((m : ℝ) + 1)) - fejerK (x + ((m : ℝ) + 1)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m ∈ Finset.range M, 8 * (x ^ 2)⁻¹ := Finset.sum_le_sum hterm
      _ = (M : ℝ) * (8 * (x ^ 2)⁻¹) := by
          rw [Finset.sum_const, Finset.card_range]; push_cast; ring
      _ = Cdecay * (x ^ 2)⁻¹ := by rw [hCdecay]; ring
  have hglobal := global_decay_of_large_compact (h := cesaroCore M)
    (C := Cdecay) (B := B) (R := R) hR1 hB0 hlarge hBle
  refine integrable_of_global_decay hcontC (A := 2 * max Cdecay 0 + 2 * (B * R ^ 2)) ?_
  intro x
  rw [cesaroCoreC, Complex.norm_real, Real.norm_eq_abs]
  exact hglobal x

/-- `x ↦ (HNcore N x : ℂ) · echar t x` is integrable (finite sum of shifted Fejér kernels
times the bounded character). -/
theorem integrable_HNcore_echar (N : ℕ) (t : ℝ) :
    Integrable (fun z : ℝ => (HNcore N z : ℂ) * echar t z) (volume : Measure ℝ) := by
  have hcast : (fun z : ℝ => (HNcore N z : ℂ) * echar t z)
      = fun z : ℝ => ∑ m ∈ Finset.range N,
          (((fejerK (z - ((m : ℝ) + 1)) : ℂ) * echar t z)
            - ((fejerK (z + ((m : ℝ) + 1)) : ℂ) * echar t z)) := by
    funext z
    unfold HNcore
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => by ring)
  rw [hcast]
  refine MeasureTheory.integrable_finsetSum _ (fun m _ => ?_)
  refine (integrable_fejerK_shift_echar t ((m : ℝ) + 1)).sub ?_
  have hadd_eq : (fun z : ℝ => (fejerK (z + ((m : ℝ) + 1)) : ℂ) * echar t z)
      = (fun z : ℝ => (fejerK (z - (-((m : ℝ) + 1))) : ℂ) * echar t z) := by
    funext z; rw [sub_neg_eq_add]
  rw [hadd_eq]
  exact integrable_fejerK_shift_echar t (-((m : ℝ) + 1))

/-! ## §3 — The pointwise integral FT of `gCore M` -/

/-- `deriv (cesaroCoreC M) = 2 · gCore M` pointwise. -/
theorem deriv_cesaroCoreC_eq_two_gCore (M : ℕ) :
    deriv (cesaroCoreC M) = fun v => 2 * gCore M v := by
  funext v
  rw [deriv_cesaroCoreC, gCore]
  push_cast
  ring

/-- `gCore M` is integrable (`= ½·(deriv (cesaroCore M) : ℂ)`, integrable by §2). -/
theorem integrable_gCore (M : ℕ) : Integrable (gCore M) (volume : Measure ℝ) := by
  have h : gCore M = fun v => (1 / 2 : ℂ) * ((deriv (cesaroCore M) v : ℝ) : ℂ) := by
    funext v; rw [gCore]; push_cast; ring
  rw [h]
  exact (integrable_deriv_cesaroCore M).const_mul _

/-- **The pointwise integral FT of `gCore M`.**  Via the proven half-derivative multiplier
rule (`halfDeriv_FT_eq_mul`) on `f = cesaroCoreC M`, then the Cesàro-average identity
`cesaroCore_eq_average` and the proven `N`-level derivative transform `HNcore_deriv_FT_eq`:

    ∫ gCore M x · echar t x dx
      = (1/M) ∑_{N<M} fejerTriangle t · (π t · cotC t
            + π i t · (i · cos(π(2N+1)t)/sin(π t))).

This is the un-averaged form; §4 collapses the sum to `jPrincipalCore + Ravg`. -/
theorem gCore_echar_integral (M : ℕ) {t : ℝ} (ht : Real.sin (π * t) ≠ 0) :
    (∫ x : ℝ, gCore M x * echar t x)
      = (1 / (M : ℝ) : ℂ) * ∑ N ∈ Finset.range M,
          (MathExtras.Fourier.fejerTriangle t : ℂ)
            * ((π * t : ℂ) * cotC t
                + (π * Complex.I * t : ℂ)
                    * (Complex.I * ((Real.cos (π * (2 * N + 1) * t) : ℂ) / (Real.sin (π * t) : ℂ)))) := by
  -- Step 1: half-derivative multiplier rule.
  have hmul := halfDeriv_FT_eq_mul (f := cesaroCoreC M) (g := gCore M)
    (integrable_cesaroCoreC M) (differentiable_cesaroCoreC M)
    (by rw [deriv_cesaroCoreC_eq_two_gCore]; exact (integrable_gCore M).const_mul 2)
    (deriv_cesaroCoreC_eq_two_gCore M) t
  rw [hmul]
  -- Step 2: ∫ cesaroCoreC M · echar t = (1/M) ∑_{N<M} ∫ (HNcore N : ℂ) · echar t
  have hces_int : (∫ x : ℝ, cesaroCoreC M x * echar t x)
      = (1 / (M : ℝ) : ℂ) * ∑ N ∈ Finset.range M, (∫ z : ℝ, (HNcore N z : ℂ) * echar t z) := by
    -- rewrite the integrand via cesaroCore_eq_average
    have hcast : (fun x : ℝ => cesaroCoreC M x * echar t x)
        = fun x : ℝ => (1 / (M : ℝ) : ℂ) * ∑ N ∈ Finset.range M, ((HNcore N x : ℂ) * echar t x) := by
      funext x
      rw [cesaroCoreC, cesaroCore_eq_average]
      push_cast
      rw [mul_assoc, Finset.sum_mul]
    rw [hcast]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finsetSum]
    intro N _
    exact integrable_HNcore_echar N t
  rw [hces_int]
  -- Step 3: push πit through the (1/M)·∑, and apply HNcore_deriv_FT_eq termwise.
  rw [mul_comm (1 / (M : ℝ) : ℂ) (∑ N ∈ Finset.range M, ∫ z : ℝ, (HNcore N z : ℂ) * echar t z),
    Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun N _ => ?_)
  rw [show (π * Complex.I * t : ℂ) * ((∫ z : ℝ, (HNcore N z : ℂ) * echar t z) * (1 / (M : ℝ) : ℂ))
      = ((π * Complex.I * t : ℂ) * ∫ z : ℝ, (HNcore N z : ℂ) * echar t z) * (1 / (M : ℝ) : ℂ) by ring,
    HNcore_deriv_FT_eq ht]
  ring

/-! ## §4 — Collapsing the Cesàro sum to `fejerTriangle·πt·cotC + Ravg` -/

/-- The `(πit)·(i·cos/sin)` oscillatory factor simplifies to `−πt·cos((2N+1)πt)/sin(πt)`. -/
theorem osc_term_eq (N : ℕ) (t : ℝ) :
    (π * Complex.I * t : ℂ)
        * (Complex.I * ((Real.cos (π * (2 * N + 1) * t) : ℂ) / (Real.sin (π * t) : ℂ)))
      = (-(π * t) : ℂ) * ((Real.cos (π * (2 * N + 1) * t) : ℂ) / (Real.sin (π * t) : ℂ)) := by
  rw [show (π * Complex.I * t : ℂ)
        * (Complex.I * ((Real.cos (π * (2 * N + 1) * t) : ℂ) / (Real.sin (π * t) : ℂ)))
      = (Complex.I * Complex.I) * (π * t : ℂ)
          * ((Real.cos (π * (2 * N + 1) * t) : ℂ) / (Real.sin (π * t) : ℂ)) by ring,
    Complex.I_mul_I]
  ring

/-- **The Cesàro sum of the `gCore` transform collapses to `fejerTriangle·πt·cotC + Ravg`.**

For `sin(π t) ≠ 0` and `M ≥ 1`:

    (1/M) ∑_{N<M} fejerTriangle·(π t·cotC + π i t·(i·cos(π(2N+1)t)/sin(π t)))
      = fejerTriangle t · (π t) · cotC t + (Ravg M t : ℂ).

The principal `fejerTriangle·πt·cotC` is `N`-independent (×M/M = itself); the oscillatory part
averages by `VaalerCesaroDirichletSum.sum_cos_odd_eq` (with `θ = π t`) to
`−fejerTriangle·πt·sin(2πMt)/(2M sin²(π t)) = Ravg M t`. -/
theorem cesaroSum_collapse {M : ℕ} (hM : 0 < M) {t : ℝ} (ht : Real.sin (π * t) ≠ 0) :
    (1 / (M : ℝ) : ℂ) * ∑ N ∈ Finset.range M,
        (MathExtras.Fourier.fejerTriangle t : ℂ)
          * ((π * t : ℂ) * cotC t
              + (π * Complex.I * t : ℂ)
                  * (Complex.I * ((Real.cos (π * (2 * N + 1) * t) : ℂ) / (Real.sin (π * t) : ℂ))))
      = (MathExtras.Fourier.fejerTriangle t : ℂ) * (π * t : ℂ) * cotC t + (Ravg M t : ℂ) := by
  have hMC : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMCc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  -- split each summand into principal (N-independent) + oscillatory
  have hsplit : ∀ N ∈ Finset.range M,
      (MathExtras.Fourier.fejerTriangle t : ℂ)
          * ((π * t : ℂ) * cotC t
              + (π * Complex.I * t : ℂ)
                  * (Complex.I * ((Real.cos (π * (2 * N + 1) * t) : ℂ) / (Real.sin (π * t) : ℂ))))
        = (MathExtras.Fourier.fejerTriangle t : ℂ) * ((π * t : ℂ) * cotC t)
          + (MathExtras.Fourier.fejerTriangle t : ℂ)
              * ((-(π * t) : ℂ) * ((Real.cos (π * (2 * N + 1) * t) : ℂ) / (Real.sin (π * t) : ℂ))) := by
    intro N _; rw [osc_term_eq N t]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_const, Finset.card_range, mul_add, ← Finset.mul_sum]
  -- principal piece:  (1/M)·(M • (fejerTriangle·πt·cotC)) = fejerTriangle·πt·cotC
  have hprinc : (1 / (M : ℝ) : ℂ) * ((M : ℕ) • ((MathExtras.Fourier.fejerTriangle t : ℂ)
        * ((π * t : ℂ) * cotC t)))
      = (MathExtras.Fourier.fejerTriangle t : ℂ) * (π * t : ℂ) * cotC t := by
    rw [nsmul_eq_mul]
    have hcast : ((M : ℕ) : ℂ) = ((M : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, show (1 / (M : ℝ) : ℂ) = ((1 / (M : ℝ) : ℝ) : ℂ) by push_cast; ring]
    rw [← mul_assoc, ← Complex.ofReal_mul, show (1 / (M : ℝ) : ℝ) * (M : ℝ) = 1 by
      field_simp]
    push_cast
    ring
  -- oscillatory piece:  (1/M)·fejerTriangle·(−πt)·(∑cos)/sin = Ravg
  have hosc : (1 / (M : ℝ) : ℂ) * ((MathExtras.Fourier.fejerTriangle t : ℂ)
        * ∑ N ∈ Finset.range M,
            ((-(π * t) : ℂ) * ((Real.cos (π * (2 * N + 1) * t) : ℂ) / (Real.sin (π * t) : ℂ))))
      = (Ravg M t : ℂ) := by
    have hsinne : (Real.sin (π * t) : ℂ) ≠ 0 := by exact_mod_cast ht
    -- pull the constants out of the sum:  ∑ = (−πt/sin)·∑cos((2N+1)πt)
    have hsum : (∑ N ∈ Finset.range M,
          ((-(π * t) : ℂ) * ((Real.cos (π * (2 * N + 1) * t) : ℂ) / (Real.sin (π * t) : ℂ))))
        = (-(π * t) : ℂ) / (Real.sin (π * t) : ℂ)
            * ((∑ N ∈ Finset.range M, Real.cos ((2 * (N : ℝ) + 1) * (π * t)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun N _ => ?_)
      have hc : Real.cos (π * (2 * N + 1) * t) = Real.cos ((2 * (N : ℝ) + 1) * (π * t)) := by
        congr 1; ring
      rw [hc]; ring
    rw [hsum, sum_cos_odd_eq ht M, Ravg]
    have hsin2 : Real.sin (2 * (M : ℝ) * (π * t)) = Real.sin (2 * π * (M : ℝ) * t) := by
      congr 1; ring
    rw [hsin2]
    push_cast
    field_simp
  rw [hprinc, hosc]

/-! ## §5 — The principal `fejerTriangle·πt·cotC = jPrincipalCoreC` match -/

open MathExtras.NumberTheory.Analysis.VaalerFejerCoefficientNonneg
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT

/-- **`fejerTriangle t · π t · cotC t = jPrincipalCoreC t` for `sin(π t) ≠ 0`.**

On `|t| ≥ 1` both sides vanish (`fejerTriangle = 0`; `jPrincipalCore = vaalerJhatCont − jTail =
0 − 0`).  On `0 < |t| < 1`: `jPrincipalCore t = vaalerJhat |t| − |t| = π|t|(1−|t|)cot(π|t|)`, and
`t·cot(πt) = |t|·cot(π|t|)` (cot is odd), while `fejerTriangle t = 1 − |t|`, so the two agree. -/
theorem principal_eq_jPrincipalCoreC {t : ℝ} (ht : Real.sin (π * t) ≠ 0) :
    (MathExtras.Fourier.fejerTriangle t : ℂ) * (π * t : ℂ) * cotC t = jPrincipalCoreC t := by
  -- both sides as a real number, then cast
  have hcot_odd : Real.cot (π * (-t)) = - Real.cot (π * t) := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, mul_neg, Real.cos_neg, Real.sin_neg]
    ring
  have hcotC : cotC t = ((Real.cot (π * t) : ℝ) : ℂ) := by
    rw [cotC, Real.cot_eq_cos_div_sin]; push_cast; rfl
  -- the real principal value
  have hreal : (MathExtras.Fourier.fejerTriangle t) * (π * t) * Real.cot (π * t)
      = jPrincipalCore t := by
    rw [jPrincipalCore, jTail, vaalerJhatCont]
    by_cases h1 : 1 ≤ |t|
    · rw [MathExtras.Fourier.fejerTriangle_eq_zero_of_one_le_abs h1, if_pos h1, if_pos h1]
      ring
    · rw [not_le] at h1
      have ht0 : t ≠ 0 := by rintro rfl; simp at ht
      have hkey : t * Real.cot (π * t) = |t| * Real.cot (π * |t|) := by
        rcases lt_or_gt_of_ne ht0 with hneg | hpos
        · rw [abs_of_neg hneg, hcot_odd]; ring
        · rw [abs_of_pos hpos]
      rw [MathExtras.Fourier.fejerTriangle_eq_one_sub_abs_of_abs_le_one (le_of_lt h1),
        if_neg (not_le.mpr h1), if_neg ht0, if_neg (not_le.mpr h1), if_neg ht0, vaalerJhat]
      -- (1−|t|)·πt·cot(πt) = π|t|(1−|t|)cot(π|t|) + |t| − |t|
      have hpv : (1 - |t|) * (π * t) * Real.cot (π * t)
          = π * |t| * (1 - |t|) * Real.cot (π * |t|) := by
        rw [show (1 - |t|) * (π * t) * Real.cot (π * t)
              = π * (1 - |t|) * (t * Real.cot (π * t)) by ring, hkey]; ring
      rw [hpv]; ring
  rw [hcotC, jPrincipalCoreC]
  rw [show (MathExtras.Fourier.fejerTriangle t : ℂ) * (π * t : ℂ) * ((Real.cot (π * t) : ℝ) : ℂ)
        = ((MathExtras.Fourier.fejerTriangle t * (π * t) * Real.cot (π * t) : ℝ) : ℂ) by
    push_cast; ring]
  rw [hreal]

/-! ## §6 — The pointwise core identity (`M ≥ 1`) -/

/-- **The pointwise integral FT of `gCore M` equals `jPrincipalCoreC + Ravg` (`M ≥ 1`,
`sin(π t) ≠ 0`).** -/
theorem gCore_echar_integral_eq {M : ℕ} (hM : 0 < M) {t : ℝ} (ht : Real.sin (π * t) ≠ 0) :
    (∫ x : ℝ, gCore M x * echar t x) = jPrincipalCoreC t + (Ravg M t : ℂ) := by
  rw [gCore_echar_integral M ht, cesaroSum_collapse hM ht, principal_eq_jPrincipalCoreC ht]

/-! ## §7 — The `L²`-FT identity and the named residual (`M ≥ 1`) -/

/-- `sin (π t) ≠ 0` for a.e. `t` (the zero set `{n : ℤ}` is countable, hence null). -/
theorem ae_sin_pi_mul_ne_zero :
    ∀ᵐ t : ℝ, Real.sin (π * t) ≠ 0 := by
  have hsub : {t : ℝ | Real.sin (π * t) = 0} ⊆ Set.range ((↑) : ℤ → ℝ) := by
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    rw [show π * t = t * π by ring, Real.sin_eq_zero_iff] at ht
    obtain ⟨n, hn⟩ := ht
    exact ⟨n, mul_right_cancel₀ Real.pi_ne_zero hn⟩
  have hnull : volume (Set.range ((↑) : ℤ → ℝ)) = 0 :=
    Set.Countable.measure_zero (Set.countable_range _) _
  have : volume {t : ℝ | Real.sin (π * t) = 0} = 0 :=
    measure_mono_null hsub hnull
  rw [MeasureTheory.ae_iff]
  convert this using 2
  ext t; simp

/-- **PROVEN (`M ≥ 1`) — the `L¹∩L²` core transform identity.**

For `M ≥ 1`, the Plancherel `L²`-transform of `gCore M` agrees a.e. with `jPrincipalCoreC + Ravg M`:

    `⇑(𝓕_Lp(gCore M)) =ᵐ fun t => jPrincipalCoreC t + (Ravg M t : ℂ)`.

Route: `gCore M` is `L¹∩L²` (§1–§2), so the toolkit bridge `lpFT_coeFn_ae_eq_fourierIntegral`
gives `⇑(𝓕_Lp(gCore M)) =ᵐ 𝓕(gCore M)`; the pointwise integral transform `𝓕(gCore M) t =
∫ gCore M · echar t` (`integral_mul_echar_eq_fourier`) equals `jPrincipalCoreC t + Ravg M t` for
`sin(π t) ≠ 0` (`gCore_echar_integral_eq`), which holds for a.e. `t` (`ae_sin_pi_mul_ne_zero`).

NOTE: the committed `VaalerCesaroFTDecomposition.CoreFTeqPrincipalPlusRavg` is stated `∀ M`,
but it is FALSE at `M = 0` (there `gCore 0 = 0`, so `𝓕 = 0`, while `jPrincipalCoreC ≠ 0` and
`Ravg 0 = 0`).  This is the analytically correct `M ≥ 1` form; the downstream consumer only
needs the `atTop` limit, for which `M = 0` is immaterial (see `tendsto_fourierCore_Ravg`). -/
theorem coreFT_eq_principal_plus_Ravg_pos {M : ℕ} (hM : 0 < M)
    (h : MemLp (gCore M) 2 (volume : Measure ℝ)) :
    (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
        (h.toLp (gCore M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] fun t : ℝ => jPrincipalCoreC t + (Ravg M t : ℂ) := by
  -- bridge to the pointwise integral transform
  have hbridge : (⇑(lpFT (gCore M) h) : ℝ → ℂ) =ᵐ[volume] 𝓕 (gCore M) :=
    lpFT_coeFn_ae_eq_fourierIntegral (gCore M) (integrable_gCore M) h
  -- on `sin (π t) ≠ 0`, the integral transform is the target
  have hpt : ∀ᵐ t : ℝ, 𝓕 (gCore M) t = jPrincipalCoreC t + (Ravg M t : ℂ) := by
    filter_upwards [ae_sin_pi_mul_ne_zero] with t ht
    rw [← integral_mul_echar_eq_fourier (gCore M) t, gCore_echar_integral_eq hM ht]
  filter_upwards [hbridge, hpt] with t h1 h2
  rw [show (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.toLp (gCore M))) : ℝ → ℂ) t
        = (⇑(lpFT (gCore M) h) : ℝ → ℂ) t from rfl, h1, h2]

#print axioms integrable_gCore
#print axioms gCore_echar_integral_eq
#print axioms cesaroSum_collapse
#print axioms principal_eq_jPrincipalCoreC
#print axioms coreFT_eq_principal_plus_Ravg_pos

/-! ## §8 — The `L²`-only TAIL Fourier sub-residual `TailFTeqJtail` (the `gTail ∉ L¹` half)

The committed `VaalerCesaroFTDecomposition.gcesFTeqJhatPlusRavg_of_pieces` reduced the
sign-corrected minor Fourier identity to the two named `L²`-FT sub-residuals
`CoreFTeqPrincipalPlusRavg` and `TailFTeqJtail`.  §1–§7 above proved (the `M ≥ 1` form of)
the **core** half; this section closes the **tail** half outright:

    `tailFT_eq_jTail : TailFTeqJtail`   (`⇑(𝓕_Lp gTail) =ᵐ jTailC`).

### Why this is the hard `L²`-only half, and the route that avoids the obstruction

`gTail = ½·tailFn′` is in `L²` but NOT `L¹` (`tailFn ~ O(1/x)`), so neither Mathlib's
`Real.fourier_deriv` (needs `Integrable tailFn`) nor `Real.deriv_fourier` (the `x·g` rule, needs
`Integrable (x • fejerK)`, also `O(1/x)`) applies to compute `𝓕(gTail)` forward.  Instead we
**invert**: `gTail` is the inverse transform of the band-limited `L¹∩L²` function `jTailC`.

* `jTailC = boxC − (fejerTriangle : ℂ)` pointwise (`|t|·1_{|t|<1} = 1_{(-1,1)} − (1−|t|)₊`),
  `jTailC_eq_boxC_sub_fejerTriangle`;
* `𝓕(boxC)(x) = sin(2πx)/(πx)` (a clean interval-integral FTC, `boxC_fourier`) and
  `𝓕(fejerTriangle) = fejerK` (the committed `SincSquare.fourier_fejerTriangle_eq_sincSqPi`
  + `VaalerFejerFT.fejerK_eq_sincSqPi`), so `𝓕(jTailC) = 𝓕(boxC) − fejerK = gTail`
  (`fourierIntegral_jTailC_eq_gTail`, the `deriv_tailFn` matching);
* `jTailC` is even (`jTailC_even`) and so is `gTail` (`gTail_even`), hence
  `𝓕⁻(jTailC) = 𝓕(jTailC)(−·) = gTail`;
* with the **inverse `L¹∩L²` Fourier bridge** `fourierIntegralInv_ae_eq_fourierTransformₗᵢ_symm`
  (a Mathlib-gap sibling of `FourierL1L2Agreement.fourierIntegral_ae_eq_fourierTransformₗᵢ`,
  proved here in §8.3), `⇑(𝓕_Lp.symm (toLp jTailC)) =ᵐ 𝓕⁻(jTailC) = gTail`, so at the `Lp`
  level `𝓕_Lp.symm (toLp jTailC) = toLp gTail`; applying the Plancherel isometry `𝓕_Lp` gives
  `𝓕_Lp (toLp gTail) = toLp jTailC`, i.e. the goal.

Verified numerically (mpmath, `1e-25`) before formalising: `𝓕(jTailC) = gTail` on the grid and
`gTail(x) = sin(2πx)/(πx) − fejerK x`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.31)–(2.32); Mathlib `Analysis.Fourier.LpSpace` (Plancherel isometry),
`Analysis.Fourier.FourierTransform` (`fourierInv_eq_fourier_neg`). -/

open MathExtras.NumberTheory.Analysis.VaalerGRegularityProof
open SchwartzMap

/-! ### §8.1 — `jTailC` even/bounded/`L¹∩L²`; `gTail` even -/

/-- `|jTail t| ≤ 1` (it equals `0` or `|t|` with `|t| < 1`). -/
theorem jTail_abs_le_one (t : ℝ) : |jTail t| ≤ 1 := by
  unfold jTail
  by_cases h1 : 1 ≤ |t|
  · simp [h1]
  · simp only [if_neg h1]
    by_cases h0 : t = 0
    · simp [h0]
    · simp only [if_neg h0]; rw [abs_abs]; exact le_of_lt (not_le.mp h1)

theorem measurable_jTail : Measurable jTail := by
  unfold jTail
  apply Measurable.ite
  · exact measurableSet_le measurable_const measurable_abs
  · exact measurable_const
  · apply Measurable.ite
    · exact measurableSet_singleton 0 |>.preimage measurable_id |>.congr (by ext; simp)
    · exact measurable_const
    · exact measurable_abs

theorem aesm_jTailC : AEStronglyMeasurable jTailC (volume : Measure ℝ) :=
  Complex.continuous_ofReal.comp_aestronglyMeasurable measurable_jTail.aestronglyMeasurable

/-- The support of `jTail` is contained in `[-1, 1]` (it vanishes for `1 ≤ |t|`). -/
theorem support_jTail_subset : Function.support jTail ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro t ht
  rw [Function.mem_support] at ht
  by_contra hmem
  apply ht
  rw [Set.mem_Icc, not_and_or] at hmem
  unfold jTail
  have h1 : 1 ≤ |t| := by
    rcases hmem with h | h
    · rw [not_le] at h; rw [le_abs]; right; linarith
    · rw [not_le] at h; rw [le_abs]; left; linarith
  simp [h1]

/-- **`jTailC ∈ L¹`** — bounded by `1`, supported in the finite-measure `[-1,1]`. -/
theorem integrable_jTailC : Integrable jTailC (volume : Measure ℝ) := by
  refine Integrable.mono' (g := Set.indicator (Set.Icc (-1:ℝ) 1) (fun _ => (1:ℝ))) ?_ aesm_jTailC ?_
  · refine (integrable_indicator_iff measurableSet_Icc).mpr ?_
    refine (integrableOn_const (C := (1:ℝ)) ?_)
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall (fun t => ?_)
    by_cases hmem : t ∈ Set.Icc (-1:ℝ) 1
    · rw [Set.indicator_of_mem hmem]
      unfold jTailC; rw [Complex.norm_real]; exact jTail_abs_le_one t
    · rw [Set.indicator_of_notMem hmem]
      have : jTail t = 0 := by
        by_contra hne; exact hmem (support_jTail_subset (Function.mem_support.mpr hne))
      unfold jTailC; rw [this]; simp

/-- **`jTailC ∈ L²`** — same dominator route as `integrable_jTailC`. -/
theorem memLp_jTailC_two : MemLp jTailC 2 (volume : Measure ℝ) := by
  refine MemLp.mono' (g := Set.indicator (Set.Icc (-1:ℝ) 1) (fun _ => (1:ℝ)))
    (memLp_indicator_const 2 measurableSet_Icc (1:ℝ) (Or.inr ?_)) aesm_jTailC ?_
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall (fun t => ?_)
    by_cases hmem : t ∈ Set.Icc (-1:ℝ) 1
    · rw [Set.indicator_of_mem hmem]
      unfold jTailC; rw [Complex.norm_real, Real.norm_eq_abs]; exact jTail_abs_le_one t
    · rw [Set.indicator_of_notMem hmem]
      have : jTail t = 0 := by
        by_contra hne; exact hmem (support_jTail_subset (Function.mem_support.mpr hne))
      unfold jTailC; rw [this]; simp

/-- `jTailC` is even (`jTail` depends on `t` only through `|t|`, and vanishes at `0`). -/
theorem jTailC_even (t : ℝ) : jTailC (-t) = jTailC t := by
  unfold jTailC jTail
  rw [abs_neg]
  by_cases h1 : 1 ≤ |t|
  · simp [h1]
  · simp only [if_neg h1]
    by_cases h0 : t = 0
    · simp [h0]
    · rw [if_neg (by simpa using h0), if_neg h0]

/-- `fejerK` is even. -/
theorem fejerK_even (x : ℝ) : fejerK (-x) = fejerK x := by
  unfold fejerK
  by_cases h : x = 0
  · simp [h]
  · rw [if_neg (by simpa using h), if_neg h]
    have h1 : (Real.sin (π * -x) / π) ^ 2 = (Real.sin (π * x) / π) ^ 2 := by
      rw [mul_neg, Real.sin_neg]; ring
    have h2 : ((-x)⁻¹ : ℝ) ^ 2 = (x⁻¹) ^ 2 := by rw [inv_neg, neg_sq]
    rw [h1, h2]

/-- `deriv fejerK` is odd (the derivative of an even function). -/
theorem deriv_fejerK_odd (x : ℝ) : deriv fejerK (-x) = - deriv fejerK x := by
  have h : deriv (fun y => fejerK (-y)) x = - deriv fejerK (-x) := by
    simpa using (deriv_comp_neg (fun y => fejerK y) x)
  have he : (fun y => fejerK (-y)) = fejerK := funext (fun y => fejerK_even y)
  rw [he] at h; linarith [h]

/-- `gTail = ½·tailFn′` is even (`tailFn` odd ⟹ derivative even; via `deriv_tailFn`,
`fejerK` even, `deriv fejerK` odd). -/
theorem gTail_even (x : ℝ) : gTail (-x) = gTail x := by
  rw [gTail, gTail, VaalerGCesMemLpDischarge.deriv_tailFn, VaalerGCesMemLpDischarge.deriv_tailFn,
    fejerK_even, deriv_fejerK_odd]
  push_cast; ring

/-! ### §8.2 — `𝓕(jTailC) = gTail` (the inversion FTC, via `jTailC = boxC − fejerTriangle`) -/

/-- The complex indicator of `(-1, 1)` ("box"); its forward FT is `sin(2πx)/(πx)`. -/
private def boxC (t : ℝ) : ℂ :=
  Set.indicator (Set.Ioo (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℂ)) t

private theorem boxC_integrable : Integrable boxC (volume : Measure ℝ) := by
  unfold boxC
  rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioo]
  exact MeasureTheory.integrableOn_const (C := (1 : ℂ)) (by simp [Real.volume_Ioo])

private theorem boxC_fourier_zero : 𝓕 boxC 0 = (2 : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold boxC
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
  rw [MeasureTheory.integral_indicator_const (μ := volume) (s := Set.Ioo (-1 : ℝ) 1)
    (e := (1 : ℂ)) measurableSet_Ioo]
  rw [Real.volume_real_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num

private theorem boxC_fourier_ne_zero {x : ℝ} (hx : x ≠ 0) :
    𝓕 boxC x = ((Real.sin (2 * π * x) / (π * x) : ℝ) : ℂ) := by
  let c : ℂ := (((-2 * π * x : ℝ) : ℂ) * Complex.I)
  have hc : c ≠ 0 := by
    have hr : (-2 * π * x : ℝ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) Complex.I_ne_zero
  have hfour : 𝓕 boxC x = ∫ t in (-1 : ℝ)..1, Complex.exp (c * (t : ℂ)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    unfold boxC
    change (∫ v : ℝ,
        Complex.exp (↑(-2 * π * v * x) * Complex.I) •
          Set.indicator (Set.Ioo (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℂ)) v)
      = ∫ t in (-1 : ℝ)..1, Complex.exp (c * (t : ℂ))
    have hind :
        (fun v : ℝ =>
            Complex.exp (↑(-2 * π * v * x) * Complex.I) •
              Set.indicator (Set.Ioo (-1 : ℝ) 1) (fun _ : ℝ => (1 : ℂ)) v)
          = Set.indicator (Set.Ioo (-1 : ℝ) 1) (fun v : ℝ => Complex.exp (c * (v : ℂ))) := by
      funext v
      by_cases hv : v ∈ Set.Ioo (-1 : ℝ) 1
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
        simp only [smul_eq_mul, mul_one]; dsimp [c]; congr 1; push_cast; ring
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, smul_zero]
    rw [hind, MeasureTheory.integral_indicator measurableSet_Ioo]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo
      (f := fun t : ℝ => Complex.exp (c * (t : ℂ))) (μ := volume)]
    rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [hfour, integral_exp_mul_complex hc]
  dsimp [c]
  rw [show (((-2 * π * x : ℝ) : ℂ) * Complex.I) * (1 : ℂ)
      = ((-2 * π * x : ℝ) : ℂ) * Complex.I by ring]
  rw [show (((-2 * π * x : ℝ) : ℂ) * Complex.I) * ((-1 : ℝ) : ℂ)
      = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp [Real.cos_neg, Real.sin_neg]
  field_simp [hx, Real.pi_ne_zero, Complex.I_ne_zero]
  ring

/-- **`𝓕(boxC)(x) = sin(2πx)/(πx)`** (and `= 2` at `x = 0`). -/
private theorem boxC_fourier (x : ℝ) :
    𝓕 boxC x = ((if x = 0 then 2 else Real.sin (2 * π * x) / (π * x) : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · subst hx; rw [boxC_fourier_zero]; norm_num
  · rw [boxC_fourier_ne_zero hx, if_neg hx]

/-- **`gTail x = sin(2πx)/(πx) − fejerK x`** — the closed form matching `𝓕(jTailC)`.
At `x = 0`: `gTail 0 = fejerK 0 = 1 = 2 − 1`.  Off `0`: from `deriv_tailFn` /
`hasDerivAt_two_mul_id_fejerK_offZero` and `sin(2πx) = 2 sin πx cos πx`. -/
private theorem gTail_eq_box_minus_fejerK (x : ℝ) :
    gTail x = (((if x = 0 then 2 else Real.sin (2 * π * x) / (π * x)) - fejerK x : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · subst hx
    rw [gTail, VaalerGCesMemLpDischarge.deriv_tailFn,
      VaalerGRegularityProof.deriv_fejerK_zero,
      MathExtras.NumberTheory.Analysis.VaalerInterpHContinuous.fejerK_zero]
    norm_num
  · have hderiv :
        deriv tailFn x =
          2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (2 * x⁻¹)
            + (Real.sin (π * x) / π) ^ 2 * (2 * (-(x⁻¹ ^ 2))) := by
      rw [tailFn_eq_two_mul_id_fejerK]
      exact (VaalerGRegularityProof.hasDerivAt_two_mul_id_fejerK_offZero hx).deriv
    rw [gTail, hderiv, if_neg hx, fejerK, if_neg hx]
    congr 1
    rw [show 2 * π * x = 2 * (π * x) by ring, Real.sin_two_mul]
    field_simp [hx, Real.pi_ne_zero]; ring

/-- **`jTailC = boxC − (fejerTriangle : ℂ)`** pointwise
(`|t|·1_{|t|<1} = 1_{(-1,1)} − (1−|t|)₊`). -/
private theorem jTailC_eq_boxC_sub_fejerTriangle :
    jTailC = fun t : ℝ => boxC t - (MathExtras.Fourier.fejerTriangle t : ℂ) := by
  funext t
  rw [jTailC, jTail, boxC]
  by_cases ht : |t| < 1
  · have hnot : ¬ 1 ≤ |t| := not_le.mpr ht
    rw [if_neg hnot]
    have hmem : t ∈ Set.Ioo (-1 : ℝ) 1 := by
      rw [Set.mem_Ioo]; exact ⟨(abs_lt.mp ht).1, (abs_lt.mp ht).2⟩
    rw [Set.indicator_of_mem hmem]
    have htri : MathExtras.Fourier.fejerTriangle t = 1 - |t| :=
      MathExtras.Fourier.fejerTriangle_eq_one_sub_abs_of_abs_le_one (le_of_lt ht)
    by_cases ht0 : t = 0
    · rw [if_pos ht0, htri]; simp [ht0]
    · rw [if_neg ht0, htri]; push_cast; ring
  · have hge : 1 ≤ |t| := le_of_not_gt ht
    rw [if_pos hge]
    have hnotmem : t ∉ Set.Ioo (-1 : ℝ) 1 := by
      intro hmem
      exact (not_lt_of_ge hge) (abs_lt.mpr ⟨hmem.1, hmem.2⟩)
    rw [Set.indicator_of_notMem hnotmem,
      MathExtras.Fourier.fejerTriangle_eq_zero_of_one_le_abs hge]
    norm_num

/-- **PROVEN — the forward integral FT of `jTailC` is `gTail`.**

`𝓕(jTailC) = 𝓕(boxC) − 𝓕(fejerTriangle) = sin(2π·)/(π·) − fejerK = gTail`, using
`jTailC_eq_boxC_sub_fejerTriangle`, `boxC_fourier`, the committed
`SincSquare.fourier_fejerTriangle_eq_sincSqPi` + `VaalerFejerFT.fejerK_eq_sincSqPi`, and the
closed form `gTail_eq_box_minus_fejerK`.  This is the genuine analytic content of the tail
piece (computed via *inversion*, since `gTail ∉ L¹` blocks the forward derivative-multiplier). -/
theorem fourierIntegral_jTailC_eq_gTail : 𝓕 jTailC = gTail := by
  ext x
  have htriInt : Integrable (fun t : ℝ => (MathExtras.Fourier.fejerTriangle t : ℂ))
      (volume : Measure ℝ) := MathExtras.Fourier.fejerTriangle_integrable.ofReal
  have hsplit :
      𝓕 jTailC x = 𝓕 boxC x - 𝓕 (fun t : ℝ => (MathExtras.Fourier.fejerTriangle t : ℂ)) x := by
    rw [jTailC_eq_boxC_sub_fejerTriangle]
    rw [Real.fourier_real_eq, Real.fourier_real_eq, Real.fourier_real_eq]
    simp only [smul_sub]
    change (∫ v : ℝ,
        (𝐞 (-(v * x)) • boxC v) - (𝐞 (-(v * x)) • (MathExtras.Fourier.fejerTriangle v : ℂ)))
      = (∫ v : ℝ, 𝐞 (-(v * x)) • boxC v)
          - ∫ v : ℝ, 𝐞 (-(v * x)) • (MathExtras.Fourier.fejerTriangle v : ℂ)
    rw [MeasureTheory.integral_sub]
    · simpa [Real.inner_apply, mul_comm] using
        (Real.fourierIntegral_convergent_iff x).2 boxC_integrable
    · simpa [Real.inner_apply, mul_comm] using
        (Real.fourierIntegral_convergent_iff x).2 htriInt
  rw [hsplit, boxC_fourier x, MathExtras.Fourier.fourier_fejerTriangle_eq_sincSqPi x,
    ← MathExtras.NumberTheory.Analysis.VaalerFejerFT.fejerK_eq_sincSqPi x]
  rw [← Complex.ofReal_sub]
  exact (gTail_eq_box_minus_fejerK x).symm

/-! ### §8.3 — The inverse `L¹∩L²` Fourier bridge (Mathlib-gap sibling of the forward one)

Mirror of `FourierL1L2Agreement.fourierIntegral_ae_eq_fourierTransformₗᵢ` for the *inverse*
transform: `⇑(𝓕_Lp.symm (toLp f)) =ᵐ 𝓕⁻ f` on `L¹∩L²`.  Same distributional test-function
route (`ae_eq_of_integral_contDiff_smul_eq`), via `Lp.fourierInv_toTemperedDistribution_eq` /
`TemperedDistribution.fourierInv_apply`, with the inverse multiplication formula derived from the
proven forward one by the reflection `𝓕⁻ h = 𝓕 (h ∘ neg)` (`Real.fourierInv_eq_fourier_comp_neg`)
and the `x ↦ -x` change of variables. -/

private theorem fourierInvTransformₗᵢ_test_eq (T : Lp (α := ℝ) ℂ 2) (G : 𝓢(ℝ, ℂ)) :
    ((𝓕⁻ T : Lp (α := ℝ) ℂ 2) : 𝓢'(ℝ, ℂ)) G = ∫ x : ℝ, (𝓕⁻ G) x • (T : ℝ → ℂ) x := by
  rw [← MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq T]
  rw [TemperedDistribution.fourierInv_apply]
  rw [MeasureTheory.Lp.toTemperedDistribution_apply]

private theorem integral_fourierInv_schwartz_smul_eq (f : ℝ → ℂ) (hf : Integrable f)
    (g : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, (𝓕⁻ (fun y => g y)) x • f x) = ∫ ξ : ℝ, (g ξ) • (𝓕⁻ f) ξ := by
  let gneg : 𝓢(ℝ, ℂ) :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ))) g
  have hgneg : ∀ y : ℝ, gneg y = g (-y) := fun y => rfl
  calc
    (∫ x : ℝ, (𝓕⁻ (fun y => g y)) x • f x)
        = ∫ x : ℝ, (𝓕 (fun y : ℝ => (g : ℝ → ℂ) (-y))) x • f x := by
          rw [Real.fourierInv_eq_fourier_comp_neg (fun y : ℝ => (g : ℝ → ℂ) y)]
    _ = ∫ ξ : ℝ, (g (-ξ)) • (𝓕 f) ξ := by
          rw [show (fun y : ℝ => (g : ℝ → ℂ) (-y)) = fun y : ℝ => gneg y by
            funext y; exact (hgneg y).symm]
          simpa [hgneg] using
            MathExtras.NumberTheory.Analysis.FourierL1L2Agreement.integral_fourier_schwartz_smul_eq
              f hf gneg
    _ = ∫ ξ : ℝ, (g ξ) • (𝓕 f) (-ξ) := by
          have h := integral_neg_eq_self (fun ξ : ℝ => (g ξ) * (𝓕 f) (-ξ)) volume
          simp_rw [neg_neg] at h
          simpa [smul_eq_mul] using h
    _ = ∫ ξ : ℝ, (g ξ) • (𝓕⁻ f) ξ := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          rw [Real.fourierInv_eq_fourier_neg f ξ]

private theorem continuous_fourierInv_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕⁻ f) := by
  have hcont : Continuous (fun x : ℝ => 𝓕 f (-x)) :=
    (MathExtras.NumberTheory.Analysis.FourierL1L2Agreement.continuous_fourier_of_integrable
      hf).comp continuous_neg
  convert hcont using 1
  ext x; exact Real.fourierInv_eq_fourier_neg f x

/-- **PROVEN — the inverse `L¹∩L²` Fourier bridge.**  For `f ∈ L¹∩L²`, the representative of the
Plancherel inverse `𝓕_Lp.symm` on `toLp f` agrees a.e. with the integral inverse transform `𝓕⁻ f`.
The `𝓕`-sibling of `FourierL1L2Agreement.fourierIntegral_ae_eq_fourierTransformₗᵢ`. -/
theorem fourierIntegralInv_ae_eq_fourierTransformₗᵢ_symm {f : ℝ → ℂ}
    (hf : Integrable f) (hf2 : MemLp f 2) :
    (⇑((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm (hf2.toLp f)) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ f := by
  set T : Lp (α := ℝ) ℂ 2 := hf2.toLp f with hT
  have hTf : (T : ℝ → ℂ) =ᵐ[volume] f := hf2.coeFn_toLp
  have hf1_li : LocallyIntegrable
      (⇑((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm T) : ℝ → ℂ) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hf2_li : LocallyIntegrable (𝓕⁻ f) volume :=
    (continuous_fourierInv_of_integrable hf).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hf1_li hf2_li ?_
  intro g g_smooth g_cpt
  have hG₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
  have hG₂ : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ g) := by fun_prop
  set G : 𝓢(ℝ, ℂ) := hG₁.toSchwartzMap hG₂ with hG
  have hGval : ∀ x, (G : ℝ → ℂ) x = ((g x : ℝ) : ℂ) := fun x => rfl
  have hscal : ∀ (x : ℝ) (y : ℂ), (G : ℝ → ℂ) x • y = g x • y := by
    intro x y; rw [hGval x]; simp [Complex.real_smul]
  have hpair := fourierInvTransformₗᵢ_test_eq T G
  rw [MeasureTheory.Lp.toTemperedDistribution_apply] at hpair
  calc
    (∫ x : ℝ, g x • (⇑((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm T) : ℝ → ℂ) x)
        = ∫ x : ℝ, (G : ℝ → ℂ) x •
            (⇑((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm T) : ℝ → ℂ) x :=
          integral_congr_ae (Filter.Eventually.of_forall (fun x => (hscal x _).symm))
    _ = ∫ x : ℝ, (𝓕⁻ G) x • (T : ℝ → ℂ) x := hpair
    _ = ∫ x : ℝ, (𝓕⁻ (fun y => (G : ℝ → ℂ) y)) x • (T : ℝ → ℂ) x := by
          rw [SchwartzMap.fourierInv_coe G]
    _ = ∫ x : ℝ, (𝓕⁻ (fun y => (G : ℝ → ℂ) y)) x • f x := by
          refine integral_congr_ae ?_
          filter_upwards [hTf] with x hx; rw [hx]
    _ = ∫ ξ : ℝ, (G : ℝ → ℂ) ξ • (𝓕⁻ f) ξ :=
          integral_fourierInv_schwartz_smul_eq f hf G
    _ = ∫ x : ℝ, g x • 𝓕⁻ f x :=
          integral_congr_ae (Filter.Eventually.of_forall (fun x => hscal x _))

/-! ### §8.4 — Assembly: the `L²`-only TAIL FT identity `tailFT_eq_jTail` -/

/-- **PROVEN — `TailFTeqJtail`.**  The Plancherel `L²`-transform of the (non-`L¹`) tail piece
`gTail = ½·tailFn′` equals `jTailC` a.e.:

    `⇑(𝓕_Lp gTail) =ᵐ jTailC`.

Route (inversion): `𝓕⁻(jTailC) = 𝓕(jTailC)(−·) = gTail` (forward FTC
`fourierIntegral_jTailC_eq_gTail` + evenness `jTailC`/`gTail`); the inverse `L¹∩L²` bridge
`fourierIntegralInv_ae_eq_fourierTransformₗᵢ_symm` gives `𝓕_Lp.symm (toLp jTailC) = toLp gTail`;
applying the Plancherel isometry `𝓕_Lp` yields `𝓕_Lp (toLp gTail) = toLp jTailC`. -/
theorem tailFT_eq_jTail : TailFTeqJtail := by
  intro h
  set F := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ with hF
  have hInvEq : (𝓕⁻ jTailC) = gTail := by
    funext x
    rw [Real.fourierInv_eq_fourier_neg, fourierIntegral_jTailC_eq_gTail, gTail_even]
  have hInvBridge :=
    fourierIntegralInv_ae_eq_fourierTransformₗᵢ_symm integrable_jTailC memLp_jTailC_two
  have hsymm_ae : (⇑(F.symm (memLp_jTailC_two.toLp jTailC)) : ℝ → ℂ) =ᵐ[volume] gTail := by
    rw [hInvEq] at hInvBridge; exact hInvBridge
  have hsymm_lp : F.symm (memLp_jTailC_two.toLp jTailC) = h.toLp gTail := by
    apply MeasureTheory.Lp.ext
    exact hsymm_ae.trans (h.coeFn_toLp).symm
  have hkey : memLp_jTailC_two.toLp jTailC = F (h.toLp gTail) := by
    have := congrArg F hsymm_lp; rwa [F.apply_symm_apply] at this
  have hfinal : (⇑(F (h.toLp gTail)) : ℝ → ℂ) =ᵐ[volume] jTailC := by
    rw [← hkey]; exact memLp_jTailC_two.coeFn_toLp
  exact hfinal

#print axioms fourierIntegral_jTailC_eq_gTail
#print axioms fourierIntegralInv_ae_eq_fourierTransformₗᵢ_symm
#print axioms tailFT_eq_jTail

end MathExtras.NumberTheory.Analysis.VaalerCesaroFTPieces
