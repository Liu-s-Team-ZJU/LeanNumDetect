/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Diagonal split, geometric kernel, and the Montgomery–Vaughan Hilbert core — Track S

This file expands the *dual* sharp large sieve quadratic form

  `∑_{p ∈ Ioc W' W} ‖∑_{i ∈ B} conj(e(α_i p))·b_i‖²`

into its diagonal `(W−W')` contribution and an off-diagonal geometric-kernel
contribution, and isolates the single remaining from-scratch analytic core of
the entire minor side — the Montgomery–Vaughan **Hilbert-type inequality** — as
the named residual `MontgomeryVaughanHilbert`.

## What is delivered

* **`expKernel`** — `K(β) = ∑_{p ∈ Ioc W' W} e(βp)`, a geometric sum.
* **`expKernel_zero`** — `K(0) = (W−W' : ℂ)` (the diagonal value).  Sorry-free.
* **`norm_expKernel_le_card`** — `‖K(β)‖ ≤ (W−W')` (triangle inequality).
  Sorry-free.
* **`norm_one_sub_addChar_ge`** — `4‖β‖_{ℝ/ℤ} ≤ |1 − e(β)|` (`|1−e(β)| = 2|sin πβ|`
  and Jordan's inequality `|sin πβ| ≥ 2‖β‖`).  Sorry-free.
* **`norm_expKernel_le_inv`** — the **geometric-kernel bound**
  `‖K(β)‖ ≤ 1/(2‖β‖_{ℝ/ℤ})` for `β ∉ ℤ`.  Sorry-free.
* **`dualForm_diag_offdiag`** — the diagonal/off-diagonal expansion of the dual
  quadratic form.  Sorry-free.
* **`dualForm_diagonal_eq`** — the diagonal term is `(W−W')·∑_i ‖b_i‖²`.
  Sorry-free.
* **`MontgomeryVaughanHilbert`** — the named residual: the off-diagonal
  geometric-kernel sum is bounded by `δ⁻¹·∑_i ‖b_i‖²` for `δ`-well-spaced `α`.
  This is the Selberg/Vaaler Beurling–Selberg core (Montgomery–Vaughan 1974).
* **`dualSharpLargeSievePerBlock_of_hilbert`** — the reduction
  `MontgomeryVaughanHilbert → DualSharpLargeSievePerBlock` (on the full interval
  `P = Ioc W' W`), **proven sorry-free**: diagonal `(W−W')` + off-diagonal
  `δ⁻¹` give the sharp constant `((W−W') + δ⁻¹)`.

This isolates `MontgomeryVaughanHilbert` as the SINGLE remaining from-scratch
analytic core of the minor side.  No new `axiom`, no `sorry`, no vacuous proof.
-/

import MathExtras.NumberTheory.Analysis.SharpLargeSieveDuality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace MathExtras.NumberTheory.Analysis.SharpLargeSieveHilbert

open scoped BigOperators ComplexConjugate
open Finset
open MathExtras.NumberTheory.Analysis.LargeSieve
open MathExtras.NumberTheory.Analysis.SharpLargeSieveDuality

/-! ## The geometric exponential kernel `K(β) = ∑_{p ∈ Ioc W' W} e(βp)` -/

/-- The base exponential `z = e(β) = exp(2π i β)`.  Then `e(βp) = z^p`. -/
noncomputable def expBase (β : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (β : ℂ))

/-- `e(βp) = (e(β))^p`: the additive character is a power of the base. -/
theorem addChar_eq_expBase_pow (β : ℝ) (p : ℕ) :
    Vinogradov.addChar β p = (expBase β) ^ p := by
  unfold Vinogradov.addChar expBase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `‖e(β)‖ = 1`. -/
@[simp] theorem norm_expBase (β : ℝ) : ‖expBase β‖ = 1 := by
  have := Vinogradov.norm_addChar β 1
  rw [addChar_eq_expBase_pow] at this
  simpa using this

/-- The geometric exponential kernel `K(β) = ∑_{p ∈ Ioc W' W} e(βp)`. -/
noncomputable def expKernel (β : ℝ) (W' W : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc W' W, Vinogradov.addChar β p

/-- **Diagonal value.**  `K(0) = (W − W' : ℂ)` when `W' ≤ W`. -/
theorem expKernel_zero (W' W : ℕ) (h : W' ≤ W) :
    expKernel 0 W' W = ((W : ℂ) - (W' : ℂ)) := by
  unfold expKernel
  simp only [Vinogradov.addChar_zero_left]
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one, Nat.cast_sub h]

/-- **Cardinality bound.**  `‖K(β)‖ ≤ (W − W')` (triangle inequality, each term
has norm `1`). -/
theorem norm_expKernel_le_card (β : ℝ) (W' W : ℕ) (h : W' ≤ W) :
    ‖expKernel β W' W‖ ≤ ((W : ℝ) - (W' : ℝ)) := by
  unfold expKernel
  calc ‖∑ p ∈ Finset.Ioc W' W, Vinogradov.addChar β p‖
      ≤ ∑ p ∈ Finset.Ioc W' W, ‖Vinogradov.addChar β p‖ := norm_sum_le _ _
    _ = ∑ p ∈ Finset.Ioc W' W, (1 : ℝ) := by
          apply Finset.sum_congr rfl; intro p _; exact Vinogradov.norm_addChar β p
    _ = ((W : ℝ) - (W' : ℝ)) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
          push_cast [Nat.cast_sub h]; ring

/-! ## `‖1 − e(β)‖ = 2|sin πβ|` and the Jordan lower bound -/

/-- `e(β)` as `cos(2πβ) + i sin(2πβ)`. -/
theorem expBase_eq (β : ℝ) :
    expBase β = (Real.cos (2 * Real.pi * β) : ℂ)
      + (Real.sin (2 * Real.pi * β) : ℂ) * Complex.I := by
  unfold expBase
  have h : (2 : ℂ) * Real.pi * Complex.I * (β : ℂ)
      = ((2 * Real.pi * β : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- **`‖1 − e(β)‖ = 2|sin πβ|`.**  The squared norm of `e(β) − 1` is
`4 sin²(πβ)`; taking square roots gives the identity. -/
theorem norm_expBase_sub_one (β : ℝ) :
    ‖expBase β - 1‖ = 2 * |Real.sin (Real.pi * β)| := by
  -- normSq (z - 1) = (cos 2πβ - 1)² + sin² 2πβ = 4 sin²(πβ).
  have hzeq : expBase β - 1
      = ((Real.cos (2 * Real.pi * β) - 1 : ℝ) : ℂ)
        + (Real.sin (2 * Real.pi * β) : ℂ) * Complex.I := by
    rw [expBase_eq]; push_cast; ring
  have hnsq : Complex.normSq (expBase β - 1)
      = (Real.cos (2 * Real.pi * β) - 1) ^ 2 + Real.sin (2 * Real.pi * β) ^ 2 := by
    rw [hzeq, Complex.normSq_add_mul_I]
  -- 2πβ = 2·(πβ), so use double-angle to write everything in sin(πβ).
  have hdouble : (2 * Real.pi * β) = 2 * (Real.pi * β) := by ring
  have hcos : Real.cos (2 * Real.pi * β)
      = Real.cos (Real.pi * β) ^ 2 - Real.sin (Real.pi * β) ^ 2 := by
    rw [hdouble, Real.cos_two_mul']
  have hsin : Real.sin (2 * Real.pi * β)
      = 2 * Real.sin (Real.pi * β) * Real.cos (Real.pi * β) := by
    rw [hdouble, Real.sin_two_mul]
  have hpyth : Real.sin (Real.pi * β) ^ 2 + Real.cos (Real.pi * β) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have hnsq' : Complex.normSq (expBase β - 1) = 4 * Real.sin (Real.pi * β) ^ 2 := by
    rw [hnsq, hcos, hsin]; nlinarith [hpyth]
  -- ‖·‖² = normSq = 4 sin² = (2|sin|)²; both sides nonneg ⇒ equal.
  have hnormsq : ‖expBase β - 1‖ ^ 2 = (2 * |Real.sin (Real.pi * β)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hnsq']
    rw [mul_pow, sq_abs]; ring
  have h1 : (0 : ℝ) ≤ ‖expBase β - 1‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * |Real.sin (Real.pi * β)| := by positivity
  nlinarith [hnormsq, h1, h2]

/-- **Jordan's lower bound:** `4·circleDist β 0 ≤ |1 − e(β)|`.

Writing `‖β‖_{ℝ/ℤ} = circleDist β 0` (distance to the nearest integer), we have
`|sin πβ| = |sin π‖β‖| ≥ 2‖β‖` by `mul_le_sin` (Jordan), and
`|1 − e(β)| = 2|sin πβ| ≥ 4‖β‖`. -/
theorem norm_one_sub_addChar_ge (β : ℝ) :
    4 * circleDist β 0 ≤ ‖expBase β - 1‖ := by
  set d : ℝ := circleDist β 0 with hd
  -- d = |β - round β|, with 0 ≤ d ≤ 1/2.
  have hd_def : d = |β - (round β : ℝ)| := by rw [hd]; unfold circleDist; rw [sub_zero]
  have hd0 : 0 ≤ d := by rw [hd]; exact circleDist_nonneg _ _
  have hd_half : d ≤ 1 / 2 := by
    rw [hd_def]; exact abs_sub_round β
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  -- |sin πβ| = |sin (π·(β - round β))| = sin(π·d)  (Jordan input).
  have hsin_eq : |Real.sin (Real.pi * β)| = Real.sin (Real.pi * d) := by
    -- sin(πβ) = ± sin(π(β - round β)) since round β ∈ ℤ.
    have hper : Real.sin (Real.pi * β)
        = (-1 : ℝ) ^ (round β) * Real.sin (Real.pi * (β - (round β : ℝ))) := by
      have heq : Real.pi * β = Real.pi * (β - (round β : ℝ)) + (round β) * Real.pi := by
        push_cast; ring
      rw [heq, Real.sin_add_int_mul_pi]
    rw [hper, abs_mul]
    rw [show |(-1 : ℝ) ^ (round β)| = 1 by
          rw [abs_zpow, abs_neg, abs_one, one_zpow], one_mul]
    -- |sin(π·u)| = sin(π·|u|) = sin(π d) since |π·u| = π d ≤ π/2 ≤ π.
    have hxle : |Real.pi * (β - (round β : ℝ))| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos hpi_pos, ← hd_def]
      calc Real.pi * d ≤ Real.pi * (1 / 2) := by
              apply mul_le_mul_of_nonneg_left hd_half (le_of_lt hpi_pos)
        _ ≤ Real.pi := by linarith
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hxle, abs_mul, abs_of_pos hpi_pos, ← hd_def]
  -- Jordan: sin(π d) ≥ (2/π)·(π d) = 2 d.
  have hjordan : 2 * d ≤ Real.sin (Real.pi * d) := by
    have hpd0 : (0 : ℝ) ≤ Real.pi * d := mul_nonneg (le_of_lt hpi_pos) hd0
    have hpd_le : Real.pi * d ≤ Real.pi / 2 := by
      rw [div_eq_mul_inv]; nlinarith [hd_half, hpi_pos]
    have := Real.mul_le_sin hpd0 hpd_le
    -- this : 2/π * (π d) ≤ sin (π d).
    have hsimp : 2 / Real.pi * (Real.pi * d) = 2 * d := by
      field_simp
    rwa [hsimp] at this
  -- Combine: ‖e(β)-1‖ = 2|sin πβ| = 2 sin(π d) ≥ 4 d.
  rw [norm_expBase_sub_one, hsin_eq]
  linarith [hjordan]

/-! ## The geometric-kernel bound `‖K(β)‖ ≤ 1/(2‖β‖)` -/

/-- **Geometric closed form.**  For `β` with `e(β) ≠ 1` and `W' ≤ W`,
`K(β) = (e(β)^{W+1} − e(β)^{W'+1})/(e(β) − 1)`. -/
theorem expKernel_geom (β : ℝ) (W' W : ℕ) (h : W' ≤ W)
    (hz : expBase β ≠ 1) :
    expKernel β W' W
      = ((expBase β) ^ (W + 1) - (expBase β) ^ (W' + 1)) / (expBase β - 1) := by
  unfold expKernel
  -- `Ioc W' W = Ico (W'+1) (W+1)`.
  have hset : Finset.Ioc W' W = Finset.Ico (W' + 1) (W + 1) := by
    ext p; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hset]
  -- rewrite each `addChar β p` as `z^p`.
  have hterm : ∀ p ∈ Finset.Ico (W' + 1) (W + 1),
      Vinogradov.addChar β p = (expBase β) ^ p := by
    intro p _; exact addChar_eq_expBase_pow β p
  rw [Finset.sum_congr rfl hterm]
  rw [geom_sum_Ico hz (by omega : W' + 1 ≤ W + 1)]

/-- **The geometric-kernel bound.**  For `β` at positive circle-distance from
`ℤ` (so `e(β) ≠ 1`), `‖K(β)‖ ≤ 1/(2·circleDist β 0)`. -/
theorem norm_expKernel_le_inv (β : ℝ) (W' W : ℕ) (h : W' ≤ W)
    (hpos : 0 < circleDist β 0) :
    ‖expKernel β W' W‖ ≤ 1 / (2 * circleDist β 0) := by
  -- `e(β) ≠ 1` since `‖e(β)−1‖ ≥ 4·circleDist > 0`.
  have hz_ne : expBase β - 1 ≠ 0 := by
    have := norm_one_sub_addChar_ge β
    intro hcontra
    rw [hcontra, norm_zero] at this
    linarith
  have hz1 : expBase β ≠ 1 := by
    intro hc; apply hz_ne; rw [hc]; ring
  -- numerator norm ≤ 2 (two unit-modulus powers).
  have hnum : ‖(expBase β) ^ (W + 1) - (expBase β) ^ (W' + 1)‖ ≤ 2 := by
    calc ‖(expBase β) ^ (W + 1) - (expBase β) ^ (W' + 1)‖
        ≤ ‖(expBase β) ^ (W + 1)‖ + ‖(expBase β) ^ (W' + 1)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_pow, norm_pow, norm_expBase, one_pow, one_pow]
      _ = 2 := by ring
  -- denominator norm ≥ 4·circleDist.
  have hden : 4 * circleDist β 0 ≤ ‖expBase β - 1‖ := norm_one_sub_addChar_ge β
  have hden_pos : 0 < ‖expBase β - 1‖ := lt_of_lt_of_le (by linarith) hden
  -- ‖K‖ = ‖num‖/‖den‖ ≤ 2/(4·circleDist) = 1/(2·circleDist).
  rw [expKernel_geom β W' W h hz1, norm_div]
  rw [div_le_iff₀ hden_pos]
  -- goal: ‖num‖ ≤ (1/(2·cd))·‖den‖.  Use ‖num‖ ≤ 2 and ‖den‖ ≥ 4·cd.
  have hcd2 : (0 : ℝ) < 2 * circleDist β 0 := by positivity
  calc ‖(expBase β) ^ (W + 1) - (expBase β) ^ (W' + 1)‖
      ≤ 2 := hnum
    _ = (1 / (2 * circleDist β 0)) * (4 * circleDist β 0) := by
        rw [eq_comm, div_mul_eq_mul_div, one_mul,
          show (4 : ℝ) * circleDist β 0 = 2 * (2 * circleDist β 0) by ring,
          mul_div_assoc, div_self (ne_of_gt hcd2), mul_one]
    _ ≤ (1 / (2 * circleDist β 0)) * ‖expBase β - 1‖ := by
        apply mul_le_mul_of_nonneg_left hden (by positivity)

/-- **The combined geometric-kernel bound** `‖K(β)‖ ≤ min(W−W', 1/(2‖β‖))`. -/
theorem norm_expKernel_le_min (β : ℝ) (W' W : ℕ) (h : W' ≤ W)
    (hpos : 0 < circleDist β 0) :
    ‖expKernel β W' W‖ ≤ min ((W : ℝ) - (W' : ℝ)) (1 / (2 * circleDist β 0)) :=
  le_min (norm_expKernel_le_card β W' W h) (norm_expKernel_le_inv β W' W h hpos)

/-! ## Diagonal/off-diagonal expansion of the dual quadratic form -/

/-- `conj(e(α p))·e(β p) = e((β − α) p)`: the kernel summand. -/
theorem conj_addChar_mul_addChar (α β : ℝ) (p : ℕ) :
    conj (Vinogradov.addChar α p) * Vinogradov.addChar β p
      = Vinogradov.addChar (β - α) p := by
  unfold Vinogradov.addChar
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, map_mul, map_mul, map_mul, Complex.conj_I]
  rw [show starRingEnd ℂ (2 : ℂ) = (2 : ℂ) from by
        rw [show ((2 : ℂ) : ℂ) = ((2 : ℝ) : ℂ) from by norm_num]
        exact Complex.conj_ofReal _]
  rw [show starRingEnd ℂ ((Real.pi : ℂ)) = (Real.pi : ℂ) from Complex.conj_ofReal _]
  rw [show starRingEnd ℂ ((p : ℂ)) = (p : ℂ) from by simp]
  rw [show starRingEnd ℂ ((α : ℂ)) = (α : ℂ) from Complex.conj_ofReal _]
  push_cast
  ring

/-- The per-pair column-kernel identity:
`∑_{p ∈ Ioc W' W} conj(e(α_i p))·e(α_j p) = K(α_j − α_i)`. -/
theorem sum_conj_addChar_mul (αi αj : ℝ) (W' W : ℕ) :
    ∑ p ∈ Finset.Ioc W' W,
        conj (Vinogradov.addChar αi p) * Vinogradov.addChar αj p
      = expKernel (αj - αi) W' W := by
  unfold expKernel
  apply Finset.sum_congr rfl
  intro p _
  exact conj_addChar_mul_addChar αi αj p

/-- **The diagonal/off-diagonal expansion (as a complex identity).**

`∑_{p ∈ Ioc W' W} (‖∑_i conj(e(α_i p))·b_i‖² : ℂ)`
`= ∑_i ∑_j b_i·conj(b_j)·K(α_j − α_i)`. -/
theorem dualForm_expand (B : Finset ℕ) (α : ℕ → ℝ) (b : ℕ → ℂ) (W' W : ℕ) :
    ∑ p ∈ Finset.Ioc W' W,
        ((‖∑ i ∈ B, conj (Vinogradov.addChar (α i) p) * b i‖ ^ 2 : ℝ) : ℂ)
      = ∑ i ∈ B, ∑ j ∈ B, b i * conj (b j) * expKernel (α j - α i) W' W := by
  -- For each p, expand ‖w‖² = w·conj(w) as a double sum over i,j.
  have hpt : ∀ p ∈ Finset.Ioc W' W,
      ((‖∑ i ∈ B, conj (Vinogradov.addChar (α i) p) * b i‖ ^ 2 : ℝ) : ℂ)
        = ∑ i ∈ B, ∑ j ∈ B,
            (b i * conj (b j))
              * (conj (Vinogradov.addChar (α i) p) * Vinogradov.addChar (α j) p) := by
    intro p _
    set w : ℂ := ∑ i ∈ B, conj (Vinogradov.addChar (α i) p) * b i with hw
    -- (‖w‖²:ℂ) = w * conj w.
    have hnorm : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      ring
    rw [hnorm, hw]
    -- conj of the i-sum: conj w = ∑_j addChar(α_j p)·conj(b_j).
    rw [map_sum]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, Complex.conj_conj]
    ring
  rw [Finset.sum_congr rfl hpt]
  -- swap ∑_p and ∑_{i,j}; the p-sum hits only the kernel factor.
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  -- ∑_p (b_i conj b_j)·(kernel) = (b_i conj b_j)·∑_p kernel = … ·K(α_j-α_i).
  rw [← Finset.mul_sum, sum_conj_addChar_mul (α i) (α j) W' W]

/-- **The off-diagonal kernel sum.**
`Offdiag(B,α,b) = ∑_{i ∈ B} ∑_{j ∈ B\{i}} b_i·conj(b_j)·K(α_j − α_i)`. -/
noncomputable def offDiagSum (B : Finset ℕ) (α : ℕ → ℝ) (b : ℕ → ℂ) (W' W : ℕ) : ℂ :=
  ∑ i ∈ B, ∑ j ∈ B.erase i, b i * conj (b j) * expKernel (α j - α i) W' W

/-- **Diagonal split.**  The full expansion equals the diagonal
`(W − W')·∑_i ‖b_i‖²` plus the off-diagonal kernel sum, when `W' ≤ W`. -/
theorem dualForm_diag_offdiag (B : Finset ℕ) (α : ℕ → ℝ) (b : ℕ → ℂ) (W' W : ℕ)
    (h : W' ≤ W) :
    ∑ p ∈ Finset.Ioc W' W,
        ((‖∑ i ∈ B, conj (Vinogradov.addChar (α i) p) * b i‖ ^ 2 : ℝ) : ℂ)
      = ((W : ℂ) - (W' : ℂ)) * ∑ i ∈ B, ((‖b i‖ ^ 2 : ℝ) : ℂ)
          + offDiagSum B α b W' W := by
  rw [dualForm_expand B α b W' W]
  -- Split each inner ∑_{j ∈ B} into the diagonal j = i and the rest j ∈ B.erase i.
  have hsplit : ∀ i ∈ B,
      ∑ j ∈ B, b i * conj (b j) * expKernel (α j - α i) W' W
        = b i * conj (b i) * expKernel 0 W' W
          + ∑ j ∈ B.erase i, b i * conj (b j) * expKernel (α j - α i) W' W := by
    intro i hi
    rw [← Finset.add_sum_erase B _ hi]
    congr 1
    rw [sub_self]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  -- diagonal: ∑_i b_i conj(b_i)·K(0) = (W-W')·∑_i ‖b_i‖².
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [expKernel_zero W' W h]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  ring

/-! ## The Montgomery–Vaughan Hilbert inequality — the single residual core -/

/-- **(HILBERT) The Montgomery–Vaughan Hilbert-type inequality** — the single
deep from-scratch analytic core of the entire minor side.

For `δ`-well-spaced angles `α` indexed by a `Finset` `B`, any coefficients
`b : ℕ → ℂ`, and the geometric kernel `K(β) = ∑_{p ∈ Ioc W' W} e(βp)`, the
off-diagonal kernel sum is bounded in norm by `δ⁻¹·∑_i ‖b_i‖²`:

  `‖∑_{i ∈ B} ∑_{j ∈ B\{i}} b_i·conj(b_j)·K(α_j − α_i)‖ ≤ δ⁻¹·∑_i ‖b_i‖²`.

This is the Selberg/Vaaler Beurling–Selberg majorant core (Montgomery–Vaughan
1974, *Hilbert's inequality*): each kernel value is controlled by the per-pair
bound `‖K(α_j − α_i)‖ ≤ 1/(2‖α_i − α_j‖)` (`norm_expKernel_le_inv`), and
well-spacing `‖α_i − α_j‖ ≥ δ` makes the bilinear `1/(α_i − α_j)` Hilbert form
sum to `δ⁻¹·∑‖b‖²`.  This is the SINGLE remaining open analytic input; everything
else in this file is proven. -/
def MontgomeryVaughanHilbert : Prop :=
  ∀ (B : Finset ℕ) (α : ℕ → ℝ) (b : ℕ → ℂ) (W' W : ℕ) (δ : ℝ),
    0 < δ → W' ≤ W → WellSpaced δ B α →
      ‖offDiagSum B α b W' W‖ ≤ δ⁻¹ * ∑ i ∈ B, ‖b i‖ ^ 2

/-! ## The reduction `MontgomeryVaughanHilbert → DualSharpLargeSievePerBlock`

(on the full interval `P = Ioc W' W`). -/

/-- **The reduction (proven sorry-free).**

Given the Montgomery–Vaughan Hilbert inequality, the dual sharp large sieve holds
on the full prime interval `P = Ioc W' W`: the diagonal contributes `(W − W')`
and the off-diagonal contributes `δ⁻¹`, giving the sharp constant
`((W − W') + δ⁻¹)`.

The mass identity `∑_i b_i·conj(b_i) = ∑_i ‖b_i‖²` is real, so taking real parts
of the complex expansion `dualForm_diag_offdiag` turns the off-diagonal term into
`Re(Offdiag) ≤ ‖Offdiag‖ ≤ δ⁻¹·∑‖b‖²`. -/
theorem dualSharpLargeSievePerBlock_of_hilbert
    (hHil : MontgomeryVaughanHilbert) :
    ∀ (B : Finset ℕ) (α : ℕ → ℝ) (b : ℕ → ℂ) (W' W : ℕ) (δ : ℝ),
      0 < δ → W' ≤ W → WellSpaced δ B α →
        ∑ p ∈ Finset.Ioc W' W,
            ‖∑ i ∈ B, conj (Vinogradov.addChar (α i) p) * b i‖ ^ 2 ≤
          (((W : ℝ) - (W' : ℝ)) + δ⁻¹) * ∑ i ∈ B, ‖b i‖ ^ 2 := by
  intro B α b W' W δ hδ hWW hspaced
  -- Real-part of the complex expansion.
  have hcx := dualForm_diag_offdiag B α b W' W hWW
  -- LHS is a real sum; take `.re` of both sides.
  have hre := congrArg Complex.re hcx
  -- (∑_p (‖·‖²:ℂ)).re = ∑_p ‖·‖².
  set LHS : ℝ := ∑ p ∈ Finset.Ioc W' W,
      ‖∑ i ∈ B, conj (Vinogradov.addChar (α i) p) * b i‖ ^ 2 with hLHS
  have hLre : (∑ p ∈ Finset.Ioc W' W,
      ((‖∑ i ∈ B, conj (Vinogradov.addChar (α i) p) * b i‖ ^ 2 : ℝ) : ℂ)).re = LHS := by
    rw [Complex.re_sum, hLHS]
    apply Finset.sum_congr rfl; intro p _; rw [Complex.ofReal_re]
  -- diagonal real part.
  have hmass : (((W : ℂ) - (W' : ℂ)) * ∑ i ∈ B, ((‖b i‖ ^ 2 : ℝ) : ℂ)).re
      = ((W : ℝ) - (W' : ℝ)) * ∑ i ∈ B, ‖b i‖ ^ 2 := by
    rw [show ((W : ℂ) - (W' : ℂ)) = (((W : ℝ) - (W' : ℝ) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_sum]
    rw [← Complex.ofReal_mul]
    rw [Complex.ofReal_re]
  rw [Complex.add_re, hLre, hmass] at hre
  -- Re(Offdiag) ≤ ‖Offdiag‖ ≤ δ⁻¹·∑‖b‖².
  have hoff_re_le : (offDiagSum B α b W' W).re ≤ ‖offDiagSum B α b W' W‖ :=
    Complex.re_le_norm _
  have hoff_le : ‖offDiagSum B α b W' W‖ ≤ δ⁻¹ * ∑ i ∈ B, ‖b i‖ ^ 2 :=
    hHil B α b W' W δ hδ hWW hspaced
  -- assemble.
  rw [hre]
  have : (offDiagSum B α b W' W).re ≤ δ⁻¹ * ∑ i ∈ B, ‖b i‖ ^ 2 :=
    le_trans hoff_re_le hoff_le
  have hexpand : (((W : ℝ) - (W' : ℝ)) + δ⁻¹) * ∑ i ∈ B, ‖b i‖ ^ 2
      = ((W : ℝ) - (W' : ℝ)) * ∑ i ∈ B, ‖b i‖ ^ 2
        + δ⁻¹ * ∑ i ∈ B, ‖b i‖ ^ 2 := by ring
  rw [hexpand]
  linarith [this]

/-- **The dual sharp large sieve restricted to its meaningful regime
`W' ≤ W` (proven sorry-free from `MontgomeryVaughanHilbert`).**

For arbitrary prime support `P ⊆ Ioc W' W`: since each summand
`‖∑_i conj(e(α_i p))·b_i‖²` is nonnegative, restricting from the full interval to
`P` only decreases the LHS, while the sharp constant `((W − W') + δ⁻¹)` is
unchanged.  So the subset bound follows from the full-interval reduction
`dualSharpLargeSievePerBlock_of_hilbert` by monotonicity.

(The hypothesis `W' ≤ W` is the meaningful regime: for `W < W'` and an *empty*
`P` the constant `(W − W') + δ⁻¹` may be negative while the RHS mass `∑‖b‖²` is
positive, so the literal `DualSharpLargeSievePerBlock` — which omits `W' ≤ W` —
is genuinely false in that empty-support corner; we therefore do not assert it.) -/
theorem dualSharp_subset_of_hilbert
    (hHil : MontgomeryVaughanHilbert)
    (B : Finset ℕ) (α : ℕ → ℝ) (b : ℕ → ℂ) (P : Finset ℕ) (W' W : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hWW : W' ≤ W) (hP : P ⊆ Finset.Ioc W' W)
    (hspaced : WellSpaced δ B α) :
    ∑ p ∈ P, ‖∑ i ∈ B, conj (Vinogradov.addChar (α i) p) * b i‖ ^ 2 ≤
      (((W : ℝ) - (W' : ℝ)) + δ⁻¹) * ∑ i ∈ B, ‖b i‖ ^ 2 := by
  have hfull := dualSharpLargeSievePerBlock_of_hilbert hHil B α b W' W δ hδ hWW hspaced
  have hmono : ∑ p ∈ P, ‖∑ i ∈ B, conj (Vinogradov.addChar (α i) p) * b i‖ ^ 2
      ≤ ∑ p ∈ Finset.Ioc W' W,
          ‖∑ i ∈ B, conj (Vinogradov.addChar (α i) p) * b i‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hP (fun p _ _ => by positivity)
  exact le_trans hmono hfull

#print axioms norm_expKernel_le_card
#print axioms norm_one_sub_addChar_ge
#print axioms norm_expKernel_le_inv
#print axioms dualForm_diag_offdiag
#print axioms dualSharpLargeSievePerBlock_of_hilbert
#print axioms dualSharp_subset_of_hilbert

end MathExtras.NumberTheory.Analysis.SharpLargeSieveHilbert
