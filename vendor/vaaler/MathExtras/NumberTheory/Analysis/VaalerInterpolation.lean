/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Vaaler's interpolation inequality `|sgn(x) − H(x)| ≤ K(x)` — Track S, FOLLOWING VAALER

This file develops the pointwise core of Vaaler's Beurling-majorant construction:
the **interpolation inequality**

  `|sgn(x) − H(x)| ≤ K(x)`   for every real `x`,                       (V-§3)

with the explicit functions of `BeurlingSelbergConstruction.lean`

  `K(x) = (sin πx / (πx))²`,
  `H(x) = (sin πx / π)² · ( ∑_{n∈ℤ} sgn(n)/(x − n)²  +  2/x )`.

## FOLLOWING THE BOOK

* **J. D. Vaaler, _Some extremal functions in Fourier analysis_, BAMS (N.S.) 12
  (1985), §2–§3**; **H. L. Montgomery, _Ten Lectures …_ (CBMS 84), Lecture 1**.

Vaaler's argument rests on the **cosecant-squared partial-fraction identity**

  `∑_{n∈ℤ} 1/(x − n)² = π² / sin²(πx)`   (x ∉ ℤ),                       (csc²)

equivalently  `J(x) := (sin πx / π)² · ∑_{n∈ℤ} 1/(x − n)² = 1`.  Writing
`c(x) := (sin πx / π)²`, the `n = 0` term of `J` is exactly `K`, and for `x > 0`
(so `sgn(x) = 1 = J(x)`) one finds the **decomposition**

  `sgn(x) − H(x) = J(x) − H(x)
                = c(x)·[ ∑_{n∈ℤ} 1/(x−n)² − ∑_{n≠0} sgn(n)/(x−n)² − 2/x ]
                = K(x) + 2·c(x)·[ ∑_{n<0} 1/(x−n)² − 1/x ].`              (V-dec)

The upper half of `(V-§3)` for `x > 0` is therefore equivalent to the elementary
**tail bound**

  `∑_{n≥1} 1/(x + n)² ≤ 1/x`   (x > 0),                                 (V-tail)

which we prove sorry-free by telescoping `1/(x+n)² ≤ 1/(x+n−1) − 1/(x+n)`.  This
gives `sgn(x) − H(x) ≤ K(x)` for `x > 0` — half of Vaaler's inequality — without
any axiom.  The matching lower half `sgn(x) − H(x) ≥ −K(x)` is the genuinely
delicate residual and is isolated.

## CRITICAL FINDING — the *as-defined* `beurlingInterpolant` is NOT Vaaler's `H`

Lean's `1/0 = 0` convention makes the `tsum` in `beurlingInterpolant` drop the
pole term at every node.  Concretely we prove **sorry-free**

  `beurlingInterpolant (m : ℝ) = 0`   for every integer `m`               (node-0)

(because the prefactor `(sin πm)² = 0`).  Hence at a nonzero integer `m`,
`|rsgn m − beurlingInterpolant m| = |±1 − 0| = 1` while `beurlingKernel m = 0`,
so the residual `BeurlingInterpolationInequality` of `BeurlingSelbergConstruction`
is **literally false at every nonzero integer** — see `not_BeurlingInterpolationInequality`.
The true Vaaler `H` takes the value `sgn(m)` at nodes via the *removable
singularity* / residue (the `(sin πx)²` zero cancels the double pole), which the
naive `tsum` does not realize.  We therefore define the **corrected interpolant**
`vaalerHc` agreeing with the naive object off `ℤ` and with `sgn` on `ℤ`, prove
the node-interpolation facts `vaalerHc (m) = sgn(m)` sorry-free, and state the
corrected inequality `VaalerInterpolationInequalityCorrected` against it.

## What is delivered (NEW file; no axiom, no sorry, no vacuous proof)

* `csc²` value `vaalerJ_eq_one`  — `(sin πx/π)²·∑_n 1/(x−n)² = 1` off `ℤ`
  (sorry-free, from the repo's `CotangentSquareSum`).
* `beurlingKernel_eq_prefactor_div_sq`  — `K(x) = c(x)/x²` off `0`.
* `beurlingInterpolant_intCast` (node-0) and `not_BeurlingInterpolationInequality`
  — the node defect of the naive object.
* `vaalerHc`, `vaalerHc_intCast` — the corrected interpolant and its node values.
* `tail_sum_le` (V-tail), `sgn_sub_interpolant_le_kernel_of_pos` — the **upper
  half** of Vaaler's inequality for `x > 0`, sorry-free.
* `VaalerInterpolationInequalityCorrected` — the residual (the matching lower
  half / the full corrected statement), with the reduction lemmas around it.
-/

import MathExtras.NumberTheory.Analysis.BeurlingSelbergConstruction
import MathExtras.Analysis.CotangentSquareSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries

noncomputable section

namespace MathExtras.NumberTheory.Analysis.VaalerInterpolation

open scoped BigOperators
open MathExtras.NumberTheory.Analysis.BeurlingSelberg

/-! ## §1 — The cosecant-square value `J(x) = 1` (Vaaler, from `CotangentSquareSum`)

Vaaler's central identity is `J(x) := (sin πx/π)² · ∑_{n∈ℤ} 1/(x−n)² = 1` for
`x ∉ ℤ`.  We obtain it sorry-free from the repository's Euler cotangent-square
theorem `tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq`. -/

/-- The Vaaler prefactor `c(x) = (sin πx / π)²`. -/
def prefactor (x : ℝ) : ℝ := (Real.sin (Real.pi * x) / Real.pi) ^ 2

/-- The reindexed cosecant-square sum: `∑_{n∈ℤ} 1/(x−n)²`.  Note `(x − n)² =
((-n) + x)²`, so this is the `CotangentSquareSum` family at `s = x`. -/
theorem tsum_one_div_sub_sq_eq (x : ℝ) (hx : ∀ n : ℤ, (x : ℝ) - (n : ℝ) ≠ 0) :
    (∑' n : ℤ, (1 : ℝ) / (x - (n : ℝ)) ^ 2)
      = Real.pi ^ 2 / Real.sin (x * Real.pi) ^ 2 := by
  have hs : ∀ n : ℤ, ((n : ℝ) + x) ≠ 0 := by
    intro n
    have := hx (-n)
    simpa [sub_eq_add_neg, add_comm] using this
  have hkey := MathExtras.CotangentSquareSum.tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq x hs
  -- reindex n ↦ -n to turn (n + x) into (x - n)
  rw [← hkey]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => (1 : ℝ) / ((n : ℝ) + x) ^ 2)]
  apply tsum_congr
  intro n
  simp only [Equiv.neg_apply, Int.cast_neg]
  rw [show (x - (n : ℝ)) ^ 2 = (-(n : ℝ) + x) ^ 2 by ring]

/-- **Vaaler's identity `J(x) = 1`** (off the integers):
`(sin πx / π)² · ∑_{n∈ℤ} 1/(x−n)² = 1`.  Sorry-free, from `(csc²)`. -/
theorem vaalerJ_eq_one (x : ℝ) (hx : ∀ n : ℤ, (x : ℝ) - (n : ℝ) ≠ 0) :
    prefactor x * (∑' n : ℤ, (1 : ℝ) / (x - (n : ℝ)) ^ 2) = 1 := by
  have hsin : Real.sin (x * Real.pi) ≠ 0 := by
    rw [Real.sin_ne_zero_iff]
    intro n hn
    -- n * π = x * π ⇒ n = x ⇒ x - n = 0, contradicting hx
    have hpi : (Real.pi) ≠ 0 := Real.pi_ne_zero
    have : (n : ℝ) = x := by
      have := mul_right_cancel₀ hpi hn
      exact this
    exact hx n (by rw [← this]; ring)
  rw [tsum_one_div_sub_sq_eq x hx]
  unfold prefactor
  rw [show Real.sin (Real.pi * x) = Real.sin (x * Real.pi) by rw [mul_comm]]
  field_simp

/-! ## §2 — The node defect: the *as-defined* `beurlingInterpolant` vanishes on `ℤ`

Because Lean uses `1/0 = 0`, the `tsum` in `beurlingInterpolant` silently drops
the pole term at every integer node, and the `(sin πx)²` prefactor then kills the
whole product.  So `beurlingInterpolant (m) = 0` for every integer `m`.  This is
**not** Vaaler's `H` (which has `H(m) = sgn(m)`); the discrepancy is the
removable-singularity value the naive `tsum` cannot see.  We record the defect
honestly and disprove the literal residual `BeurlingInterpolationInequality`. -/

/-- **(node-0) The naive interpolant vanishes at every integer.**  Since
`sin(π·m) = 0`, the prefactor `(sin πm/π)²` is `0`, so the product is `0`
regardless of the (Lean-finite) bracket. -/
theorem beurlingInterpolant_intCast (m : ℤ) :
    beurlingInterpolant ((m : ℝ)) = 0 := by
  unfold beurlingInterpolant
  have hsin : Real.sin (Real.pi * (m : ℝ)) = 0 := by
    rw [mul_comm]; exact Real.sin_int_mul_pi m
  rw [hsin]; simp

/-- **The literal residual `BeurlingInterpolationInequality` is FALSE.**  At any
nonzero integer `m`, `|rsgn m − beurlingInterpolant m| = |±1 − 0| = 1` while
`beurlingKernel m = 0`, so `1 ≤ 0` would be required.  Concretely we disprove it
at `m = 1`.  (This is the crux finding: the naive `tsum` object is not Vaaler's
`H` at the interpolation nodes.) -/
theorem not_BeurlingInterpolationInequality :
    ¬ MathExtras.NumberTheory.Analysis.BeurlingSelberg.BeurlingInterpolationInequality := by
  intro h
  have h1 := h (1 : ℝ)
  have hH : beurlingInterpolant (1 : ℝ) = 0 := by
    have := beurlingInterpolant_intCast 1; simpa using this
  have hrsgn : rsgn (1 : ℝ) = 1 := rsgn_pos one_pos
  have hker : beurlingKernel (1 : ℝ) = 0 := by
    have := beurlingKernel_intCast_ne_zero (m := (1 : ℤ)) (by decide)
    simpa using this
  rw [hH, hrsgn, hker] at h1
  norm_num at h1

/-! ## §3 — The kernel as the `n = 0` term of `J` -/

/-- `K(x) = c(x) / x²` for `x ≠ 0`, i.e. the kernel is exactly the `n = 0` term
of the cosecant-square sum that defines `J`. -/
theorem beurlingKernel_eq_prefactor_div_sq {x : ℝ} (hx : x ≠ 0) :
    beurlingKernel x = prefactor x / x ^ 2 := by
  unfold beurlingKernel prefactor
  rw [if_neg hx]
  field_simp

/-! ## §4 — The corrected interpolant and the node-interpolation facts

Vaaler's `H` satisfies `H(m) = sgn(m)` at every integer node `m` (the
removable-singularity value).  Since the naive object vanishes on `ℤ`
((node-0)), the faithful Lean encoding agrees with the naive object off `ℤ` and
takes the value `rsgn` on `ℤ`.  We make this explicit and prove the node values
sorry-free.  Off `ℤ` it is `beurlingInterpolant`, so the deep inequality is
unchanged there. -/

/-- The corrected Vaaler interpolant `Hc`: equal to `rsgn` at the integer
interpolation nodes (Vaaler's removable-singularity value), and to the naive
`beurlingInterpolant` off the integers. -/
def vaalerHc (x : ℝ) : ℝ :=
  open Classical in
  if (∃ m : ℤ, (m : ℝ) = x) then rsgn x else beurlingInterpolant x

/-- **(node-interpolation) `Hc(m) = sgn(m)`** at every integer node — Vaaler's
defining interpolation property, sorry-free for the corrected interpolant. -/
theorem vaalerHc_intCast (m : ℤ) : vaalerHc ((m : ℝ)) = rsgn ((m : ℝ)) := by
  unfold vaalerHc
  rw [if_pos]
  exact ⟨m, rfl⟩

/-- Off the integers, `Hc` is the naive `beurlingInterpolant` (so the deep
analytic content is identical there). -/
theorem vaalerHc_of_not_int {x : ℝ} (hx : ∀ m : ℤ, (m : ℝ) ≠ x) :
    vaalerHc x = beurlingInterpolant x := by
  unfold vaalerHc
  rw [if_neg]
  rintro ⟨m, hm⟩
  exact hx m hm


/-- **The interpolation inequality holds at every integer node** for the
corrected interpolant: `|sgn(m) − Hc(m)| = 0 ≤ K(m)`.  Sorry-free. -/
theorem vaalerHc_interpolation_at_node (m : ℤ) :
    |rsgn ((m : ℝ)) - vaalerHc ((m : ℝ))| ≤ beurlingKernel ((m : ℝ)) := by
  rw [vaalerHc_intCast m, sub_self, abs_zero]
  exact beurlingKernel_nonneg _

/-! ## §5 — The tail bound (V-tail) and the upper half of Vaaler's inequality

For `x > 0`, the upper half `sgn(x) − H(x) ≤ K(x)` reduces, via the `(V-dec)`
decomposition and `J(x) = 1`, to the elementary tail bound

  `∑_{n≥1} 1/(x + n)² ≤ 1/x`.                                          (V-tail)

We prove `(V-tail)` sorry-free by telescoping
`1/(x+n+1)² ≤ 1/(x+n) − 1/(x+n+1)`. -/

/-- Per-term telescoping bound: for `x > 0` and `n : ℕ`,
`1/(x + (n+1))² ≤ 1/(x + n) − 1/(x + (n+1))`. -/
theorem tail_term_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (1 : ℝ) / (x + ((n : ℝ) + 1)) ^ 2
      ≤ 1 / (x + (n : ℝ)) - 1 / (x + ((n : ℝ) + 1)) := by
  have h0 : (0 : ℝ) < x + (n : ℝ) := by positivity
  have h1 : (0 : ℝ) < x + ((n : ℝ) + 1) := by positivity
  -- RHS = 1/((x+n)(x+n+1)) and (x+n)(x+n+1) ≤ (x+n+1)²
  have hrhs : (1 : ℝ) / (x + (n : ℝ)) - 1 / (x + ((n : ℝ) + 1))
      = 1 / ((x + (n : ℝ)) * (x + ((n : ℝ) + 1))) := by
    rw [div_sub_div _ _ (ne_of_gt h0) (ne_of_gt h1)]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hrhs]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [h0, h1]

/-- **(V-tail) The tail bound** `∑_{n≥1} 1/(x+n)² ≤ 1/x` for `x > 0`.  Sorry-free,
by telescoping.  This is the elementary inequality to which the upper half of
Vaaler's interpolation inequality reduces. -/
theorem tail_sum_le {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, (1 : ℝ) / (x + ((n : ℝ) + 1)) ^ 2) ≤ 1 / x := by
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro N
  -- partial sum ≤ telescoping sum = 1/x − 1/(x+N) ≤ 1/x
  have hbound : (∑ i ∈ Finset.range N, (1 : ℝ) / (x + ((i : ℝ) + 1)) ^ 2)
      ≤ ∑ i ∈ Finset.range N,
          ((fun k : ℕ => (1 : ℝ) / (x + (k : ℝ))) i
            - (fun k : ℕ => (1 : ℝ) / (x + (k : ℝ))) (i + 1)) := by
    apply Finset.sum_le_sum
    intro i _
    have := tail_term_le hx i
    simp only [Nat.cast_add, Nat.cast_one]
    convert this using 2
  rw [Finset.sum_range_sub' (fun k : ℕ => (1 : ℝ) / (x + (k : ℝ)))] at hbound
  simp only [Nat.cast_zero, add_zero] at hbound
  have hN : (0 : ℝ) ≤ 1 / (x + (N : ℝ)) := by positivity
  linarith

/-! ## §6 — The upper half of Vaaler's inequality for `x > 0`

Following `(V-dec)`: for `x > 0` with `x ∉ ℤ`,

  `sgn(x) − H(x) = 1 − H(x) = J(x) − H(x)
                = c(x)·[ ∑_n 1/(x−n)² − ∑_{n≠0} sgn(n)/(x−n)² − 2/x ]
                = c(x)·[ 1/x² + 2·∑_{k≥1} 1/(x+k)² − 2/x ]
                = K(x) + 2·c(x)·[ ∑_{k≥1} 1/(x+k)² − 1/x ]
               ≤ K(x)`            (by `(V-tail)` and `c ≥ 0`).

All summability and the `ℤ`-split are discharged via the repo's
`summable_one_div_int_add_sq` and Mathlib's `tsum_of_nat_of_neg_add_one`. -/

/-- Summability over `ℤ` of `n ↦ 1/(x−n)²`.  Reindex of `summable_one_div_int_add_sq`. -/
theorem summable_one_div_sub_sq (x : ℝ) :
    Summable fun n : ℤ => (1 : ℝ) / (x - (n : ℝ)) ^ 2 := by
  have h := MathExtras.CotangentSquareSum.summable_one_div_int_add_sq (s := x)
  have h2 := (Equiv.neg ℤ).summable_iff.mpr h
  apply h2.congr
  intro n
  simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg]
  rw [show (x - (n : ℝ)) ^ 2 = (-(n : ℝ) + x) ^ 2 by ring]

/-- Summability over `ℤ` of the sgn-weighted term `n ↦ (if n=0 then 0 else
sgn(n)/(x−n)²)`.  Dominated by `1/(x−n)²`. -/
theorem summable_sgnTerm (x : ℝ) :
    Summable fun n : ℤ =>
      (if n = 0 then (0 : ℝ) else rsgn (n : ℝ) / (x - (n : ℝ)) ^ 2) := by
  apply Summable.of_norm_bounded (summable_one_div_sub_sq x)
  intro n
  by_cases hn : n = 0
  · simp only [if_pos hn, norm_zero]
    positivity
  · simp only [if_neg hn, Real.norm_eq_abs, abs_div]
    rw [abs_of_nonneg (sq_nonneg ((x - (n : ℝ))))]
    have hnum : |rsgn (n : ℝ)| ≤ 1 := by unfold rsgn; split_ifs <;> norm_num
    rcases eq_or_ne ((x - (n : ℝ)) ^ 2) 0 with hz | hz
    · rw [hz]; simp
    · have hden : (0 : ℝ) < (x - (n : ℝ)) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
      gcongr

/-- The per-term difference `d(n) = 1/(x−n)² − (sgn-weighted term)`.  It vanishes
for `n > 0`, equals `1/x²` at `n = 0`, and equals `2/(x−n)²` for `n < 0`. -/
def diffTerm (x : ℝ) (n : ℤ) : ℝ :=
  (1 : ℝ) / (x - (n : ℝ)) ^ 2
    - (if n = 0 then (0 : ℝ) else rsgn (n : ℝ) / (x - (n : ℝ)) ^ 2)

/-- For a positive integer index `n = (k : ℕ)+1 > 0`, `rsgn = 1` and the
difference term vanishes. -/
theorem diffTerm_pos (x : ℝ) (k : ℕ) : diffTerm x ((k : ℤ) + 1) = 0 := by
  unfold diffTerm
  have hne : ((k : ℤ) + 1) ≠ 0 := by omega
  rw [if_neg hne]
  have hpos : (0 : ℝ) < (((k : ℤ) + 1 : ℤ) : ℝ) := by exact_mod_cast Nat.cast_add_one_pos k
  rw [rsgn_pos hpos]
  ring

/-- At `n = 0` the difference term is `1/x²`. -/
theorem diffTerm_zero (x : ℝ) : diffTerm x 0 = 1 / x ^ 2 := by
  unfold diffTerm; simp

/-- For a negative integer index `n = -((k : ℕ)+1) < 0`, `rsgn = −1` and the
difference term is `2/(x + (k+1))²`. -/
theorem diffTerm_neg (x : ℝ) (k : ℕ) :
    diffTerm x (-((k : ℤ) + 1)) = 2 / (x + ((k : ℝ) + 1)) ^ 2 := by
  unfold diffTerm
  have hne : (-((k : ℤ) + 1)) ≠ 0 := by omega
  rw [if_neg hne]
  have hneg : (((-((k : ℤ) + 1) : ℤ)) : ℝ) < 0 := by
    have : (0 : ℝ) < (((k : ℤ) + 1 : ℤ) : ℝ) := by exact_mod_cast Nat.cast_add_one_pos k
    push_cast; linarith
  rw [rsgn_neg hneg]
  have : (x - (((-((k : ℤ) + 1) : ℤ)) : ℝ)) = (x + ((k : ℝ) + 1)) := by push_cast; ring
  rw [this]; ring

/-- `diffTerm` is summable over `ℤ` (difference of two summables). -/
theorem summable_diffTerm (x : ℝ) : Summable (diffTerm x) := by
  unfold diffTerm
  exact (summable_one_div_sub_sq x).sub (summable_sgnTerm x)

/-- The two summability facts for the `ℕ`-pieces of the `ℤ`-split of `diffTerm`. -/
theorem summable_diffTerm_nat (x : ℝ) : Summable fun k : ℕ => diffTerm x (k : ℤ) :=
  (summable_diffTerm x).comp_injective (fun a b h => by exact_mod_cast h)

theorem summable_diffTerm_negSucc (x : ℝ) :
    Summable fun k : ℕ => diffTerm x (-((k : ℤ) + 1)) :=
  (summable_diffTerm x).comp_injective (fun a b h => by
    simp only [neg_inj, add_left_inj] at h; exact_mod_cast h)

/-- **(Step D) The `ℤ`-split of `∑'_n diffTerm`.**  For `x > 0`:

  `∑'_{n∈ℤ} diffTerm x n = 1/x² + 2·∑'_{k} 1/(x+(k+1))²`.

The positive-index ℕ-part collapses to `1/x²` (only `k=0` survives, the rest
vanish by `diffTerm_pos`), and the negative-index ℕ-part is `2·tail` by
`diffTerm_neg`. -/
theorem tsum_diffTerm_eq (x : ℝ) :
    (∑' n : ℤ, diffTerm x n)
      = 1 / x ^ 2 + 2 * ∑' k : ℕ, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2 := by
  rw [tsum_of_nat_of_neg_add_one (summable_diffTerm_nat x) (summable_diffTerm_negSucc x)]
  congr 1
  · -- positive part: ∑'_k diffTerm x k = diffTerm x 0 = 1/x²  (all k≥1 vanish)
    rw [tsum_eq_single 0 ?_]
    · rw [Nat.cast_zero, diffTerm_zero]
    · intro k hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
      rw [this, diffTerm_pos]
  · -- negative part: ∑'_k diffTerm x (-(k+1)) = 2·tail
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [diffTerm_neg]
    ring

/-! ## §7 — Assembly of the upper-half inequality `sgn(x) − H(x) ≤ K(x)` for `x > 0` -/

/-- The naive interpolant in `prefactor`-factored form: `H(x) = c(x)·(Ssgn + 2/x)`
where `Ssgn = ∑'_n (sgn-weighted term)`. -/
theorem beurlingInterpolant_eq_prefactor (x : ℝ) :
    beurlingInterpolant x
      = prefactor x *
          ((∑' n : ℤ, (if n = 0 then (0 : ℝ) else rsgn (n : ℝ) / (x - (n : ℝ)) ^ 2)) + 2 / x) := by
  rfl

/-- **(V-dec) The decomposition identity.**  For non-integer `x`,

  `1 − H(x) = c(x)·( ∑'_n diffTerm − 2/x )
            = c(x)·( 1/x² + 2·tail − 2/x )`.

Sorry-free, using `vaalerJ_eq_one`, `Summable.tsum_sub`, and `tsum_diffTerm_eq`. -/
theorem one_sub_interpolant_eq (x : ℝ) (hx : ∀ n : ℤ, (x : ℝ) - (n : ℝ) ≠ 0) :
    1 - beurlingInterpolant x
      = prefactor x *
          (1 / x ^ 2 + 2 * (∑' k : ℕ, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2) - 2 / x) := by
  have hJ := vaalerJ_eq_one x hx
  rw [beurlingInterpolant_eq_prefactor]
  -- ∑ diffTerm = Sall − Ssgn  (tsum_sub)
  have hsub : (∑' n : ℤ, diffTerm x n)
      = (∑' n : ℤ, (1 : ℝ) / (x - (n : ℝ)) ^ 2)
        - ∑' n : ℤ, (if n = 0 then (0 : ℝ) else rsgn (n : ℝ) / (x - (n : ℝ)) ^ 2) := by
    unfold diffTerm
    exact (summable_one_div_sub_sq x).tsum_sub (summable_sgnTerm x)
  rw [tsum_diffTerm_eq] at hsub
  -- abbreviations
  set Sall := ∑' n : ℤ, (1 : ℝ) / (x - (n : ℝ)) ^ 2 with hSall
  set Ssgn := ∑' n : ℤ, (if n = 0 then (0 : ℝ) else rsgn (n : ℝ) / (x - (n : ℝ)) ^ 2) with hSsgn
  set T := ∑' k : ℕ, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2 with hT
  -- hJ : prefactor·Sall = 1 ; hsub : 1/x² + 2T = Sall − Ssgn
  -- goal : 1 − prefactor·(Ssgn + 2/x) = prefactor·(1/x² + 2T − 2/x)
  have hexp : prefactor x * (1 / x ^ 2 + 2 * T - 2 / x)
      = prefactor x * (Sall - Ssgn) - prefactor x * (2 / x) := by
    rw [hsub]; ring
  rw [hexp]
  have : prefactor x * (Sall - Ssgn) = 1 - prefactor x * Ssgn := by
    rw [mul_sub, hJ]
  rw [this]; ring

/-- **(Upper half of Vaaler §3) `sgn(x) − H(x) ≤ K(x)` for `x > 0`.**

Sorry-free.  For `x > 0` with `x ∉ ℤ`: `sgn(x) = 1`, and by `(V-dec)`

  `sgn(x) − H(x) = K(x) + 2·c(x)·( tail − 1/x ) ≤ K(x)`

since `c(x) ≥ 0` and `tail ≤ 1/x` by `(V-tail)`.  (At a positive *integer* `x`
the corrected node value `vaalerHc(x) = sgn(x)` gives the inequality directly;
see `vaalerHc_interpolation_at_node`.) -/
theorem sgn_sub_interpolant_le_kernel_of_pos
    (x : ℝ) (hpos : 0 < x) (hx : ∀ n : ℤ, (x : ℝ) - (n : ℝ) ≠ 0) :
    rsgn x - beurlingInterpolant x ≤ beurlingKernel x := by
  have hrsgn : rsgn x = 1 := rsgn_pos hpos
  rw [hrsgn]
  rw [one_sub_interpolant_eq x hx]
  rw [beurlingKernel_eq_prefactor_div_sq (ne_of_gt hpos)]
  have hpref : 0 ≤ prefactor x := by unfold prefactor; positivity
  have htail := tail_sum_le hpos
  -- prefactor·(1/x² + 2·tail − 2/x) ≤ prefactor·(1/x²)  ⟺  2·tail − 2/x ≤ 0
  have hkey : 1 / x ^ 2 + 2 * (∑' k : ℕ, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2) - 2 / x
      ≤ 1 / x ^ 2 := by
    have : (∑' k : ℕ, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2) ≤ 1 / x := by
      have heq : (∑' k : ℕ, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2)
          = ∑' n : ℕ, (1 : ℝ) / (x + ((n : ℝ) + 1)) ^ 2 := rfl
      rw [heq]; exact htail
    have h2x : (2 : ℝ) / x = 2 * (1 / x) := by ring
    rw [h2x]
    linarith [this]
  calc prefactor x * (1 / x ^ 2 + 2 * (∑' k : ℕ, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2) - 2 / x)
      ≤ prefactor x * (1 / x ^ 2) := by
        apply mul_le_mul_of_nonneg_left hkey hpref
    _ = prefactor x / x ^ 2 := by ring

/-- The **upper-half inequality for the corrected interpolant** at non-integer
`x > 0` (where `vaalerHc = beurlingInterpolant`): `sgn(x) − Hc(x) ≤ K(x)`. -/
theorem sgn_sub_vaalerHc_le_kernel_of_pos
    (x : ℝ) (hpos : 0 < x) (hx : ∀ n : ℤ, (n : ℝ) ≠ x) :
    rsgn x - vaalerHc x ≤ beurlingKernel x := by
  rw [vaalerHc_of_not_int hx]
  exact sgn_sub_interpolant_le_kernel_of_pos x hpos (fun n => by
    have := hx n; intro h; exact this (by linarith))

/-! ## §8 — The corrected interpolation inequality residual

We package Vaaler's `(V-§3)` for the *corrected* interpolant `vaalerHc`.  The
parts proven sorry-free above are:

* the inequality **at every integer node** (`vaalerHc_interpolation_at_node`);
* the **upper half** at non-integer `x > 0`
  (`sgn_sub_vaalerHc_le_kernel_of_pos`), reducing to `(V-tail)` and `J = 1`.

What remains for the full two-sided `|sgn − Hc| ≤ K` is (a) the matching **lower
half** `sgn(x) − Hc(x) ≥ −K(x)` for `x > 0`, and (b) the `x < 0` cases — all
following by the same `(V-dec)`/oddness route but with the more delicate
lower-bound on the cosecant tail.  We isolate the full two-sided statement as the
single named residual. -/

/-- **(VAALER §3, corrected) The interpolation inequality for `vaalerHc`.**

`|sgn(x) − Hc(x)| ≤ K(x)` for every real `x`.  This is the faithful Lean form of
Vaaler 1985 §3 (the naive `beurlingInterpolant` version is *false* at the integer
nodes — see `not_BeurlingInterpolationInequality`).  Proven here: the node case
and the upper half for `x > 0`; the residual is the matching lower half and the
`x < 0` cases. -/
def VaalerInterpolationInequalityCorrected : Prop :=
  ∀ x : ℝ, |rsgn x - vaalerHc x| ≤ beurlingKernel x

/-- Reduction: the corrected inequality yields the majorize property
`sgn(x) ≤ Hc(x) + K(x)` for the corrected interpolant, exactly as the literal
residual was intended to (mirrors `majorize_of_interpolation_ineq`). -/
theorem vaalerHc_majorize_of_corrected
    (h : VaalerInterpolationInequalityCorrected) (x : ℝ) :
    rsgn x ≤ vaalerHc x + beurlingKernel x := by
  have hle : rsgn x - vaalerHc x ≤ beurlingKernel x :=
    le_trans (le_abs_self _) (h x)
  linarith

#print axioms vaalerJ_eq_one
#print axioms beurlingInterpolant_intCast
#print axioms not_BeurlingInterpolationInequality
#print axioms vaalerHc_intCast
#print axioms vaalerHc_interpolation_at_node
#print axioms tail_sum_le
#print axioms tsum_diffTerm_eq
#print axioms one_sub_interpolant_eq
#print axioms sgn_sub_interpolant_le_kernel_of_pos
#print axioms sgn_sub_vaalerHc_le_kernel_of_pos
#print axioms vaalerHc_majorize_of_corrected

end MathExtras.NumberTheory.Analysis.VaalerInterpolation

end