/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Vaaler's interpolation inequality — the LOWER half and the full two-sided bound

This file completes the pointwise core of Vaaler's Beurling-majorant construction
begun in `VaalerInterpolation.lean`.  There the **upper half**

  `sgn(x) − Hc(x) ≤ K(x)`   for `x > 0`                                (V-up)

was proven sorry-free via the cosecant-square identity `J(x) = 1`, the
decomposition `(V-dec)`, and the elementary **tail upper bound**
`∑_{k≥1} 1/(x+k)² ≤ 1/x`.

Here we supply the matching **lower half**

  `sgn(x) − Hc(x) ≥ −K(x)`   for `x > 0`,                              (V-low)

then extend to `x < 0` by **oddness** and to `x ∈ ℤ` (already done), obtaining the
full two-sided statement `VaalerInterpolationInequalityCorrected`:

  `|sgn(x) − Hc(x)| ≤ K(x)`   for every real `x`.                      (V-§3)

## FOLLOWING THE BOOK

* **J. D. Vaaler, _Some extremal functions in Fourier analysis_, BAMS (N.S.) 12
  (1985), §3**; **H. L. Montgomery, _Ten Lectures …_ (CBMS 84), Lecture 1**.

By `one_sub_interpolant_eq` (proven in `VaalerInterpolation.lean`),

  `1 − H(x) = c(x)·( 1/x² + 2·tail − 2/x )`,        `c(x) = (sin πx/π)² ≥ 0`.

For `x > 0` (so `sgn(x) = 1`), `(V-low)` ⟺ `1 − H(x) ≥ −K(x)` ⟺
`c(x)·(1/x² + 2·tail − 2/x) ≥ −c(x)/x²` ⟺ (as `c ≥ 0`)
`2/x² + 2·tail − 2/x ≥ 0` ⟺ `1/x² + tail ≥ 1/x`.  This is the **tail LOWER
bound** dual to `(V-tail)`: the cosecant tail dominates `1/x − 1/x²`.

We prove it sorry-free by the matching telescoping inequality

  `1/(x+(k+1))² ≥ 1/(x+k+1) − 1/(x+k+2)`,

whose partial sums telescope to `≥ 1/(x+1) − 1/(x+N+1)`, giving in the limit
`tail ≥ 1/(x+1)`.  Since `1/(x+1) ≥ 1/x − 1/x²` for `x > 0` (their difference is
`1/(x²(x+1)) > 0`), the required `1/x² + tail ≥ 1/x` follows.  This is enough:
the lower bound `tail ≥ 1/(x+1)` is the simple sufficient form of the cosecant
lower bound `∑_{n≥0} 1/(x+n)² ≥ 1/x`.

## What is delivered (NEW file; no axiom, no sorry, no vacuous proof)

* `tail_term_ge` — the per-term telescoping LOWER bound.
* `tail_sum_ge` — `(V-low tail)` `∑_{k≥1} 1/(x+k)² ≥ 1/(x+1)` for `x > 0`,
  via `HasSum.tendsto_sum_nat` + `1/(x+N+1) → 0`.  Sorry-free.
* `sgn_sub_interpolant_ge_neg_kernel_of_pos`,
  `sgn_sub_vaalerHc_ge_neg_kernel_of_pos` — the **lower half** of `(V-§3)` for
  `x > 0`.
* `abs_sgn_sub_vaalerHc_le_kernel_of_pos` — the two-sided bound for `x > 0`.
* `beurlingInterpolant_neg`, `vaalerHc_neg` — the **oddness** of the interpolant.
* `VaalerInterpolationInequalityCorrected_proof` — `(V-§3)` PROVEN for all real
  `x`, closing the Beurling-majorant interpolation core, together with the
  majorize corollary `vaalerHc_majorize`.
-/

import MathExtras.NumberTheory.Analysis.VaalerInterpolation

noncomputable section

namespace MathExtras.NumberTheory.Analysis.VaalerInterpolation

open scoped BigOperators
open Filter Topology
open MathExtras.NumberTheory.Analysis.BeurlingSelberg

/-! ## §1 — The tail LOWER bound `(V-low tail)`

Dual to `tail_sum_le` (`tail ≤ 1/x`).  We prove the matching lower bound
`tail ≥ 1/(x+1)` for `x > 0` by telescoping with the per-term inequality
`1/(x+(k+1))² ≥ 1/(x+k+1) − 1/(x+k+2)`. -/

/-- Per-term telescoping LOWER bound: for `x > 0` and `k : ℕ`,
`1/(x+(k+1))² ≥ 1/(x+k+1) − 1/(x+k+2)`.  Dual of `tail_term_le`. -/
theorem tail_term_ge {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (1 : ℝ) / (x + (k : ℝ) + 1) - 1 / (x + (k : ℝ) + 2)
      ≤ 1 / (x + ((k : ℝ) + 1)) ^ 2 := by
  have h1 : (0 : ℝ) < x + (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < x + (k : ℝ) + 2 := by positivity
  -- LHS = 1/((x+k+1)(x+k+2)) ≤ 1/(x+k+1)²  since (x+k+1)² ≤ (x+k+1)(x+k+2)
  have hlhs : (1 : ℝ) / (x + (k : ℝ) + 1) - 1 / (x + (k : ℝ) + 2)
      = 1 / ((x + (k : ℝ) + 1) * (x + (k : ℝ) + 2)) := by
    rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2)]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hlhs]
  rw [show (x + ((k : ℝ) + 1)) ^ 2 = (x + (k : ℝ) + 1) ^ 2 by ring]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [h1, h2]

/-- The tail series `∑_{k≥1} 1/(x+k)²` is summable for `x > 0` (reindex of the
`ℤ`-summability used in the sibling file). -/
theorem summable_tail {x : ℝ} (hx : 0 < x) :
    Summable fun k : ℕ => (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2 := by
  -- The negative-index ℕ-part of `diffTerm` is `2 · this`; that part is summable.
  have h := summable_diffTerm_negSucc x
  have h2 : Summable fun k : ℕ => 2 / (x + ((k : ℝ) + 1)) ^ 2 := by
    apply h.congr
    intro k
    rw [diffTerm_neg]
  -- divide out the factor 2
  have h3 := h2.div_const 2
  apply h3.congr
  intro k
  field_simp

/-- **(V-low tail) The tail LOWER bound** `∑_{k≥1} 1/(x+k)² ≥ 1/(x+1)` for
`x > 0`.  Sorry-free: the partial sums telescope to `≥ 1/(x+1) − 1/(x+N+1)`, and
`1/(x+N+1) → 0`.  This is the simple sufficient form of the cosecant lower bound
dual to `(V-tail)`. -/
theorem tail_sum_ge {x : ℝ} (hx : 0 < x) :
    (1 : ℝ) / (x + 1) ≤ ∑' k : ℕ, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2 := by
  have hsum := summable_tail hx
  have hHS := hsum.hasSum.tendsto_sum_nat
  -- partial sums S_N := ∑_{k<N} 1/(x+(k+1))²  →  tsum
  -- lower bound S_N ≥ 1/(x+1) − 1/(x+N+1)
  have hpartial : ∀ N : ℕ,
      (1 : ℝ) / (x + 1) - 1 / (x + (N : ℝ) + 1)
        ≤ ∑ k ∈ Finset.range N, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2 := by
    intro N
    have hbound :
        (∑ k ∈ Finset.range N,
            ((fun j : ℕ => (1 : ℝ) / (x + (j : ℝ) + 1)) k
              - (fun j : ℕ => (1 : ℝ) / (x + (j : ℝ) + 1)) (k + 1)))
          ≤ ∑ k ∈ Finset.range N, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      have hterm := tail_term_ge hx k
      have hcast : (1 : ℝ) / (x + (k : ℝ) + 1) - 1 / (x + ((k : ℕ) + 1 : ℕ) + 1)
          = (1 : ℝ) / (x + (k : ℝ) + 1) - 1 / (x + (k : ℝ) + 2) := by
        push_cast; ring_nf
      simp only []
      rw [hcast]
      exact hterm
    rw [Finset.sum_range_sub' (fun j : ℕ => (1 : ℝ) / (x + (j : ℝ) + 1))] at hbound
    simp only [Nat.cast_zero, add_zero] at hbound
    -- hbound : 1/(x+1) - 1/(x+N+1) ≤ partial
    exact hbound
  -- 1/(x+N+1) → 0
  have htend0 : Tendsto (fun N : ℕ => (1 : ℝ) / (x + (N : ℝ) + 1)) atTop (𝓝 0) := by
    have hden : Tendsto (fun N : ℕ => x + (N : ℝ) + 1) atTop atTop := by
      apply tendsto_atTop_add_const_right
      apply tendsto_atTop_add_const_left
      exact tendsto_natCast_atTop_atTop
    have hinv := (tendsto_inv_atTop_zero.comp hden)
    simpa [Function.comp_def, one_div] using hinv
  -- lower bound tendsto: 1/(x+1) − 1/(x+N+1) → 1/(x+1)
  have htendL : Tendsto (fun N : ℕ => (1 : ℝ) / (x + 1) - 1 / (x + (N : ℝ) + 1))
      atTop (𝓝 (1 / (x + 1))) := by
    have hsub := (tendsto_const_nhds (x := (1 : ℝ) / (x + 1)) (f := (atTop : Filter ℕ))).sub htend0
    simpa using hsub
  -- conclude by comparison of limits
  exact le_of_tendsto_of_tendsto' htendL hHS hpartial

/-! ## §2 — The lower half of Vaaler's inequality for `x > 0` -/

/-- **(V-low) `sgn(x) − H(x) ≥ −K(x)` for `x > 0`.**

Sorry-free.  For `x > 0` with `x ∉ ℤ`, by `(V-dec)`/`one_sub_interpolant_eq`

  `sgn(x) − H(x) = 1 − H(x) = c(x)·(1/x² + 2·tail − 2/x)`,

and the lower bound `tail ≥ 1/(x+1) ≥ 1/x − 1/x²` gives
`1/x² + 2·tail − 2/x ≥ −1/x²`, whence (since `c ≥ 0`)
`1 − H(x) ≥ −c(x)/x² = −K(x)`. -/
theorem sgn_sub_interpolant_ge_neg_kernel_of_pos
    (x : ℝ) (hpos : 0 < x) (hx : ∀ n : ℤ, (x : ℝ) - (n : ℝ) ≠ 0) :
    -beurlingKernel x ≤ rsgn x - beurlingInterpolant x := by
  have hrsgn : rsgn x = 1 := rsgn_pos hpos
  rw [hrsgn]
  rw [one_sub_interpolant_eq x hx]
  rw [beurlingKernel_eq_prefactor_div_sq (ne_of_gt hpos)]
  have hpref : 0 ≤ prefactor x := by unfold prefactor; positivity
  have htail := tail_sum_ge hpos
  -- key real inequality: 1/x² + 2·tail − 2/x ≥ −1/x²
  have hkey : -(1 / x ^ 2)
      ≤ 1 / x ^ 2 + 2 * (∑' k : ℕ, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2) - 2 / x := by
    set T := ∑' k : ℕ, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2 with hT
    -- htail : 1/(x+1) ≤ T  ;  and  1/x − 1/x² ≤ 1/(x+1)
    have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    have hx1 : (0 : ℝ) < x + 1 := by positivity
    -- 1/x − 1/x² ≤ 1/(x+1)  ⟺  (difference) = 1/(x²(x+1)) ≥ 0
    have hcmp : 1 / x - 1 / x ^ 2 ≤ 1 / (x + 1) := by
      have hdiff : 1 / (x + 1) - (1 / x - 1 / x ^ 2)
          = 1 / (x ^ 2 * (x + 1)) := by
        field_simp
        ring
      have hpd : (0 : ℝ) ≤ 1 / (x ^ 2 * (x + 1)) := by positivity
      linarith [hdiff ▸ hpd]
    have hTge : 1 / x - 1 / x ^ 2 ≤ T := le_trans hcmp htail
    -- now: −1/x² ≤ 1/x² + 2T − 2/x  ⟺  2/x² + 2T − 2/x ≥ 0  ⟺  1/x² + T ≥ 1/x
    have hxinv : 2 / x = 2 * (1 / x) := by ring
    rw [hxinv]
    linarith [hTge]
  -- multiply by prefactor ≥ 0
  have hmul := mul_le_mul_of_nonneg_left hkey hpref
  -- hmul : prefactor·(−1/x²) ≤ prefactor·(1/x²+2T−2/x)
  calc -(prefactor x / x ^ 2)
      = prefactor x * (-(1 / x ^ 2)) := by ring
    _ ≤ prefactor x *
          (1 / x ^ 2 + 2 * (∑' k : ℕ, (1 : ℝ) / (x + ((k : ℝ) + 1)) ^ 2) - 2 / x) := hmul

/-- The **lower-half inequality for the corrected interpolant** at non-integer
`x > 0` (where `vaalerHc = beurlingInterpolant`): `sgn(x) − Hc(x) ≥ −K(x)`. -/
theorem sgn_sub_vaalerHc_ge_neg_kernel_of_pos
    (x : ℝ) (hpos : 0 < x) (hx : ∀ n : ℤ, (n : ℝ) ≠ x) :
    -beurlingKernel x ≤ rsgn x - vaalerHc x := by
  rw [vaalerHc_of_not_int hx]
  exact sgn_sub_interpolant_ge_neg_kernel_of_pos x hpos (fun n => by
    have hn := hx n; intro h; exact hn (by linarith))

/-- The two-sided bound `|sgn(x) − Hc(x)| ≤ K(x)` for non-integer `x > 0`,
assembling the upper half (`sgn_sub_vaalerHc_le_kernel_of_pos`) and the lower
half above. -/
theorem abs_sgn_sub_vaalerHc_le_kernel_of_pos
    (x : ℝ) (hpos : 0 < x) (hx : ∀ n : ℤ, (n : ℝ) ≠ x) :
    |rsgn x - vaalerHc x| ≤ beurlingKernel x := by
  rw [abs_le]
  exact ⟨sgn_sub_vaalerHc_ge_neg_kernel_of_pos x hpos hx,
         sgn_sub_vaalerHc_le_kernel_of_pos x hpos hx⟩

/-! ## §3 — Oddness of the interpolant and the `x < 0` case

Vaaler's `H` is odd: `H(−x) = −H(x)`.  We prove this directly from the explicit
`tsum` form: the prefactor `(sin π(−x)/π)² = (sin πx/π)²` is even, and the bracket
`∑_n sgn(n)/(−x − n)² + 2/(−x)` reindexes `n ↦ −n` (with `sgn(−n) = −sgn(n)`) into
`−( ∑_n sgn(n)/(x − n)² + 2/x )`.  The corrected `Hc` inherits oddness since it
agrees with `H` off `ℤ` and equals the odd `rsgn` on `ℤ`. -/

/-- **Oddness of the naive interpolant** `H(−x) = −H(x)`.  From the explicit
`tsum`, using the reindexing `n ↦ −n` and `sgn(−n) = −sgn(n)`. -/
theorem beurlingInterpolant_neg (x : ℝ) :
    beurlingInterpolant (-x) = -beurlingInterpolant x := by
  unfold beurlingInterpolant
  -- prefactor part is even
  have hsin : (Real.sin (Real.pi * (-x)) / Real.pi) ^ 2
      = (Real.sin (Real.pi * x) / Real.pi) ^ 2 := by
    rw [show Real.pi * (-x) = -(Real.pi * x) by ring, Real.sin_neg]
    rw [neg_div]; ring
  rw [hsin]
  -- bracket: reindex the sum n ↦ −n
  have hbr : (∑' n : ℤ, (if n = 0 then (0 : ℝ) else rsgn (n : ℝ) / (-x - (n : ℝ)) ^ 2)) + 2 / (-x)
      = -((∑' n : ℤ, (if n = 0 then (0 : ℝ) else rsgn (n : ℝ) / (x - (n : ℝ)) ^ 2)) + 2 / x) := by
    have hreindex :
        (∑' n : ℤ, (if n = 0 then (0 : ℝ) else rsgn (n : ℝ) / (-x - (n : ℝ)) ^ 2))
          = ∑' n : ℤ, -(if n = 0 then (0 : ℝ) else rsgn (n : ℝ) / (x - (n : ℝ)) ^ 2) := by
      rw [← (Equiv.neg ℤ).tsum_eq
        (fun n : ℤ => (if n = 0 then (0 : ℝ) else rsgn (n : ℝ) / (-x - (n : ℝ)) ^ 2))]
      apply tsum_congr
      intro n
      simp only [Equiv.neg_apply, Int.cast_neg]
      by_cases hn : n = 0
      · subst hn; simp
      · have hnn : (-n) ≠ 0 := by simpa using hn
        rw [if_neg hnn, if_neg hn]
        -- rsgn(−n) = −rsgn(n), and (−x − (−n))² = (x − n)²
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        have hrs : rsgn (-(n : ℝ)) = -rsgn (n : ℝ) := by
          rcases lt_trichotomy (n : ℝ) 0 with h | h | h
          · rw [rsgn_neg h, rsgn_pos (by linarith)]; norm_num
          · exact absurd h hnR
          · rw [rsgn_pos h, rsgn_neg (by linarith)]
        rw [hrs]
        rw [show (-x - (-(n : ℝ))) ^ 2 = (x - (n : ℝ)) ^ 2 by ring]
        ring
    rw [hreindex]
    rw [tsum_neg, div_neg]
    ring
  rw [hbr]; ring

/-- **Oddness of the corrected interpolant** `Hc(−x) = −Hc(x)`.  Off `ℤ` this is
`beurlingInterpolant_neg`; on `ℤ` it is the oddness of `rsgn`. -/
theorem vaalerHc_neg (x : ℝ) : vaalerHc (-x) = -vaalerHc x := by
  unfold vaalerHc
  by_cases hx : ∃ m : ℤ, (m : ℝ) = x
  · obtain ⟨m, hm⟩ := hx
    rw [if_pos ⟨-m, by push_cast; rw [hm]⟩, if_pos ⟨m, hm⟩]
    -- rsgn(−x) = −rsgn(x)
    rcases lt_trichotomy x 0 with h | h | h
    · rw [rsgn_neg h, rsgn_pos (by linarith)]; norm_num
    · subst h; simp
    · rw [rsgn_pos h, rsgn_neg (by linarith)]
  · rw [if_neg, if_neg hx]
    · exact beurlingInterpolant_neg x
    · rintro ⟨m, hm⟩
      exact hx ⟨-m, by push_cast; linarith⟩

/-! ## §4 — The full two-sided interpolation inequality `(V-§3)`, PROVEN

We now combine: the integer-node case (`vaalerHc_interpolation_at_node`), the
`x > 0` two-sided bound (`abs_sgn_sub_vaalerHc_le_kernel_of_pos`), and the
`x < 0` case obtained from `x > 0` by oddness
(`vaalerHc_neg`, `beurlingKernel_neg`, `rsgn` oddness). -/

/-- **(VAALER §3, corrected) — PROVEN.** `|sgn(x) − Hc(x)| ≤ K(x)` for every real
`x`.  This is the full two-sided Vaaler interpolation inequality for the faithful
corrected interpolant `vaalerHc`, closing the deep pointwise core of the
Beurling–Selberg majorant construction. -/
theorem VaalerInterpolationInequalityCorrected_proof :
    VaalerInterpolationInequalityCorrected := by
  intro x
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · -- x < 0: reduce to −x > 0 by oddness
    by_cases hint : ∃ m : ℤ, (m : ℝ) = x
    · -- x is an integer node
      obtain ⟨m, hm⟩ := hint
      have hnode := vaalerHc_interpolation_at_node m
      rw [hm] at hnode
      exact hnode
    · -- x ∉ ℤ, so y = −x ∉ ℤ
      set y := -x with hy
      have hypos : 0 < y := by rw [hy]; linarith
      have hrs : rsgn x = -rsgn y := by
        rw [hy, rsgn_neg hneg, rsgn_pos (by linarith)]
      have hHc : vaalerHc x = -vaalerHc y := by
        have hv := vaalerHc_neg y
        rw [hy, neg_neg] at hv
        rw [hv]
      have hK : beurlingKernel x = beurlingKernel y := by
        have hk := beurlingKernel_neg y
        rw [hy, neg_neg] at hk
        rw [hk]
      have hyint : ∀ n : ℤ, (n : ℝ) ≠ y := by
        intro n hn
        apply hint
        exact ⟨-n, by rw [hy] at hn; push_cast; linarith⟩
      have hpos_bound := abs_sgn_sub_vaalerHc_le_kernel_of_pos y hypos hyint
      rw [hrs, hHc, hK]
      have hneg_eq : -rsgn y - -vaalerHc y = -(rsgn y - vaalerHc y) := by ring
      rw [hneg_eq, abs_neg]
      exact hpos_bound
  · -- x = 0: integer node m = 0
    subst hzero
    have hnode := vaalerHc_interpolation_at_node 0
    simpa using hnode
  · -- x > 0
    by_cases hint : ∃ m : ℤ, (m : ℝ) = x
    · obtain ⟨m, hm⟩ := hint
      have hnode := vaalerHc_interpolation_at_node m
      rw [hm] at hnode
      exact hnode
    · have hxint : ∀ n : ℤ, (n : ℝ) ≠ x := by
        intro n hn; exact hint ⟨n, hn⟩
      exact abs_sgn_sub_vaalerHc_le_kernel_of_pos x hpos hxint

/-- The majorize corollary, now **unconditional**: `sgn(x) ≤ Hc(x) + K(x)` for
the corrected interpolant, for every real `x`. -/
theorem vaalerHc_majorize (x : ℝ) :
    rsgn x ≤ vaalerHc x + beurlingKernel x :=
  vaalerHc_majorize_of_corrected VaalerInterpolationInequalityCorrected_proof x

#print axioms tail_term_ge
#print axioms tail_sum_ge
#print axioms sgn_sub_interpolant_ge_neg_kernel_of_pos
#print axioms abs_sgn_sub_vaalerHc_le_kernel_of_pos
#print axioms beurlingInterpolant_neg
#print axioms vaalerHc_neg
#print axioms VaalerInterpolationInequalityCorrected_proof
#print axioms vaalerHc_majorize

end MathExtras.NumberTheory.Analysis.VaalerInterpolation

end
