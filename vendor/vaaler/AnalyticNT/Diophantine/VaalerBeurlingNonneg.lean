/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Vaaler's Lemma 5: nonnegativity of the Beurling majorant `φ = H + K − sgn`

This leaf formalises, faithfully to Vaaler, "Some extremal functions in Fourier
analysis", Bull. AMS 12 (1985), **Lemma 5** (eqs (2.23)–(2.26), pp. 191–192): the
Beurling function `B = H + K` majorises `sgn`, i.e. `|sgn(x) − H(x)| ≤ K(x)` for
all real `x`, equivalently

* `φ(x) = H(x) + K(x) − sgn(x) ≥ 0`   (the majorant side), and
* `H(x) − K(x) − sgn(x) ≤ 0`          (the minorant side).

This is the `nonneg` field of `VaalerBeurlingMajorant`
(`MathExtras.NumberTheory.Analysis.VaalerThm16Mechanism`).

## The objects (Vaaler §2)

* Fejér kernel `K(x) = (sin πx / (πx))²` (with `K(0) = 1`).  Nonnegative.
* `H(x) = (sin πx / π)² · { ∑_{m∈ℤ} sgn(m)·(x−m)⁻² + 2 x⁻¹ }`, the odd interpolant
  of `sgn`, with `H(0) = 0`.
* `φ = H + K − sgn`.

## The proof

By oddness of `sgn` and `H` and evenness of `K`, it suffices to prove
`1 − K(x) ≤ H(x) ≤ 1` for `x > 0` (Vaaler eq (2.25)).

The crux is the **classical squared cotangent (cosecant²) identity**
`∑_{m∈ℤ} (x−m)⁻² = (π / sin πx)²` for `x ∉ ℤ`.  In Mathlib this is the negative
derivative of the Mittag-Leffler series `cot_series_rep`
(`Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent`).  Differentiating it
term-by-term over the reals is a substantial separate task; we therefore isolate it
here as the single named sub-lemma `vaalerSumInvSqIdentity` (a precise, standard
classical identity) and prove everything else outright.

Using the identity, for `x > 0` (Vaaler eq (2.26)):
`H(x) = 1 + (sin πx / π)² · { 2 x⁻¹ − x⁻² − 2·∑_{m≥1}(x+m)⁻² }`,
and the two endpoint inequalities reduce to two **elementary, fully proven**
telescoping/AM–GM facts:

* `H(x) ≤ 1`  ⇔  `x⁻² + 2 ∑_{m≥1}(x+m)⁻² ≥ 2 x⁻¹`  (AM–GM `2ab ≤ a²+b²` summed,
  RHS telescopes to `2 x⁻¹`);
* `1 − K(x) ≤ H(x)`  ⇔  `∑_{m≥1}(x+m)⁻² ≤ x⁻¹`  (`(x+m)⁻² ≤ (x+m−1)⁻¹(x+m)⁻¹`,
  RHS telescopes to `x⁻¹`).

## Status

The two telescoping/AM–GM inequalities, the `H` rewrite, oddness, and the assembly
are all proven outright.  The classical squared-cosecant identity is also proved
below from Mathlib's upper-half-plane cotangent series: analytic continuation on
the connected integer-complement transfers the identity to the real line.  Thus
`vaalerSumInvSqIdentity_holds`, `vaaler_phi_nonneg_holds`, and
`vaaler_phi_minorant_holds` are unconditional base-trio theorems.
-/

noncomputable section

open Real Filter Topology
open scoped BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg

/-! ## The objects: Fejér `K`, the interpolant `H`, and `φ` -/

/-- The Fejér kernel `K(x) = (sin πx / (πx))²`, with the removable value `K(0) = 1`.
For `x ≠ 0` this equals `(sin πx / π)² · x⁻²`. -/
def fejerK (x : ℝ) : ℝ := if x = 0 then 1 else (Real.sin (π * x) / π) ^ 2 * x⁻¹ ^ 2

/-- The "tail" piece `T(x) = ∑_{m ≥ 1} (x + m)⁻²` (indexed over `m ≥ 1`, i.e. the
positive integers), as a tsum over `k ≥ 0` of `(x + (k+1))⁻²`. -/
def tailSum (x : ℝ) : ℝ := ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2

/-- The bracket `B(x) = ∑_{m∈ℤ} sgn(m)·(x − m)⁻² + 2 x⁻¹`, written via the
`sgn`-split `∑_{m≥1}(x−m)⁻² − ∑_{m≥1}(x+m)⁻²`.  We only ever evaluate `H` for
`x ∉ ℤ` (in fact `x > 0`), where the squared identity rewrites the first sum. -/
def interpBracket (x : ℝ) : ℝ :=
  (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2) - tailSum x + 2 * x⁻¹

/-- The odd interpolant `H(x) = (sin πx / π)² · B(x)`.

At the integers (where `sin πx = 0`) the series `B` has a pole and the product
`(sin πx/π)²·B` is a removable singularity; the honest value of the interpolant
there is `sgn x` (Beurling's `B` *interpolates* `sgn` at the integers, and the Fejér
kernel `K` vanishes there).  We encode this removable value explicitly so the
definition is mathematically correct at every real `x`, not just off the integers. -/
def interpH (x : ℝ) : ℝ :=
  if Real.sin (π * x) = 0 then Real.sign x
  else (Real.sin (π * x) / π) ^ 2 * interpBracket x

/-- The Beurling majorant defect `φ(x) = H(x) + K(x) − sgn(x)`. -/
def phi (x : ℝ) : ℝ := interpH x + fejerK x - Real.sign x

/-! ## Basic positivity / value facts -/

/-- `K(x) ≥ 0`. -/
theorem fejerK_nonneg (x : ℝ) : 0 ≤ fejerK x := by
  unfold fejerK
  split
  · norm_num
  · positivity

/-! ## The classical squared cosecant identity -/

/-- The squared cotangent /
cosecant identity
`∑_{m∈ℤ} (x − m)⁻² = (π / sin πx)²` for `x ∉ ℤ`,
written here in the `ℕ`-split form that the rest of the proof consumes:
the full integer sum decomposes as `x⁻² + ∑_{m≥1}[(x−m)⁻²+(x+m)⁻²]`, so

`(∑_{k≥0}(x−(k+1))⁻²) + (∑_{k≥0}(x+(k+1))⁻²) + x⁻² = (π / sin πx)²`.

This is Vaaler's "well known" identity (the `−d/dx` of Mathlib's `cot_series_rep`).
We package its statement as a named `Prop` so the elementary part of Lemma 5 stays
modular.  The identity-theorem argument below proves it from Mathlib and supplies
it to the unconditional corollaries. -/
def VaalerSumInvSqIdentity : Prop :=
  ∀ x : ℝ, Real.sin (π * x) ≠ 0 →
    (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2) + (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2)
      + x⁻¹ ^ 2 = (π / Real.sin (π * x)) ^ 2

/-! ## The telescoping helper -/

/-- For `c > 0`, the telescoping series `∑_{k≥0} (c+k)⁻¹(c+k+1)⁻¹` has sum `c⁻¹`.
(`(c+k)⁻¹(c+k+1)⁻¹ = (c+k)⁻¹ − (c+k+1)⁻¹`; partial sums telescope to `c⁻¹ − (c+n)⁻¹`.) -/
theorem telescope_hasSum {c : ℝ} (hc : 0 < c) :
    HasSum (fun k : ℕ => (c + (k : ℝ))⁻¹ * (c + (k + 1 : ℝ))⁻¹) c⁻¹ := by
  -- the telescoping form
  set g : ℕ → ℝ := fun k => (c + (k : ℝ))⁻¹ with hg
  have hpos : ∀ k : ℕ, (0 : ℝ) < c + (k : ℝ) := by
    intro k; have : (0 : ℝ) ≤ (k : ℝ) := by positivity
    linarith
  -- term equals the difference g k − g (k+1)
  have hterm : ∀ k : ℕ,
      (c + (k : ℝ))⁻¹ * (c + (k + 1 : ℝ))⁻¹ = g k - g (k + 1) := by
    intro k
    have h1 : c + (k : ℝ) ≠ 0 := (hpos k).ne'
    have h2 : c + ((k : ℝ) + 1) ≠ 0 := by
      have := hpos (k + 1); push_cast at this; linarith
    rw [hg]
    push_cast
    field_simp
    ring
  -- partial sums: ∑_{i<n} (g i − g (i+1)) = g 0 − g n
  have hpartial : ∀ n : ℕ,
      ∑ i ∈ Finset.range n, (c + (i : ℝ))⁻¹ * (c + (i + 1 : ℝ))⁻¹
        = c⁻¹ - (c + (n : ℝ))⁻¹ := by
    intro n
    simp_rw [hterm]
    rw [Finset.sum_range_sub' g n]
    simp [hg]
  -- nonneg terms, bounded partial sums ⇒ summable
  have hnonneg : ∀ k : ℕ, (0 : ℝ) ≤ (c + (k : ℝ))⁻¹ * (c + (k + 1 : ℝ))⁻¹ := by
    intro k
    have h1 : (0 : ℝ) ≤ (c + (k : ℝ))⁻¹ := (inv_nonneg).mpr (hpos k).le
    have h2 : (0 : ℝ) ≤ (c + (k + 1 : ℝ))⁻¹ := by
      have := hpos (k + 1); push_cast at this
      exact (inv_nonneg).mpr this.le
    exact mul_nonneg h1 h2
  have hsummable : Summable (fun k : ℕ => (c + (k : ℝ))⁻¹ * (c + (k + 1 : ℝ))⁻¹) := by
    refine summable_of_sum_range_le hnonneg (c := c⁻¹) ?_
    intro n
    rw [hpartial n]
    have : (0 : ℝ) ≤ (c + (n : ℝ))⁻¹ := (inv_nonneg).mpr (hpos n).le
    linarith
  -- value via tendsto of partial sums
  rw [hsummable.hasSum_iff_tendsto_nat]
  simp_rw [hpartial]
  -- c⁻¹ − (c+n)⁻¹ → c⁻¹  since (c+n)⁻¹ → 0
  have htend : Tendsto (fun n : ℕ => (c + (n : ℝ))⁻¹) atTop (𝓝 0) := by
    have hcast : Tendsto (fun n : ℕ => c + (n : ℝ)) atTop atTop := by
      apply Filter.tendsto_atTop_add_const_left
      exact tendsto_natCast_atTop_atTop
    exact (tendsto_inv_atTop_zero).comp hcast
  have : Tendsto (fun n : ℕ => c⁻¹ - (c + (n : ℝ))⁻¹) atTop (𝓝 (c⁻¹ - 0)) :=
    Filter.Tendsto.const_sub _ htend
  simpa using this

/-! ## Summability of the comparison tail series `∑_{m≥1}(x+m)⁻²` -/

/-- For `x > 0`, the tail series `∑_{k≥0}(x+(k+1))⁻²` is summable (comparison with
the telescoping series `(x+k)⁻¹(x+k+1)⁻¹`, which has the finite sum `x⁻¹`). -/
theorem tailSum_summable {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 2) := by
  have hcmp : Summable (fun k : ℕ => (x + (k : ℝ))⁻¹ * (x + (k + 1 : ℝ))⁻¹) :=
    (telescope_hasSum hx).summable
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hcmp
  -- (x+(k+1))⁻² ≤ (x+k)⁻¹(x+(k+1))⁻¹  since 0 < x+k ≤ x+(k+1)
  have hk0 : (0 : ℝ) < x + (k : ℝ) := by positivity
  have hk1 : (0 : ℝ) < x + ((k : ℝ) + 1) := by positivity
  have hle : x + (k : ℝ) ≤ x + ((k : ℝ) + 1) := by linarith
  have : (x + ((k : ℝ) + 1))⁻¹ ≤ (x + (k : ℝ))⁻¹ := inv_anti₀ hk0 hle
  push_cast
  have hsq : (x + ((k : ℝ) + 1))⁻¹ ^ 2
      = (x + ((k : ℝ) + 1))⁻¹ * (x + ((k : ℝ) + 1))⁻¹ := sq (x + ((k : ℝ) + 1))⁻¹
  rw [hsq]
  apply mul_le_mul_of_nonneg_right this
  exact (inv_nonneg).mpr hk1.le

/-! ## The two elementary endpoint inequalities -/

/-- **Left endpoint (telescoping).**  For `x > 0`,
`∑_{m≥1}(x+m)⁻² ≤ x⁻¹`.  Termwise `(x+(k+1))⁻² ≤ (x+(k+1))⁻¹(x+(k+2))⁻¹`? — no, we
compare each `(x+(k+1))⁻²` to `(x+k)⁻¹(x+(k+1))⁻¹`, and the latter sums (telescopes)
to `x⁻¹`. -/
theorem tailSum_le_inv {x : ℝ} (hx : 0 < x) : tailSum x ≤ x⁻¹ := by
  unfold tailSum
  have hcmpHasSum : HasSum (fun k : ℕ => (x + (k : ℝ))⁻¹ * (x + (k + 1 : ℝ))⁻¹) x⁻¹ :=
    telescope_hasSum hx
  have hcmp := hcmpHasSum.summable
  have hsum := tailSum_summable hx
  have hle : ∀ k : ℕ,
      (x + (k + 1 : ℕ))⁻¹ ^ 2 ≤ (x + (k : ℝ))⁻¹ * (x + (k + 1 : ℝ))⁻¹ := by
    intro k
    have hk0 : (0 : ℝ) < x + (k : ℝ) := by positivity
    have hk1 : (0 : ℝ) < x + ((k : ℝ) + 1) := by positivity
    have hcmple : (x + ((k : ℝ) + 1))⁻¹ ≤ (x + (k : ℝ))⁻¹ :=
      inv_anti₀ hk0 (by linarith)
    push_cast
    rw [sq]
    exact mul_le_mul_of_nonneg_right hcmple ((inv_nonneg).mpr hk1.le)
  calc ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2
      ≤ ∑' k : ℕ, (x + (k : ℝ))⁻¹ * (x + (k + 1 : ℝ))⁻¹ :=
        Summable.tsum_le_tsum hle hsum hcmp
    _ = x⁻¹ := hcmpHasSum.tsum_eq

/-- **Right endpoint (AM–GM + telescoping).**  For `x > 0`,
`x⁻² + 2·∑_{m≥1}(x+m)⁻² ≥ 2 x⁻¹`.

Summing the AM–GM bound `2 (x+m)⁻¹(x+m+1)⁻¹ ≤ (x+m)⁻² + (x+m+1)⁻²` over `m ≥ 0`:
the LHS telescopes (`×2`) to `2 x⁻¹`, the RHS regroups to `x⁻² + 2 ∑_{m≥1}(x+m)⁻²`. -/
theorem two_inv_le_aux {x : ℝ} (hx : 0 < x) :
    2 * x⁻¹ ≤ x⁻¹ ^ 2 + 2 * tailSum x := by
  unfold tailSum
  -- the AM–GM termwise bound, indexed over k ≥ 0 (m = k)
  -- a k = (x+k)⁻¹ ,  term: 2·(x+k)⁻¹(x+k+1)⁻¹ ≤ (x+k)⁻² + (x+k+1)⁻²
  have hsum := tailSum_summable hx
  -- HasSum of the doubled telescoping series → 2 x⁻¹
  have hcmpHasSum : HasSum (fun k : ℕ => (x + (k : ℝ))⁻¹ * (x + (k + 1 : ℝ))⁻¹) x⁻¹ :=
    telescope_hasSum hx
  have hcmp2 : Summable (fun k : ℕ => 2 * ((x + (k : ℝ))⁻¹ * (x + (k + 1 : ℝ))⁻¹)) :=
    hcmpHasSum.summable.mul_left 2
  -- the RHS series R k = (x+k)⁻² + (x+(k+1))⁻²  is summable
  -- first, ∑ (x+k)⁻²  = x⁻² + tailSum   (reindex)
  have hAk_sum : Summable (fun k : ℕ => (x + (k : ℝ))⁻¹ ^ 2) := by
    -- summable as ∑_{k≥0} = (k=0 term) + tail
    rw [← summable_nat_add_iff 1]
    refine hsum.congr ?_
    intro k; push_cast; ring_nf
  have hRsum : Summable (fun k : ℕ =>
      (x + (k : ℝ))⁻¹ ^ 2 + (x + ((k : ℝ) + 1))⁻¹ ^ 2) := by
    refine hAk_sum.add ?_
    refine (hsum).congr ?_
    intro k; push_cast; ring_nf
  -- termwise AM–GM:  2 a b ≤ a² + b²  with a = (x+k)⁻¹, b = (x+(k+1))⁻¹
  have htermle : ∀ k : ℕ,
      2 * ((x + (k : ℝ))⁻¹ * (x + (k + 1 : ℝ))⁻¹)
        ≤ (x + (k : ℝ))⁻¹ ^ 2 + (x + ((k : ℝ) + 1))⁻¹ ^ 2 := by
    intro k
    have := two_mul_le_add_sq (x + (k : ℝ))⁻¹ (x + ((k : ℝ) + 1))⁻¹
    -- this : 2 * (x+k)⁻¹ * (x+(k+1))⁻¹ ≤ (x+k)⁻¹^2 + (x+(k+1))⁻¹^2
    calc 2 * ((x + (k : ℝ))⁻¹ * (x + (k + 1 : ℝ))⁻¹)
        = 2 * (x + (k : ℝ))⁻¹ * (x + ((k : ℝ) + 1))⁻¹ := by push_cast; ring
      _ ≤ (x + (k : ℝ))⁻¹ ^ 2 + (x + ((k : ℝ) + 1))⁻¹ ^ 2 := this
  -- compare tsums
  have hcmptsum : (∑' k : ℕ, 2 * ((x + (k : ℝ))⁻¹ * (x + (k + 1 : ℝ))⁻¹))
      ≤ ∑' k : ℕ, ((x + (k : ℝ))⁻¹ ^ 2 + (x + ((k : ℝ) + 1))⁻¹ ^ 2) :=
    Summable.tsum_le_tsum htermle hcmp2 hRsum
  -- LHS tsum = 2 x⁻¹
  have hLHS : (∑' k : ℕ, 2 * ((x + (k : ℝ))⁻¹ * (x + (k + 1 : ℝ))⁻¹)) = 2 * x⁻¹ := by
    rw [tsum_mul_left, hcmpHasSum.tsum_eq]
  -- RHS tsum = (x⁻² + tailSum) + tailSum = x⁻² + 2 tailSum
  have hAk_tsum : (∑' k : ℕ, (x + (k : ℝ))⁻¹ ^ 2)
      = x⁻¹ ^ 2 + ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2 := by
    rw [Summable.tsum_eq_zero_add hAk_sum]
    norm_num
  have hRHS : (∑' k : ℕ, ((x + (k : ℝ))⁻¹ ^ 2 + (x + ((k : ℝ) + 1))⁻¹ ^ 2))
      = x⁻¹ ^ 2 + 2 * ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2 := by
    rw [Summable.tsum_add hAk_sum
          ((hsum).congr (fun k => by push_cast; ring_nf)), hAk_tsum]
    have hsecond : (∑' k : ℕ, (x + ((k : ℝ) + 1))⁻¹ ^ 2)
        = ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2 := by
      apply tsum_congr; intro k; push_cast; ring_nf
    rw [hsecond]; ring
  rw [hLHS, hRHS] at hcmptsum
  exact hcmptsum

/-! ## The `H` rewrite for `x ∉ ℤ` (Vaaler eq (2.26)) -/

/-- For `x` with `sin πx ≠ 0`, `H(x) = 1 + (sin πx / π)² · { 2 x⁻¹ − x⁻² − 2·T(x) }`,
where `T(x) = ∑_{m≥1}(x+m)⁻²`.  (Vaaler eq (2.26); uses the squared identity to
rewrite `∑_{m≥1}(x−m)⁻²`.) -/
theorem interpH_rewrite (hId : VaalerSumInvSqIdentity) {x : ℝ} (hx : Real.sin (π * x) ≠ 0) :
    interpH x = 1 + (Real.sin (π * x) / π) ^ 2 * (2 * x⁻¹ - x⁻¹ ^ 2 - 2 * tailSum x) := by
  unfold interpH
  rw [if_neg hx]
  unfold interpBracket tailSum
  have hid := hId x hx
  -- abbreviate the two ℕ-sums
  set A := ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2 with hA
  set Bt := ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2 with hBt
  -- from identity:  A = (π/sin)² − Bt − x⁻²
  have hAval : A = (π / Real.sin (π * x)) ^ 2 - Bt - x⁻¹ ^ 2 := by
    have : A + Bt + x⁻¹ ^ 2 = (π / Real.sin (π * x)) ^ 2 := hid
    linarith
  rw [hAval]
  -- (sin/π)² · ((π/sin)² − Bt − x⁻² − Bt + 2x⁻¹) = (sin/π)²·(π/sin)² + (sin/π)²·(...)
  have hsinπ : (Real.sin (π * x) / π) ^ 2 * (π / Real.sin (π * x)) ^ 2 = 1 := by
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp
  -- expand
  have : ((π / Real.sin (π * x)) ^ 2 - Bt - x⁻¹ ^ 2 - Bt + 2 * x⁻¹)
      = (π / Real.sin (π * x)) ^ 2 + (2 * x⁻¹ - x⁻¹ ^ 2 - 2 * Bt) := by ring
  rw [this, mul_add, hsinπ]

/-! ## The endpoint inequalities `1 − K(x) ≤ H(x)` and `H(x) ≤ 1` for `x > 0` -/

/-- For `x > 0`, `H(x) ≤ 1` (Vaaler eq (2.25), right). -/
theorem interpH_le_one (hId : VaalerSumInvSqIdentity) {x : ℝ} (hx : 0 < x) : interpH x ≤ 1 := by
  by_cases hs : Real.sin (π * x) = 0
  · -- removable value: H(x) = sgn x = 1 ≤ 1
    have h1 : interpH x = 1 := by unfold interpH; rw [if_pos hs, Real.sign_of_pos hx]
    exact le_of_eq h1
  · rw [interpH_rewrite hId hs]
    -- need (sin/π)²·(2x⁻¹ − x⁻² − 2T) ≤ 0; i.e. 2x⁻¹ − x⁻² − 2T ≤ 0
    have hbracket : 2 * x⁻¹ - x⁻¹ ^ 2 - 2 * tailSum x ≤ 0 := by
      have := two_inv_le_aux hx; linarith
    have hcoef : (0 : ℝ) ≤ (Real.sin (π * x) / π) ^ 2 := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef hbracket]

/-- For `x > 0`, `1 − K(x) ≤ H(x)` (Vaaler eq (2.25), left). -/
theorem one_sub_fejerK_le_interpH (hId : VaalerSumInvSqIdentity) {x : ℝ} (hx : 0 < x) :
    1 - fejerK x ≤ interpH x := by
  by_cases hs : Real.sin (π * x) = 0
  · -- removable value: H(x) = sgn x = 1, and K(x) = (sin/π)²·x⁻² = 0, so 1 − 0 ≤ 1.
    have hKzero : fejerK x = 0 := by
      unfold fejerK
      rw [if_neg hx.ne', hs]; ring
    have hH1 : interpH x = 1 := by unfold interpH; rw [if_pos hs, Real.sign_of_pos hx]
    rw [hH1, hKzero]; norm_num
  · rw [interpH_rewrite hId hs]
    -- K(x) = (sin/π)²·x⁻²  (x ≠ 0)
    have hKeq : fejerK x = (Real.sin (π * x) / π) ^ 2 * x⁻¹ ^ 2 := by
      unfold fejerK; rw [if_neg hx.ne']
    rw [hKeq]
    -- reduce to (sin/π)²·(2x⁻¹ − 2T) ≥ 0, which holds since T ≤ x⁻¹
    have hTle : tailSum x ≤ x⁻¹ := tailSum_le_inv hx
    have hcoef : (0 : ℝ) ≤ (Real.sin (π * x) / π) ^ 2 := by positivity
    nlinarith [mul_nonneg hcoef (by linarith : (0:ℝ) ≤ 2 * x⁻¹ - 2 * tailSum x)]

/-! ## Assembly -/

/-- Oddness of `Real.sign`: for the reflection argument. -/
theorem interpH_neg (x : ℝ) : interpH (-x) = - interpH x := by
  unfold interpH interpBracket tailSum
  have hsin : Real.sin (π * (-x)) = - Real.sin (π * x) := by
    rw [show π * (-x) = -(π * x) by ring, Real.sin_neg]
  by_cases hs : Real.sin (π * x) = 0
  · rw [hsin, hs]; simp [Real.sign_neg]
  · have hs' : Real.sin (π * (-x)) ≠ 0 := by rw [hsin]; simpa using hs
    rw [if_neg hs', if_neg hs, hsin]
    -- (−sin)² = sin²; and the bracket is odd:
    --   A(−x)=∑(−x−(k+1))⁻²=∑(x+(k+1))⁻²=tailSum x;  T(−x)=∑(−x+(k+1))⁻²=∑(x−(k+1))⁻²
    --   so bracket(−x) = tailSum x − (∑(x−(k+1))⁻²) + 2(−x)⁻¹ = −bracket(x).
    have hAneg : (∑' k : ℕ, (-x - (k + 1 : ℕ))⁻¹ ^ 2)
        = ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2 := by
      apply tsum_congr; intro k
      rw [show (-x - (k + 1 : ℕ)) = -(x + (k + 1 : ℕ)) by push_cast; ring,
        inv_neg, neg_pow, neg_one_sq]; ring_nf
    have hTneg : (∑' k : ℕ, (-x + (k + 1 : ℕ))⁻¹ ^ 2)
        = ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2 := by
      apply tsum_congr; intro k
      rw [show (-x + (k + 1 : ℕ)) = -(x - (k + 1 : ℕ)) by push_cast; ring,
        inv_neg, neg_pow, neg_one_sq]; ring_nf
    rw [show ((-Real.sin (π * x)) / π) ^ 2 = (Real.sin (π * x) / π) ^ 2 by ring]
    rw [hAneg, hTneg]
    have hxinv : (-x)⁻¹ = -x⁻¹ := by rw [inv_neg]
    rw [hxinv]; ring

/-- **Vaaler Lemma 5 (majorant side).**  `φ = H + K − sgn ≥ 0` for every real `x`. -/
theorem vaaler_phi_nonneg (hId : VaalerSumInvSqIdentity) : ∀ x : ℝ, 0 ≤ phi x := by
  intro x
  unfold phi
  rcases lt_trichotomy x 0 with hx | hx | hx
  · -- x < 0: reflect to y = -x > 0.  φ(x) = H(x)+K(x)−sgn(x); with H odd, K even.
    set y := -x with hy
    have hypos : 0 < y := by rw [hy]; linarith
    have hHy : interpH y = - interpH x := by rw [hy]; exact interpH_neg x
    have hHx : interpH x = - interpH y := by rw [hHy]; ring
    have hKx : fejerK x = fejerK y := by
      unfold fejerK
      rw [hy]
      rw [show π * (-x) = -(π * x) by ring, Real.sin_neg]
      by_cases hxz : x = 0
      · simp [hxz]
      · rw [if_neg hxz, if_neg (by simpa [hy] using (by linarith : x ≠ 0) : -x ≠ 0)]
        rw [inv_neg]; ring
    have hsgn : Real.sign x = - Real.sign y := by
      rw [hy, Real.sign_neg]; ring
    rw [hHx, hKx, hsgn]
    -- need 0 ≤ −H(y)+K(y)+sgn(y) = K(y) − (H(y) − sgn(y)) ; sgn(y)=1 (y>0)
    rw [Real.sign_of_pos hypos]
    -- H(y) ≤ 1 and 0 ≤ K(y):  −H(y) + K(y) + 1 ≥ −1 + 0 + 1 = 0
    have hH := interpH_le_one hId hypos
    have hK := fejerK_nonneg y
    linarith
  · -- x = 0: H(0)=sgn 0=0 (sin 0 = 0), K(0)=1, sgn 0 = 0 ⇒ φ = 0+1−0 = 1 ≥ 0
    subst hx
    have hsin0 : Real.sin (π * 0) = 0 := by simp
    unfold interpH fejerK
    rw [if_pos hsin0, if_pos rfl, Real.sign_zero]
    norm_num
  · -- x > 0: sgn x = 1, need H(x)+K(x) ≥ 1, i.e. 1 − K(x) ≤ H(x)
    rw [Real.sign_of_pos hx]
    have := one_sub_fejerK_le_interpH hId hx
    linarith

/-- **Vaaler Lemma 5 (minorant side).**  `H − K − sgn ≤ 0`, i.e. `H − K ≤ sgn`,
for every real `x`.  (Symmetric companion of `vaaler_phi_nonneg`.) -/
theorem vaaler_phi_minorant (hId : VaalerSumInvSqIdentity) :
    ∀ x : ℝ, interpH x - fejerK x - Real.sign x ≤ 0 := by
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · -- x < 0: H(x)−K(x)−sgn(x) = −H(y)−K(y)+1 ≤ 0  ⇔  H(y)+K(y) ≥ 1, the left ineq at y>0
    set y := -x with hy
    have hypos : 0 < y := by rw [hy]; linarith
    have hHy : interpH y = - interpH x := by rw [hy]; exact interpH_neg x
    have hHx : interpH x = - interpH y := by rw [hHy]; ring
    have hKx : fejerK x = fejerK y := by
      unfold fejerK
      rw [hy]
      rw [show π * (-x) = -(π * x) by ring, Real.sin_neg]
      by_cases hxz : x = 0
      · simp [hxz]
      · rw [if_neg hxz, if_neg (by simpa [hy] using (by linarith : x ≠ 0) : -x ≠ 0)]
        rw [inv_neg]; ring
    have hsgn : Real.sign x = - Real.sign y := by rw [hy, Real.sign_neg]; ring
    rw [hHx, hKx, hsgn, Real.sign_of_pos hypos]
    have := one_sub_fejerK_le_interpH hId hypos
    linarith
  · subst hx
    have hsin0 : Real.sin (π * 0) = 0 := by simp
    unfold interpH fejerK
    rw [if_pos hsin0, if_pos rfl, Real.sign_zero]
    norm_num
  · -- x > 0: H(x)−K(x)−1 ≤ 0 ⇔ H(x) ≤ 1 + K(x); since H≤1 and K≥0
    rw [Real.sign_of_pos hx]
    have hH := interpH_le_one hId hx
    have hK := fejerK_nonneg x
    linarith

/-! ## Discharge of the squared-cosecant identity

The proof below internalizes the classical analytic-continuation argument.  Its
helper declarations live in a nested namespace so the public names of this leaf
remain collision-free.
-/

namespace SumInvSqProof

local notation "ℂ_ℤ" => Complex.integerComplement
local notation "ℍₒ" => UpperHalfPlane.upperHalfPlaneSet

/-- The full integer Eisenstein-type sum `S z = ∑_{n∈ℤ} 1/(z+n)²`. -/
def S (z : ℂ) : ℂ := ∑' n : ℤ, 1 / (z + n) ^ 2

/-- The squared cosecant `C z = (π / sin (π z))²`. -/
def C (z : ℂ) : ℂ := ((π : ℂ) / Complex.sin (π * z)) ^ 2

/-- `ℂ_ℤ` is open. -/
theorem isOpen_integerComplement : IsOpen ℂ_ℤ := Complex.isOpen_compl_range_intCast

/-- For every `z`, the term family `n ↦ 1/(z+n)²` is summable over `ℤ`. -/
theorem summable_term (z : ℂ) : Summable (fun n : ℤ => 1 / (z + n) ^ 2) := by
  have h := EisensteinSeries.linear_right_summable z 1 (k := 2) (by norm_num)
  refine h.congr ?_
  intro n
  rw [Int.cast_one, one_mul, one_div]
  rfl

/-! ### Identity on the upper half-plane -/

/-- `Complex.cot` has derivative `-1/(sin z)²` wherever `sin z ≠ 0`. -/
theorem hasDerivAt_cot {z : ℂ} (hz : Complex.sin z ≠ 0) :
    HasDerivAt Complex.cot (-1 / (Complex.sin z) ^ 2) z := by
  have hcot : Complex.cot = fun w => Complex.cos w / Complex.sin w := by
    funext w
    exact Complex.cot_eq_cos_div_sin w
  rw [hcot]
  have hnum : HasDerivAt Complex.cos (-Complex.sin z) z := Complex.hasDerivAt_cos z
  have hden : HasDerivAt Complex.sin (Complex.cos z) z := Complex.hasDerivAt_sin z
  have hq := hnum.div hden hz
  refine hq.congr_deriv ?_
  have hpyth : Complex.sin z ^ 2 + Complex.cos z ^ 2 = 1 := Complex.sin_sq_add_cos_sq z
  have hnumerator :
      -Complex.sin z * Complex.sin z - Complex.cos z * Complex.cos z = -1 := by
    linear_combination -hpyth
  rw [hnumerator]

/-- `deriv (fun z => π * cot (π * z)) z = -(π/sin(πz))²` off the zeros of sine. -/
theorem deriv_pi_cot {z : ℂ} (hz : Complex.sin (π * z) ≠ 0) :
    deriv (fun w : ℂ => (π : ℂ) * Complex.cot (π * w)) z = -C z := by
  have hinner : HasDerivAt (fun w : ℂ => (π : ℂ) * w) (π : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (π : ℂ)
  have hcot : HasDerivAt Complex.cot (-1 / (Complex.sin (π * z)) ^ 2) (π * z) :=
    hasDerivAt_cot hz
  have hcomp : HasDerivAt (fun w : ℂ => Complex.cot (π * w))
      ((-1 / (Complex.sin (π * z)) ^ 2) * (π : ℂ)) z := hcot.comp z hinner
  have hfull : HasDerivAt (fun w : ℂ => (π : ℂ) * Complex.cot (π * w))
      ((π : ℂ) * ((-1 / (Complex.sin (π * z)) ^ 2) * (π : ℂ))) z :=
    hcomp.const_mul (π : ℂ)
  rw [hfull.deriv]
  unfold C
  have hsin : Complex.sin (π * z) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  rw [div_pow, mul_comm]
  field_simp

/-- The integer sum equals the squared cosecant on the upper half-plane. -/
theorem S_eq_C_on_upperHalfPlane {z : ℂ} (hz : z ∈ ℍₒ) : S z = C z := by
  have hmem : z ∈ ℂ_ℤ := UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩
  have hsin : Complex.sin (π * z) ≠ 0 := sin_pi_mul_ne_zero hmem
  have hmain := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k := 1) (by norm_num) hz
  rw [iteratedDerivWithin_one] at hmain
  rw [derivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hz] at hmain
  rw [deriv_pi_cot hsin] at hmain
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one, neg_mul, one_mul] at hmain
  show S z = C z
  unfold S
  have heq : (∑' n : ℤ, 1 / (z + (n : ℂ)) ^ (1 + 1)) =
      ∑' n : ℤ, 1 / (z + (n : ℂ)) ^ 2 := by
    norm_num
  rw [heq] at hmain
  exact (neg_injective hmain).symm

/-! ### Analytic continuation on the integer-complement -/

/-- Each summand is differentiable away from the integers. -/
theorem term_differentiableOn (n : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => 1 / (z + n) ^ 2) ℂ_ℤ := by
  apply DifferentiableOn.div
  · fun_prop
  · fun_prop
  · intro z hz
    have : z + (n : ℂ) ≠ 0 := Complex.integerComplement_add_ne_zero hz n
    exact pow_ne_zero 2 this

/-- The integer sum is differentiable at every point off the integers. -/
theorem S_differentiableAt {z₀ : ℂ} (hz₀ : z₀ ∈ ℂ_ℤ) : DifferentiableAt ℂ S z₀ := by
  classical
  set s : Set ℂ := Set.range ((↑) : ℤ → ℂ) with hs
  have hsclosed : IsClosed s := Complex.isClosed_range_intCast
  have hz₀s : z₀ ∉ s := hz₀
  have hsne : s.Nonempty := ⟨(0 : ℂ), ⟨0, by simp⟩⟩
  set δ : ℝ := Metric.infDist z₀ s with hδ
  have hδpos : 0 < δ := by
    rw [hδ, ← hsclosed.notMem_iff_infDist_pos hsne]
    exact hz₀s
  set r : ℝ := δ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hball_open : IsOpen (Metric.ball z₀ r) := Metric.isOpen_ball
  set u : ℤ → ℝ := fun n => 4 * ‖(1 : ℂ) / (z₀ + n) ^ 2‖ with hu
  have husum : Summable u := by
    refine Summable.mul_left 4 ?_
    exact (summable_term z₀).norm
  have hlb₀ : ∀ n : ℤ, δ ≤ ‖z₀ + (n : ℂ)‖ := by
    intro n
    have hmem : (-(n : ℂ)) ∈ s := ⟨-n, by push_cast; ring⟩
    have h := Metric.infDist_le_dist_of_mem (x := z₀) hmem
    rw [Complex.dist_eq] at h
    calc δ ≤ ‖z₀ - (-(n : ℂ))‖ := h
      _ = ‖z₀ + (n : ℂ)‖ := by rw [sub_neg_eq_add]
  have hbound : ∀ (n : ℤ) (z : ℂ), z ∈ Metric.ball z₀ r →
      ‖(1 : ℂ) / (z + n) ^ 2‖ ≤ u n := by
    intro n z hz
    have hzdist : ‖z - z₀‖ < r := by
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      exact hz
    have hge : ‖z₀ + (n : ℂ)‖ / 2 ≤ ‖z + (n : ℂ)‖ := by
      have htri : ‖z₀ + (n : ℂ)‖ - ‖z - z₀‖ ≤ ‖z + (n : ℂ)‖ := by
        have h : ‖z₀ + (n : ℂ)‖ ≤ ‖z + (n : ℂ)‖ + ‖z - z₀‖ := by
          calc ‖z₀ + (n : ℂ)‖ = ‖(z + (n : ℂ)) - (z - z₀)‖ := by ring_nf
            _ ≤ ‖z + (n : ℂ)‖ + ‖z - z₀‖ := norm_sub_le _ _
        linarith
      have hrle : r ≤ ‖z₀ + (n : ℂ)‖ / 2 := by
        have h := hlb₀ n
        rw [hr]
        linarith
      linarith
    have hz₀n_pos : 0 < ‖z₀ + (n : ℂ)‖ :=
      lt_of_lt_of_le (by have h := hlb₀ n; linarith) (hlb₀ n)
    have hzn_pos : 0 < ‖z + (n : ℂ)‖ := lt_of_lt_of_le (by linarith) hge
    have hlhs : ‖(1 : ℂ) / (z + (n : ℂ)) ^ 2‖ = 1 / ‖z + (n : ℂ)‖ ^ 2 := by
      rw [norm_div, norm_one, norm_pow]
    have hun : u n = 4 / ‖z₀ + (n : ℂ)‖ ^ 2 := by
      rw [hu]
      simp only [norm_div, norm_one, norm_pow]
      ring
    rw [hlhs, hun]
    have hsq : (‖z₀ + (n : ℂ)‖ / 2) ^ 2 ≤ ‖z + (n : ℂ)‖ ^ 2 := by
      apply sq_le_sq'
      · linarith [hge, hzn_pos]
      · exact hge
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq, hz₀n_pos, hzn_pos]
  have hball_sub : Metric.ball z₀ r ⊆ ℂ_ℤ := by
    intro z hz
    rw [Metric.mem_ball] at hz
    intro hzmem
    obtain ⟨m, hm⟩ := hzmem
    have h : δ ≤ dist z₀ z := by
      rw [hδ]
      exact Metric.infDist_le_dist_of_mem ⟨m, hm⟩
    rw [dist_comm] at h
    rw [hr] at hz
    linarith
  have hdiffOn : DifferentiableOn ℂ S (Metric.ball z₀ r) := by
    have h := Complex.differentiableOn_tsum_of_summable_norm (U := Metric.ball z₀ r)
      (F := fun n : ℤ => fun z : ℂ => (1 : ℂ) / (z + n) ^ 2) husum
      (fun n => (term_differentiableOn n).mono hball_sub) hball_open hbound
    exact h
  exact hdiffOn.differentiableAt (hball_open.mem_nhds (Metric.mem_ball_self hrpos))

/-- The integer sum is differentiable throughout `ℂ_ℤ`. -/
theorem S_differentiableOn : DifferentiableOn ℂ S ℂ_ℤ :=
  fun _ hz => (S_differentiableAt hz).differentiableWithinAt

/-- The squared cosecant is differentiable throughout `ℂ_ℤ`. -/
theorem C_differentiableOn : DifferentiableOn ℂ C ℂ_ℤ := by
  apply DifferentiableOn.pow
  apply DifferentiableOn.div
  · fun_prop
  · fun_prop
  · intro z hz
    exact sin_pi_mul_ne_zero hz

/-- `ℂ_ℤ` is preconnected. -/
theorem isPreconnected_integerComplement : IsPreconnected ℂ_ℤ := by
  have hcount : (Set.range ((↑) : ℤ → ℂ)).Countable := Set.countable_range _
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  exact (hcount.isConnected_compl_of_one_lt_rank hrank).isPreconnected

/-- Analytic continuation extends the identity to all of `ℂ_ℤ`. -/
theorem S_eq_C_on_integerComplement : Set.EqOn S C ℂ_ℤ := by
  have hSan : AnalyticOnNhd ℂ S ℂ_ℤ := S_differentiableOn.analyticOnNhd isOpen_integerComplement
  have hCan : AnalyticOnNhd ℂ C ℂ_ℤ := C_differentiableOn.analyticOnNhd isOpen_integerComplement
  have hI_upper : Complex.I ∈ ℍₒ := by
    show (0 : ℝ) < Complex.I.im
    simp
  have hI_mem : Complex.I ∈ ℂ_ℤ :=
    UpperHalfPlane.coe_mem_integerComplement ⟨Complex.I, hI_upper⟩
  have hev : S =ᶠ[𝓝 Complex.I] C := by
    apply Filter.eventuallyEq_of_mem (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hI_upper)
    intro z hz
    exact S_eq_C_on_upperHalfPlane hz
  exact hSan.eqOn_of_preconnected_of_eventuallyEq hCan
    isPreconnected_integerComplement hI_mem hev

/-! ### Specialization to the real line -/

/-- A real point with nonzero `sin (πx)` lies in `ℂ_ℤ`. -/
theorem ofReal_mem_integerComplement {x : ℝ} (hx : Real.sin (π * x) ≠ 0) :
    (x : ℂ) ∈ ℂ_ℤ := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hxn : x = (n : ℝ) := by exact_mod_cast hn.symm
  apply hx
  rw [hxn]
  rw [show π * (n : ℝ) = (n : ℝ) * π by ring, Real.sin_int_mul_pi]

/-- The squared-cosecant identity in the `ℕ`-split form consumed above. -/
theorem identity_holds : VaalerSumInvSqIdentity := by
  intro x hx
  have hmem : (x : ℂ) ∈ ℂ_ℤ := ofReal_mem_integerComplement hx
  have hSC : S (x : ℂ) = C (x : ℂ) := S_eq_C_on_integerComplement hmem
  set f : ℤ → ℂ := fun n => 1 / ((x : ℂ) + n) ^ 2 with hf
  have hsumZ : Summable f := summable_term (x : ℂ)
  have hsumP : Summable (fun n : ℕ => f (n + 1)) := by
    have hinj : Function.Injective (fun n : ℕ => ((n : ℤ) + 1)) := by
      intro a b hab
      simpa using hab
    have h := hsumZ.comp_injective hinj
    refine h.congr ?_
    intro n
    simp [hf]
  have hsumN : Summable (fun n : ℕ => f (-(n + 1))) := by
    have hinj : Function.Injective (fun n : ℕ => (-((n : ℤ) + 1))) := by
      intro a b hab
      simpa using hab
    have h := hsumZ.comp_injective hinj
    refine h.congr ?_
    intro n
    simp [hf]
  have hsplit : (∑' n : ℤ, f n) =
      (∑' n : ℕ, f (n + 1)) + f 0 + ∑' n : ℕ, f (-(n + 1)) :=
    tsum_of_add_one_of_neg_add_one hsumP hsumN
  have hSsplit : S (x : ℂ) =
      (∑' n : ℕ, f (n + 1)) + f 0 + ∑' n : ℕ, f (-(n + 1)) := by
    rw [show S (x : ℂ) = ∑' n : ℤ, f n from rfl, hsplit]
  have hPcast : (∑' n : ℕ, f (n + 1)) =
      ((∑' n : ℕ, (x + ((n : ℕ) + 1 : ℕ))⁻¹ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr ?_
    intro n
    rw [hf]
    push_cast [one_div, inv_pow]
    ring_nf
  have hNcast : (∑' n : ℕ, f (-(n + 1))) =
      ((∑' n : ℕ, (x - ((n : ℕ) + 1 : ℕ))⁻¹ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr ?_
    intro n
    rw [hf]
    push_cast [one_div, inv_pow]
    ring_nf
  have hCcast : f 0 = ((x⁻¹ ^ 2 : ℝ) : ℂ) := by
    rw [hf]
    push_cast [one_div, inv_pow]
    norm_num
  have hCval : C (x : ℂ) = (((π / Real.sin (π * x)) ^ 2 : ℝ) : ℂ) := by
    rw [show C (x : ℂ) = ((π : ℂ) / Complex.sin (π * x)) ^ 2 from rfl]
    rw [show ((π : ℂ) * (x : ℂ)) = ((π * x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sin]
    push_cast
    ring
  rw [hSsplit, hPcast, hNcast, hCcast, hCval] at hSC
  have hSC' : (((∑' n : ℕ, (x + ((n : ℕ) + 1 : ℕ))⁻¹ ^ 2)
        + x⁻¹ ^ 2 + ∑' n : ℕ, (x - ((n : ℕ) + 1 : ℕ))⁻¹ ^ 2 : ℝ) : ℂ) =
      (((π / Real.sin (π * x)) ^ 2 : ℝ) : ℂ) := by
    push_cast at hSC ⊢
    linear_combination hSC
  have hreal := Complex.ofReal_injective hSC'
  linarith [hreal]

end SumInvSqProof

/-- **Unconditional squared-cosecant identity.** -/
theorem vaalerSumInvSqIdentity_holds : VaalerSumInvSqIdentity :=
  SumInvSqProof.identity_holds

/-- **Unconditional Vaaler Lemma 5, majorant side.** -/
theorem vaaler_phi_nonneg_holds : ∀ x : ℝ, 0 ≤ phi x :=
  vaaler_phi_nonneg vaalerSumInvSqIdentity_holds

/-- **Unconditional Vaaler Lemma 5, minorant side.** -/
theorem vaaler_phi_minorant_holds :
    ∀ x : ℝ, interpH x - fejerK x - Real.sign x ≤ 0 :=
  vaaler_phi_minorant vaalerSumInvSqIdentity_holds

#print axioms vaaler_phi_nonneg
#print axioms vaaler_phi_minorant
#print axioms vaalerSumInvSqIdentity_holds
#print axioms vaaler_phi_nonneg_holds
#print axioms vaaler_phi_minorant_holds

end MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
