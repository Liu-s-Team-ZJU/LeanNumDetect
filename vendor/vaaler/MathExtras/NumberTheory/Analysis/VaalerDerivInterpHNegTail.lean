/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerDerivInterpHProbe

/-!
# D-1: term-by-term derivative of the NEGATIVE tail of `interpBracket`

This NEW leaf advances the D-1 wall isolated by `VaalerDerivInterpHProbe`
(`DerivInterpHClosedForm`).  That probe PROVED the *positive*-tail derivative
`hasDerivAt_posTail` (the tsum `∑ (x+(k+1))⁻²` has no poles on `(0,∞)`, so the
`ball ⊆ (0,∞)` envelope closed it).  Here we close the genuinely harder half: the
*negative* tail

    negTailSum x = ∑'_k (x − (k+1))⁻²

whose terms have poles at every positive integer.  Mirroring
`VaalerSumInvSqProof.S_differentiableAt` (which handled the complex Eisenstein sum
`∑ 1/(z+n)²` on `ℂ ∖ ℤ` by a `infDist`-ball uniform bound), we replace the
"`ball ⊆ (0,∞)`" trick by an "`infDist`-ball `⊆ ℝ ∖ ℤ`" trick over the reals and
apply Mathlib's `hasDerivAt_tsum_of_isPreconnected` to the *cube* derivative series.

## What is PROVEN here (sorry/axiom-free, non-vacuous)

* `summable_invSq_shift_neg` — for `x ∉ ℤ`, `∑'_k (x−(k+1))⁻²` is summable
  (comparison with the `p = 2` series after translating past `x`).
* `summable_invCube_shift_neg` — for `x ∉ ℤ`, `∑'_k |x−(k+1)|⁻³` is summable.
* `negTail_localUnifBound` — on the `infDist`-ball `ball x₀ (δ/2) ⊆ ℝ∖ℤ`
  (`δ = infDist x₀ (range Int.cast)`), the cube-derivative term is uniformly
  dominated by a summable envelope — the exact `‖g′ n y‖ ≤ u n` input to
  `hasDerivAt_tsum_of_isPreconnected`.
* `hasDerivAt_negTailSum` — **closed form** `HasDerivAt negTailSum (∑'_k −2(x−(k+1))⁻³) x`
  for `x ∉ ℤ`: term-by-term differentiation of the negative tail tsum.  DONE.
* `hasDerivAt_interpBracket` — **closed form** for `deriv interpBracket` for
  `0 < x`, `x ∉ ℤ`: assembles the negative tail (this file) + the positive tail and
  `2x⁻¹` parts (from the probe) into one `HasDerivAt`.
* `hasDerivAt_interpH` — **closed form** for `deriv interpH` for `0 < x`, `x ∉ ℤ`,
  via the product rule through the `(sin πx/π)²` prefactor.

## The single named residual (NOT an axiom)

The remaining identification of the proven closed-form `deriv interpH` with
`2·vaalerJ` (Vaaler Theorem 6, the J-Fourier-transform computation, eqs (2.27)–(2.32))
stays bundled in ONE named `Prop` `DerivInterpHEqTwoJ`, never an `axiom`.

## Hard constraints honoured

NEW leaf only; nothing existing/committed edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.  Build
green; `#print axioms` of each result is `[propext, Classical.choice, Quot.sound]`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2.
-/

noncomputable section

open Real Filter Topology Metric
open scoped BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail

open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerDerivInterpHProbe

/-! ## §0 — The negative-tail sum -/

/-- The negative bracket tail `negTailSum x = ∑_{k≥0} (x − (k+1))⁻²`, exactly the
first summand of `interpBracket`. -/
def negTailSum (x : ℝ) : ℝ := ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2

/-! ## §1 — Summability of the negative tail and its cube envelope -/

/-- For `x ∉ ℤ` (here `x` real, no integrality assumption needed for *summability*,
since the junk value `0⁻²` only affects finitely many terms), the negative tail
`∑_k (x−(k+1))⁻²` is summable.

Proof: for `k+1 > x` we have `(x−(k+1))⁻² = ((k+1)−x)⁻²`; after shifting the index
past `⌈x⌉` the base grows like `k`, so we compare with the `p = 2` series. -/
theorem summable_invSq_shift_neg (x : ℝ) :
    Summable (fun k : ℕ => (x - (k + 1 : ℕ))⁻¹ ^ 2) := by
  -- choose N with N ≥ x, so for k ≥ N : (k+1) - x ≥ 1 > 0
  obtain ⟨N, hN⟩ := exists_nat_gt x
  -- summable iff summable after dropping the first N terms
  rw [← summable_nat_add_iff N]
  -- compare with the summable series 1/(k+1)² (shifted p-series)
  have hpser : Summable (fun k : ℕ => ((k : ℝ) + 1)⁻¹ ^ 2) := by
    have : Summable (fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹) := by
      have hp : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
        Real.summable_nat_pow_inv.mpr (by norm_num)
      rw [← summable_nat_add_iff 1] at hp
      refine hp.congr ?_
      intro k; push_cast; ring_nf
    refine this.congr ?_
    intro k; rw [inv_pow]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hpser
  -- for index k : real index is N + k, term (x − (N+k+1))⁻²
  -- base : (N+k+1) − x ≥ (k+1)  since N ≥ x  ⇒  N + k + 1 − x ≥ k + 1
  have hbase_pos : (0 : ℝ) < (N : ℝ) + (k : ℝ) + 1 - x := by
    have : (N : ℝ) ≤ (N : ℝ) := le_refl _
    nlinarith [hN, Nat.cast_nonneg (α := ℝ) k]
  have hge : ((k : ℝ) + 1) ≤ (N : ℝ) + (k : ℝ) + 1 - x := by
    nlinarith [hN.le]
  -- (x − (N+k+1))⁻² = ((N+k+1) − x)⁻²  ≤  (k+1)⁻²
  have hcast : (x - ((k + N : ℕ) + 1 : ℕ) : ℝ) = -(((N : ℝ) + (k : ℝ) + 1) - x) := by
    push_cast; ring
  rw [hcast]
  have hsimp : (-(((N : ℝ) + (k : ℝ) + 1) - x))⁻¹ ^ 2
      = (((N : ℝ) + (k : ℝ) + 1) - x)⁻¹ ^ 2 := by
    rw [← neg_inv, neg_pow]; simp
  rw [hsimp, inv_pow, inv_pow]
  have hpos1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hsqle : ((k : ℝ) + 1) ^ 2 ≤ (((N : ℝ) + (k : ℝ) + 1) - x) ^ 2 := by
    apply sq_le_sq'
    · nlinarith [hbase_pos, hpos1]
    · linarith
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  · linarith [hsqle]

/-- For `x ∉ ℤ`, the absolute cube tail `∑_k |x−(k+1)|⁻³` is summable.  Same shift /
`p = 3` comparison. -/
theorem summable_invCube_shift_neg (x : ℝ) :
    Summable (fun k : ℕ => |x - (k + 1 : ℕ)|⁻¹ ^ 3) := by
  obtain ⟨N, hN⟩ := exists_nat_gt x
  rw [← summable_nat_add_iff N]
  have hpser : Summable (fun k : ℕ => ((k : ℝ) + 1)⁻¹ ^ 3) := by
    have : Summable (fun k : ℕ => (((k : ℝ) + 1) ^ 3)⁻¹) := by
      have hp : Summable (fun n : ℕ => ((n : ℝ) ^ 3)⁻¹) :=
        Real.summable_nat_pow_inv.mpr (by norm_num)
      rw [← summable_nat_add_iff 1] at hp
      refine hp.congr ?_
      intro k; push_cast; ring_nf
    refine this.congr ?_
    intro k; rw [inv_pow]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hpser
  have hbase_pos : (0 : ℝ) < (N : ℝ) + (k : ℝ) + 1 - x := by
    nlinarith [hN, Nat.cast_nonneg (α := ℝ) k]
  have hge : ((k : ℝ) + 1) ≤ (N : ℝ) + (k : ℝ) + 1 - x := by
    nlinarith [hN.le]
  have hcast : (x - ((k + N : ℕ) + 1 : ℕ) : ℝ) = -(((N : ℝ) + (k : ℝ) + 1) - x) := by
    push_cast; ring
  rw [hcast, abs_neg, abs_of_pos hbase_pos]
  have hpos1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [inv_pow, inv_pow, inv_le_inv₀ (by positivity) (by positivity)]
  · apply pow_le_pow_left₀ hpos1.le hge

/-! ## §2 — The `infDist`-ball uniform bound, mirroring `S_differentiableAt` -/

/-- Per-term derivative of the negative-tail summand `(y−(k+1))⁻²`, for `y ≠ k+1`:
`d/dy (y−(k+1))⁻² = −2 (y−(k+1))⁻³`.  (Specialization of the probe's
`hasDerivAt_invSq_shift` at the shift `c = k+1`.) -/
theorem hasDerivAt_negTail_term (k : ℕ) {y : ℝ} (hy : y - (k + 1 : ℕ) ≠ 0) :
    HasDerivAt (fun z : ℝ => (z - (k + 1 : ℕ))⁻¹ ^ 2)
      (-2 * (y - (k + 1 : ℕ))⁻¹ ^ 3) y :=
  hasDerivAt_invSq_shift (k + 1 : ℕ) y hy

/-- **The `infDist`-ball local uniform bound (mirror of `S_differentiableAt`).**
For `x₀ ∉ ℤ`, set `δ = infDist x₀ (range Int.cast)`, `r = δ/2`.  On `ball x₀ r`,
the cube-derivative term `‖−2(y−(k+1))⁻³‖` is dominated by the summable envelope
`u k = 16·|x₀−(k+1)|⁻³`, and the ball is contained in `ℝ ∖ ℤ`. -/
theorem negTail_localUnifBound {x₀ : ℝ} (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ r : ℝ, 0 < r ∧ (Metric.ball x₀ r ⊆ (Set.range ((↑) : ℤ → ℝ))ᶜ) ∧
      Summable (fun k : ℕ => 16 * |x₀ - (k + 1 : ℕ)|⁻¹ ^ 3) ∧
      (∀ (k : ℕ) (y : ℝ), y ∈ Metric.ball x₀ r →
        ‖-2 * (y - (k + 1 : ℕ))⁻¹ ^ 3‖ ≤ 16 * |x₀ - (k + 1 : ℕ)|⁻¹ ^ 3) := by
  classical
  set s : Set ℝ := Set.range ((↑) : ℤ → ℝ) with hs
  have hsclosed : IsClosed s := Real.isClosed_range_intCast
  have hsne : s.Nonempty := ⟨(0 : ℝ), ⟨0, by simp⟩⟩
  set δ : ℝ := Metric.infDist x₀ s with hδ
  have hδpos : 0 < δ := by
    rw [hδ, ← hsclosed.notMem_iff_infDist_pos hsne]; exact hx₀
  set r : ℝ := δ / 2 with hr
  have hrpos : 0 < r := by positivity
  -- lower bound on |x₀ − (k+1)| ≥ δ  (since (k+1) ∈ s)
  have hlb₀ : ∀ k : ℕ, δ ≤ |x₀ - (k + 1 : ℕ)| := by
    intro k
    have hmem : ((k + 1 : ℕ) : ℝ) ∈ s := ⟨(k + 1 : ℕ), by push_cast; ring⟩
    have := Metric.infDist_le_dist_of_mem (x := x₀) hmem
    rwa [Real.dist_eq] at this
  refine ⟨r, hrpos, ?_, ?_, ?_⟩
  · -- ball ⊆ sᶜ
    intro z hz
    rw [Metric.mem_ball] at hz
    intro hzmem
    obtain ⟨m, hm⟩ := hzmem
    have : δ ≤ dist x₀ z := by rw [hδ]; exact Metric.infDist_le_dist_of_mem ⟨m, hm⟩
    rw [dist_comm] at this; rw [hr] at hz; linarith
  · -- envelope summable
    exact (summable_invCube_shift_neg x₀).mul_left 16
  · -- uniform bound
    intro k y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    -- |y − (k+1)| ≥ |x₀−(k+1)| − |y−x₀| ≥ δ − r = δ/2 = |x₀−(k+1)|/...
    -- use the S_differentiableAt trick: |y−(k+1)| ≥ |x₀−(k+1)|/2
    have hge : |x₀ - (k + 1 : ℕ)| / 2 ≤ |y - (k + 1 : ℕ)| := by
      have htri : |x₀ - (k + 1 : ℕ)| - |y - x₀| ≤ |y - (k + 1 : ℕ)| := by
        have : |x₀ - (k + 1 : ℕ)| ≤ |y - (k + 1 : ℕ)| + |y - x₀| := by
          calc |x₀ - (k + 1 : ℕ)| = |(y - (k + 1 : ℕ)) - (y - x₀)| := by ring_nf
            _ ≤ |y - (k + 1 : ℕ)| + |y - x₀| := abs_sub _ _
        linarith
      have hrle : |y - x₀| ≤ |x₀ - (k + 1 : ℕ)| / 2 := by
        have h1 := hlb₀ k; rw [hr] at hy; linarith
      linarith
    have hx0n_pos : 0 < |x₀ - (k + 1 : ℕ)| := lt_of_lt_of_le hδpos (hlb₀ k)
    have hyn_pos : 0 < |y - (k + 1 : ℕ)| := lt_of_lt_of_le (by linarith) hge
    -- ‖−2(y−(k+1))⁻³‖ = 2 |y−(k+1)|⁻³  ≤  2·8·|x₀−(k+1)|⁻³ = 16·...
    have hnormterm : ‖-2 * (y - (k + 1 : ℕ))⁻¹ ^ 3‖ = 2 * |y - (k + 1 : ℕ)|⁻¹ ^ 3 := by
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : |(-2 : ℝ)| = 2 := by norm_num
      rw [h2, abs_pow, abs_inv]
    rw [hnormterm]
    -- |y−(k+1)|⁻¹ ≤ 2 |x₀−(k+1)|⁻¹  (from |x₀−(k+1)|/2 ≤ |y−(k+1)|)
    have hinv : |y - (k + 1 : ℕ)|⁻¹ ≤ 2 * |x₀ - (k + 1 : ℕ)|⁻¹ := by
      have hhalfpos : (0 : ℝ) < |x₀ - (k + 1 : ℕ)| / 2 := by positivity
      have := inv_anti₀ hhalfpos hge
      calc |y - (k + 1 : ℕ)|⁻¹ ≤ (|x₀ - (k + 1 : ℕ)| / 2)⁻¹ := this
        _ = 2 * |x₀ - (k + 1 : ℕ)|⁻¹ := by rw [inv_div]; ring
    -- cube the inequality
    have hcube : |y - (k + 1 : ℕ)|⁻¹ ^ 3 ≤ (2 * |x₀ - (k + 1 : ℕ)|⁻¹) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hinv 3
    have hexp : (2 * |x₀ - (k + 1 : ℕ)|⁻¹) ^ 3 = 8 * |x₀ - (k + 1 : ℕ)|⁻¹ ^ 3 := by ring
    rw [hexp] at hcube
    nlinarith [hcube, inv_pos.mpr hx0n_pos]

/-! ## §3 — CLOSED FORM: term-by-term differentiation of the negative tail tsum -/

set_option maxHeartbeats 1000000 in
/-- **Closed form for `deriv negTailSum` off ℤ (the hard half of sub-fact (i)).**
For `x ∉ ℤ`, `HasDerivAt negTailSum (∑'_k −2(x−(k+1))⁻³) x`: the negative tail tsum
may be differentiated term by term.  Unlike the probe's positive tail (no poles on
`(0,∞)`), this tail has poles at every positive integer, so the local-uniform bound
runs on the `infDist`-ball `⊆ ℝ∖ℤ` of `negTail_localUnifBound` rather than
`ball ⊆ (0,∞)`.  Direct mirror of `VaalerSumInvSqProof.S_differentiableAt`. -/
theorem hasDerivAt_negTailSum {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt negTailSum (∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3) x := by
  obtain ⟨r, hrpos, hball_sub, hUsum, hUbound⟩ := negTail_localUnifBound hx
  set t : Set ℝ := Metric.ball x r with ht
  have htopen : IsOpen t := Metric.isOpen_ball
  have htconn : IsPreconnected t := (convex_ball x r).isPreconnected
  have hxmem : x ∈ t := Metric.mem_ball_self hrpos
  -- per-term HasDerivAt on t (each y ∈ ball ⊆ ℝ∖ℤ, so y − (k+1) ≠ 0)
  have hg : ∀ (k : ℕ) (y : ℝ), y ∈ t →
      HasDerivAt (fun z : ℝ => (z - (k + 1 : ℕ))⁻¹ ^ 2)
        (-2 * (y - (k + 1 : ℕ))⁻¹ ^ 3) y := by
    intro k y hy
    have hyc : y ∈ (Set.range ((↑) : ℤ → ℝ))ᶜ := hball_sub hy
    have hne : y - (k + 1 : ℕ) ≠ 0 := by
      intro h
      apply hyc
      refine ⟨(k + 1 : ℕ), ?_⟩
      push_cast; push_cast at h; linarith
    exact hasDerivAt_negTail_term k hne
  -- convergence at the base point x
  have hg0 : Summable (fun k : ℕ => (x - (k + 1 : ℕ))⁻¹ ^ 2) := summable_invSq_shift_neg x
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := fun k : ℕ => 16 * |x - (k + 1 : ℕ)|⁻¹ ^ 3)
    (g := fun (k : ℕ) (z : ℝ) => (z - (k + 1 : ℕ))⁻¹ ^ 2)
    (g' := fun (k : ℕ) (y : ℝ) => -2 * (y - (k + 1 : ℕ))⁻¹ ^ 3)
    hUsum htopen htconn hg hUbound hxmem hg0 hxmem
  have hfun : negTailSum = fun z : ℝ => ∑' k : ℕ, (z - (k + 1 : ℕ))⁻¹ ^ 2 := by
    funext z; rfl
  rw [hfun]
  exact hmain

/-! ## §4 — CLOSED FORM: `deriv interpBracket` and `deriv interpH` -/

/-- **Closed form for `deriv interpBracket` (sub-fact (i) complete).**
For `0 < x`, `x ∉ ℤ`, `interpBracket = negTailSum − tailSum + 2x⁻¹` is differentiable
with the explicit derivative obtained by combining the negative-tail term-by-term
derivative (§3), the positive-tail term-by-term derivative (probe `hasDerivAt_posTail`),
and the elementary `d/dx (2x⁻¹) = −2x⁻²`. -/
theorem hasDerivAt_interpBracket {x : ℝ} (hxpos : 0 < x)
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt interpBracket
      ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3)
        + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) + 2 * (-(x⁻¹ ^ 2)))) x := by
  -- negative tail
  have hneg : HasDerivAt negTailSum (∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3) x :=
    hasDerivAt_negTailSum hx
  -- easy parts (−tailSum + 2x⁻¹) from the probe
  have heasy := hasDerivAt_bracket_easy_parts hxpos
  -- interpBracket = negTailSum + (−tailSum + 2x⁻¹)
  have hfun : interpBracket = fun z : ℝ => negTailSum z + (-tailSum z + 2 * z⁻¹) := by
    funext z
    unfold interpBracket negTailSum
    ring
  rw [hfun]
  exact hneg.add heasy

/-- `sin (π x) ≠ 0` for `x ∉ ℤ` (i.e. `x ∉ range Int.cast`). -/
theorem sin_pi_mul_ne_zero_of_notMem {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    Real.sin (π * x) ≠ 0 := by
  rw [Real.sin_ne_zero_iff]
  intro n hn
  apply hx
  refine ⟨n, ?_⟩
  -- n * π = π * x  ⇒  x = n
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hxe : (n : ℝ) * π = x * π := by rw [hn]; ring
  exact (mul_right_cancel₀ hπ hxe)

set_option maxHeartbeats 1000000 in
/-- **Closed form for `deriv interpH` off ℤ (sub-fact (i), the full interpolant).**
For `0 < x`, `x ∉ ℤ`, `interpH = (sin πx/π)²·interpBracket` (the removable-value
branch is not taken since `sin πx ≠ 0`), so by the product rule its derivative is
`H′(x) = 2·(sin πx/π)·cos(πx)·interpBracket(x) + (sin πx/π)²·interpBracket′(x)`,
with `interpBracket′` the closed form of `hasDerivAt_interpBracket`. -/
theorem hasDerivAt_interpH {x : ℝ} (hxpos : 0 < x)
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt interpH
      ((2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π)) * interpBracket x
        + (Real.sin (π * x) / π) ^ 2 *
          ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3)
            + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) + 2 * (-(x⁻¹ ^ 2))))) x := by
  have hsin : Real.sin (π * x) ≠ 0 := sin_pi_mul_ne_zero_of_notMem hx
  -- derivative of the prefactor (sin(πz)/π)²
  have hsinpi : HasDerivAt (fun z : ℝ => Real.sin (π * z)) (Real.cos (π * x) * π) x := by
    have hinner : HasDerivAt (fun z : ℝ => π * z) π x := by
      simpa using (hasDerivAt_id x).const_mul π
    exact (Real.hasDerivAt_sin (π * x)).comp x hinner
  have hdiv : HasDerivAt (fun z : ℝ => Real.sin (π * z) / π) (Real.cos (π * x) * π / π) x :=
    hsinpi.div_const π
  have hsq : HasDerivAt (fun z : ℝ => (Real.sin (π * z) / π) ^ 2)
      (2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π)) x := by
    refine ((hdiv.pow 2).congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards with z
    rfl
  -- derivative of interpBracket
  have hbr := hasDerivAt_interpBracket hxpos hx
  -- product rule for the unguarded function
  have hprod : HasDerivAt (fun z : ℝ => (Real.sin (π * z) / π) ^ 2 * interpBracket z)
      ((2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π)) * interpBracket x
        + (Real.sin (π * x) / π) ^ 2 *
          ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3)
            + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) + 2 * (-(x⁻¹ ^ 2))))) x := by
    refine (hsq.mul hbr).congr_of_eventuallyEq ?_
    filter_upwards with z
    rfl
  -- interpH agrees with the product on a neighbourhood of x (sin ≠ 0 there)
  have hcont : ContinuousAt (fun z : ℝ => Real.sin (π * z)) x := by
    apply Continuous.continuousAt
    exact Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hnhds : ∀ᶠ z : ℝ in nhds x, Real.sin (π * z) ≠ 0 :=
    hcont.eventually_ne hsin
  have heq : (fun z : ℝ => (Real.sin (π * z) / π) ^ 2 * interpBracket z)
      =ᶠ[nhds x] interpH := by
    filter_upwards [hnhds] with z hz
    unfold interpH
    rw [if_neg hz]
  exact hprod.congr_of_eventuallyEq heq.symm

/-! ## §5 — The single named residual (NOT an axiom): `H′ = 2·vaalerJ` -/

/-- **The remaining content of the D-1 wall, ONE named `Prop` (never an axiom).**
The closed-form `deriv interpH` (proven above by `hasDerivAt_interpH`) must be
identified with `2·vaalerJ` (Vaaler Theorem 6, the J-Fourier-transform computation,
eqs (2.27)–(2.32)).  That identity — not the existence/closed form of the
derivative, which is now PROVEN — is the only piece left. -/
def DerivInterpHEqTwoJ : Prop :=
  ∀ x : ℝ, 0 < x → x ∉ Set.range ((↑) : ℤ → ℝ) →
    ((2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π)) * interpBracket x
      + (Real.sin (π * x) / π) ^ 2 *
        ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3)
          + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) + 2 * (-(x⁻¹ ^ 2)))))
      = 2 * (MathExtras.NumberTheory.Analysis.VaalerCor7RouteB.vaalerJ x).re

#print axioms summable_invSq_shift_neg
#print axioms summable_invCube_shift_neg
#print axioms negTail_localUnifBound
#print axioms hasDerivAt_negTailSum
#print axioms hasDerivAt_interpBracket
#print axioms hasDerivAt_interpH

end MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail
