/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCor7RouteB

/-!
# D-1 de-risk probe: term-by-term differentiation of the Beurling interpolant `interpH`

This NEW leaf is a **de-risk probe** for the single remaining D-1 wall

    deriv interpH = 2 · J      on (0,∞)  and (−∞,0)      (Vaaler eq (2.32), J = ½H′)

isolated by both Route A (`Real.fourier_deriv`) and Route B (improper IBP,
`VaalerCor7RouteB`).  The wall decomposes into two sub-facts:

* **(i)** `deriv interpH` exists with a closed form off ℤ, via term-by-term
  differentiation of the bracket tsum `interpBracket` (Mathlib
  `hasDerivAt_tsum_of_isPreconnected`).
* **(ii)** the resulting function's Fourier transform equals the closed form
  `Ĵ = vaalerJhatFT` (Vaaler Theorem 6, eqs (2.27)–(2.32)).

This file PROVES the genuinely cheap pieces of (i) — the per-term derivatives, the
local uniform `‖g′ n y‖ ≤ u n` bound that powers `hasDerivAt_tsum_of_isPreconnected`
on a real ball off ℤ, the summability of the derivative series, and the closed-form
`HasDerivAt` for ONE of the two bracket tsums — and records the precise feasibility
verdict for the full wall.

## What is PROVEN here (sorry/axiom-free, non-vacuous)

* `hasDerivAt_invSq_shift` — per term `d/dx (x − c)⁻² = −2 (x − c)⁻³` for `x ≠ c`.
* `tailDerivSummable_pos` — for `x > 0`, the derivative series `∑ −2 (x+(k+1))⁻³`
  is summable (comparison, same envelope as `tailSum_summable`).
* `posTail_localUnifBound` — on a real ball `ball x₀ r ⊆ (0,∞)`, the uniform bound
  `‖−2(y+(k+1))⁻³‖ ≤ u k` with `u` summable, the exact input to
  `hasDerivAt_tsum_of_isPreconnected`.
* `hasDerivAt_posTail` — **closed form** `HasDerivAt (tailSum) (∑ −2(x+(k+1))⁻³) x`
  for `x > 0`: term-by-term differentiation of the positive tail tsum, DONE.

## The single named residual (NOT an axiom)

The remaining content of sub-fact (i) — the *negative* bracket tsum
`∑ (x−(k+1))⁻²` (whose terms have poles in `(0,∞)` at every positive integer, so the
"`ball ⊆ (0,∞)`" trick must be replaced by "`ball ⊆ ℝ ∖ ℤ`") and the product/`sin²`
factor — plus the whole of sub-fact (ii) (Vaaler Theorem 6's J-FT) are bundled into
ONE named `Prop` `DerivInterpHClosedForm`, never an `axiom`.

## Hard constraints honoured

NEW leaf only; nothing existing/committed edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.  Build
green; `#print axioms` of each result is `[propext, Classical.choice, Quot.sound]`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6 and eqs (2.27)–(2.34).
-/

noncomputable section

open Real Filter Topology Metric
open scoped BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerDerivInterpHProbe

open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg

/-! ## §1 — Per-term derivative: `d/dx (x − c)⁻² = −2 (x − c)⁻³` -/

/-- The single-term derivative `d/dx (x − c)⁻² = −2 (x − c)⁻³` for `x ≠ c`.
(Written with `(x − c)⁻¹ ^ 2` to match `interpBracket`'s shape.) -/
theorem hasDerivAt_invSq_shift (c x : ℝ) (hx : x - c ≠ 0) :
    HasDerivAt (fun y : ℝ => (y - c)⁻¹ ^ 2) (-2 * (x - c)⁻¹ ^ 3) x := by
  -- Differentiate the inverse and then square it.  This direct real-field route
  -- avoids the typeclass-coherence problems caused by normalising through
  -- integer powers.
  have hinner : HasDerivAt (fun y : ℝ => y - c) 1 x := by
    simpa using (hasDerivAt_id x).sub_const c
  have hinv := hinner.inv hx
  refine (hinv.pow 2).congr_deriv ?_
  simp only [Pi.inv_apply]
  field_simp [hx]
  have hcancel : (x - c) * (x - c)⁻¹ = 1 := mul_inv_cancel₀ hx
  calc
    _ = -2 * ((x - c) * (x - c)⁻¹) := by ring
    _ = -2 := by rw [hcancel]; ring

/-- Per-term derivative of the positive-tail summand `(y+(k+1))⁻²`, the shape that
appears in `tailSum`.  For `y > 0`: `d/dy (y+(k+1))⁻² = −2 (y+(k+1))⁻³`. -/
theorem hasDerivAt_posTail_term (k : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => (z + (k + 1 : ℕ))⁻¹ ^ 2)
      (-2 * (y + (k + 1 : ℕ))⁻¹ ^ 3) y := by
  have hx : y - (-(k + 1 : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < y + ((k : ℝ) + 1) := by positivity
    push_cast; intro h; nlinarith [this]
  have h := hasDerivAt_invSq_shift (-(k + 1 : ℕ) : ℝ) y hx
  -- (z − (−(k+1))) = z + (k+1)
  have hfun : (fun z : ℝ => (z - (-(k + 1 : ℕ) : ℝ))⁻¹ ^ 2)
      = fun z : ℝ => (z + (k + 1 : ℕ))⁻¹ ^ 2 := by
    funext z; rw [sub_neg_eq_add]
  rw [hfun] at h
  have hval : (-2 * (y - (-(k + 1 : ℕ) : ℝ))⁻¹ ^ 3) = -2 * (y + (k + 1 : ℕ))⁻¹ ^ 3 := by
    rw [sub_neg_eq_add]
  rw [hval] at h
  exact h

/-! ## §2 — Summability of the positive-tail derivative series `∑ −2 (y+(k+1))⁻³` -/

/-- For `x > 0`, the derivative series `∑_{k≥0} −2 (x+(k+1))⁻³` is absolutely
summable.  Comparison: `(x+(k+1))⁻³ ≤ (x+(k+1))⁻²` since `x+(k+1) ≥ 1`… actually we
just dominate by the proven-summable squared tail `(x+(k+1))⁻²` (each cube `≤` the
square when `x+(k+1) ≥ 1`, which holds for `x > 0` and `k ≥ 0`). -/
theorem tailDerivSummable_pos {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) := by
  apply Summable.mul_left
  -- ∑ (x+(k+1))⁻³ summable: dominate by the squared tail (cube ≤ square since base ≥ 1)
  have hsq : Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 2) := tailSum_summable hx
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsq
  have hb1 : (1 : ℝ) ≤ x + (k + 1 : ℕ) := by
    have : (0 : ℝ) ≤ x := hx.le
    push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hbpos : (0 : ℝ) < x + (k + 1 : ℕ) := by positivity
  have hinv : (x + (k + 1 : ℕ))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact hb1
  have hinvpos : (0 : ℝ) ≤ (x + (k + 1 : ℕ))⁻¹ := by positivity
  calc (x + (k + 1 : ℕ))⁻¹ ^ 3 = (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹ := by ring
    _ ≤ (x + (k + 1 : ℕ))⁻¹ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (x + (k + 1 : ℕ))⁻¹ ^ 2 := by ring

/-! ## §3 — The local uniform bound on a ball `⊆ (0,∞)` (input to `hasDerivAt_tsum`) -/

/-- On the ball `ball x₀ (x₀/2) ⊆ (0,∞)` (for `x₀ > 0`), the derivative term is
uniformly dominated by the summable envelope `u k = 2 (x₀/2 + (k+1))⁻³`.  This is
exactly the `‖g′ n y‖ ≤ u n` hypothesis of `hasDerivAt_tsum_of_isPreconnected`,
with `u` summable by `tailDerivSummable_pos` (at `x₀/2 > 0`). -/
theorem posTail_localUnifBound {x₀ : ℝ} (hx₀ : 0 < x₀) :
    (Summable (fun k : ℕ => 2 * (x₀ / 2 + (k + 1 : ℕ))⁻¹ ^ 3)) ∧
    (∀ (k : ℕ) (y : ℝ), y ∈ Metric.ball x₀ (x₀ / 2) →
      ‖-2 * (y + (k + 1 : ℕ))⁻¹ ^ 3‖ ≤ 2 * (x₀ / 2 + (k + 1 : ℕ))⁻¹ ^ 3) := by
  have hhalf : 0 < x₀ / 2 := by positivity
  refine ⟨?_, ?_⟩
  · -- envelope summable: −2·(...) negated, still summable; use tailDerivSummable_pos at x₀/2
    have := tailDerivSummable_pos hhalf
    -- this : Summable (k ↦ −2 (x₀/2+(k+1))⁻³); negate to get +2
    have hneg := this.neg
    refine hneg.congr ?_
    intro k; ring
  · intro k y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    -- |y − x₀| < x₀/2 ⇒ y > x₀/2 ⇒ y + (k+1) > x₀/2 + (k+1) > 0
    have hylb : x₀ / 2 < y := by
      rcases abs_lt.mp hy with ⟨h1, _⟩; linarith
    have hbpos : (0 : ℝ) < x₀ / 2 + (k + 1 : ℕ) := by positivity
    have hbpos2 : (0 : ℝ) < y + (k + 1 : ℕ) := by
      have : (0 : ℝ) ≤ (k + 1 : ℕ) := by positivity
      linarith
    have hle : x₀ / 2 + (k + 1 : ℕ) ≤ y + (k + 1 : ℕ) := by linarith
    have hinv : (y + (k + 1 : ℕ))⁻¹ ≤ (x₀ / 2 + (k + 1 : ℕ))⁻¹ := inv_anti₀ hbpos hle
    have hinvpos : (0 : ℝ) ≤ (y + (k + 1 : ℕ))⁻¹ := by positivity
    have hpow : (y + (k + 1 : ℕ))⁻¹ ^ 3 ≤ (x₀ / 2 + (k + 1 : ℕ))⁻¹ ^ 3 :=
      pow_le_pow_left₀ hinvpos hinv 3
    have hnn : (0 : ℝ) ≤ (y + (k + 1 : ℕ))⁻¹ ^ 3 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonpos (by nlinarith [hnn]), neg_mul]
    linarith [hpow]

/-! ## §4 — CLOSED FORM: term-by-term differentiation of the positive tail tsum

**Closed form for `deriv tailSum` on `(0,∞)` (sub-fact (i), positive half).**
For `x > 0`, `HasDerivAt tailSum (∑_{k≥0} −2 (x+(k+1))⁻³) x`, i.e. the positive tail
tsum may be differentiated term by term, with the derivative series summable.  This
is the cleanly tractable half of sub-fact (i): the positive tail `∑(x+(k+1))⁻²` has
*no poles* on `(0,∞)`, so the local-uniform bound trick on `ball x₀ (x₀/2) ⊆ (0,∞)`
(rather than the integer-complement) closes it directly via Mathlib's
`hasDerivAt_tsum_of_isPreconnected`. -/

set_option maxHeartbeats 1000000 in
theorem hasDerivAt_posTail {x : ℝ} (hx : 0 < x) :
    HasDerivAt tailSum (∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) x := by
  obtain ⟨hUsum, hUbound⟩ := posTail_localUnifBound hx
  have hhalf : 0 < x / 2 := by positivity
  set t : Set ℝ := Metric.ball x (x / 2) with ht
  have htopen : IsOpen t := Metric.isOpen_ball
  have htconn : IsPreconnected t := (convex_ball x (x / 2)).isPreconnected
  have hxmem : x ∈ t := Metric.mem_ball_self hhalf
  -- per-term HasDerivAt on t (each y ∈ ball ⊆ (0,∞), so y > 0)
  have hg : ∀ (k : ℕ) (y : ℝ), y ∈ t →
      HasDerivAt (fun z : ℝ => (z + (k + 1 : ℕ))⁻¹ ^ 2)
        (-2 * (y + (k + 1 : ℕ))⁻¹ ^ 3) y := by
    intro k y hy
    rw [ht, Metric.mem_ball, Real.dist_eq] at hy
    have hypos : 0 < y := by rcases abs_lt.mp hy with ⟨h1, _⟩; linarith
    exact hasDerivAt_posTail_term k hypos
  -- convergence at the base point x
  have hg0 : Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 2) := tailSum_summable hx
  have := hasDerivAt_tsum_of_isPreconnected
    (u := fun k : ℕ => 2 * (x / 2 + (k + 1 : ℕ))⁻¹ ^ 3)
    (g := fun (k : ℕ) (z : ℝ) => (z + (k + 1 : ℕ))⁻¹ ^ 2)
    (g' := fun (k : ℕ) (y : ℝ) => -2 * (y + (k + 1 : ℕ))⁻¹ ^ 3)
    hUsum htopen htconn hg hUbound hxmem hg0 hxmem
  -- this : HasDerivAt (fun z => ∑' k, (z+(k+1))⁻²) (∑' k, −2(x+(k+1))⁻³) x
  -- tailSum is exactly that tsum
  have hfun : tailSum = fun z : ℝ => ∑' k : ℕ, (z + (k + 1 : ℕ))⁻¹ ^ 2 := by
    funext z; rfl
  rw [hfun]
  exact this

/-! ## §5 — The single named residual (NOT an axiom) and the closed-form assembly -/

/-- **The remaining content of the D-1 wall, bundled as ONE named `Prop` (never an
axiom).**  For `x ∉ ℤ` (here phrased as `sin πx ≠ 0`), the full interpolant
derivative has the Vaaler closed form `H′(x) = 2 J(x)`.  Discharging this requires:

* the *negative* bracket tsum `∑(x−(k+1))⁻²` differentiated term by term — unlike the
  positive tail (proven above by `hasDerivAt_posTail`), this series has poles at every
  positive integer, so the `ball ⊆ (0,∞)` envelope must be replaced by a
  `ball ⊆ ℝ∖ℤ` envelope (the same machinery as `VaalerSumInvSqProof.S_differentiableAt`,
  but for the *cube* derivative series and over ℝ);
* the product/chain rule through the `(sin πx/π)²` prefactor of `interpH`;
* the identification of the resulting closed form with `2·vaalerJ` — Vaaler Theorem 6,
  eqs (2.27)–(2.32), the J-Fourier-transform computation. -/
def DerivInterpHClosedForm : Prop :=
  ∀ x : ℝ, Real.sin (π * x) ≠ 0 →
    HasDerivAt interpH
      (2 * (MathExtras.NumberTheory.Analysis.VaalerCor7RouteB.vaalerJ x).re) x

/-- **Bookkeeping: the positive-tail derivative is a genuine summand of the wall.**
`interpBracket` is `(negTail) − tailSum + 2·x⁻¹`; the `−tailSum` part already has a
closed-form derivative (`−1` times `hasDerivAt_posTail`), and the `2·x⁻¹` part has the
elementary derivative `−2·x⁻²`.  This records the two CHEAP, fully-proven summands of
`deriv interpBracket`, isolating the remaining hard summand (the negative-tail tsum
`negTail x = ∑(x−(k+1))⁻²`, which has poles in `(0,∞)`). -/
theorem hasDerivAt_bracket_easy_parts {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => -tailSum z + 2 * z⁻¹)
      (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) + 2 * (-(x⁻¹ ^ 2))) x := by
  have h1 : HasDerivAt (fun z : ℝ => -tailSum z)
      (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3)) x := (hasDerivAt_posTail hx).neg
  have hxne : x ≠ 0 := hx.ne'
  have h2 : HasDerivAt (fun z : ℝ => 2 * z⁻¹) (2 * (-(x⁻¹ ^ 2))) x := by
    have hinv : HasDerivAt (fun z : ℝ => z⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hxne
    refine (hinv.const_mul (2 : ℝ)).congr_deriv ?_
    rw [inv_pow]
  exact h1.add h2

#print axioms hasDerivAt_invSq_shift
#print axioms hasDerivAt_posTail_term
#print axioms tailDerivSummable_pos
#print axioms posTail_localUnifBound
#print axioms hasDerivAt_posTail
#print axioms hasDerivAt_bracket_easy_parts

end MathExtras.NumberTheory.Analysis.VaalerDerivInterpHProbe
