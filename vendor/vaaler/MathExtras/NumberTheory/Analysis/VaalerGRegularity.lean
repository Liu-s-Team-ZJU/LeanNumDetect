/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch

/-!
# Vaaler Theorem 6: regularity of `G = ½H′` (continuity off ℤ, integrability reduction)
  and the two-IBP structure of `vaalerJ`

This NEW leaf attacks the *tractable* minor residuals about the explicit half-derivative
`G = ½H′` (`VaalerHPrimeEqTwoJ.G`, complexified `GC = (G : ℂ)`) that the committed
`VaalerGCFourierMatch.gcFourierMatch_of` reduces the minor wall to, namely

* `GContinuous := Continuous GC`,
* `GIntegrable := Integrable GC`,

together with the `vaalerJ`-side two-IBP decay `VaalerJDecayBound.VaalerJTwoIBPDecay`.

## What is PROVEN here (sorry/axiom-free, non-vacuous)

The series occurring in `G` are the cube-tail tsums `∑ −2(x∓(k+1))⁻³` (the bracket
derivative) and the `^2` tsums of `interpBracket`.  Off ℤ these are *continuous* (no
poles), provable via Mathlib's `continuousOn_tsum` on the `infDist`-ball `⊆ ℝ∖ℤ` of the
committed `VaalerDerivInterpHNegTail.negTail_localUnifBound`-style envelopes.  Concretely:

* `tsumInvPow_neg_continuousAt` / `tsumInvPow_pos_continuousAt` — **PROVEN** continuity at
  every `x₀ ∉ ℤ` of the negative/positive shift series `x ↦ ∑'_k (x ∓ (k+1))⁻¹ ^ p`
  (`p ≥ 2`), via `continuousOn_tsum` with a summable `infDist`-ball sup-envelope.
* `interpBracket_continuousAt` — **PROVEN** `ContinuousAt interpBracket x₀` for `x₀ ∉ ℤ`.
* `G_continuousAt_of_notMem` / `gC_continuousAt_of_notMem` — **PROVEN** `ContinuousAt GC x₀`
  for every `x₀ ∉ ℤ` (assembling the trig factors, `interpBracket`, the two cube tsums
  and the `x⁻²` term).  This is the entire off-ℤ continuity of `G`.
* `gIntegrable_of_continuous_of_decay` — **PROVEN** `GContinuous → GDecayBound →
  GIntegrable` (mirror of `VaalerJIntegrable.vaalerJ_integrable_of_decay`:
  `Integrable.mono'` against `integrable_inv_one_add_sq`, measurability from continuity).
* `gContinuous_of_offInt_of_atInt` — **PROVEN** assembly of `GContinuous` from the proven
  off-ℤ continuity and the single named integer residual `GContinuousAtIntegers`.

## The genuinely-hard sub-pieces, isolated as named `Prop`s (NEVER axioms)

* `GContinuousAtIntegers : ∀ n : ℤ, ContinuousAt GC n` — continuity of `G` *at the
  integers*.  Here both singular pieces `(sin πx/π)(cos πx)·(x−n)⁻²` and
  `(sin πx/π)²·(x−n)⁻³` blow up like `(x−n)⁻¹` individually; they *cancel* to leave
  `G → 0` (band-limited `Re J`).  This cancellation is the same analytic depth as the FT
  heart `GCFTeqJ`; isolated as ONE precise named `Prop`, a TRUE statement, NOT an axiom.
* `GDecayBound : ∃ C, ∀ x, ‖GC x‖ ≤ C·(1+x²)⁻¹` — the `O((1+x²)⁻¹)` decay of `½H′`
  (Vaaler eq. (2.32), `½H′ = J` band-limited).  A TRUE statement; NOT an axiom.
* The `vaalerJ` two-IBP decay `VaalerJTwoIBPDecay` is the `vaalerJ`-side residual; here we
  record the cleanly-provable structural facts feeding its two integrations by parts:
  `vaalerJ` is the inverse FT of the compactly-supported `Ĵ` with `Ĵ(±1)=0`
  (`vaalerJ_norm_le_jhatL1` is the unconditional small-`z` half, already committed), and
  `decayBound_of_const_and_quadratic` (committed) assembles the `(1+z²)⁻¹` envelope.  The
  large-`z` gain itself stays the named `Prop` `VaalerJTwoIBPDecay`.

## How this shrinks the minor residual set

`gcFourierMatch_of` consumes `{GContinuous, GIntegrable, GCFTeqJ, VaalerJhatContCornerOne,
VaalerJTwoIBPDecay}`.  This file reduces:

* `GContinuous` ⟸ `GContinuousAtIntegers` (off-ℤ is now PROVEN);
* `GIntegrable` ⟸ `GContinuous ∧ GDecayBound` (PROVEN reduction);

so the *minor* residual set is shrunk to
`{GContinuousAtIntegers, GDecayBound, GCFTeqJ, VaalerJhatContCornerOne, VaalerJTwoIBPDecay}`
— two new precise `G`-side analytic facts replacing the two bundled `Continuous/Integrable`
residuals, with the entire off-ℤ continuity discharged on Mathlib.

## Hard constraints honoured

NEW leaf only; nothing existing/committed edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.  Build green;
`#print axioms` of each result is `[propext, Classical.choice, Quot.sound]`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.27)–(2.32), p. 192.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology Metric
open scoped BigOperators FourierTransform RealInnerProductSpace

namespace MathExtras.NumberTheory.Analysis.VaalerGRegularity

open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail
open MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ
open MathExtras.NumberTheory.Analysis.VaalerCor7RouteB
open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerJDecayBound
open MathExtras.NumberTheory.Analysis.VaalerJIntegrable
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch

/-! ## §1 — Summability of the positive-shift power tails (all `x`, from the neg lemmas) -/

/-- For every `x`, `∑'_k (x + (k+1))⁻¹ ^ 2` is summable (substitute `x ↦ −x` in the
committed `summable_invSq_shift_neg`). -/
theorem summable_invSq_shift_pos (x : ℝ) :
    Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 2) := by
  have h := summable_invSq_shift_neg (-x)
  refine h.congr ?_
  intro k
  rw [show (-x - (k + 1 : ℕ)) = -(x + (k + 1 : ℕ)) by push_cast; ring, inv_neg, neg_pow]
  simp

/-- For every `x`, `∑'_k |x + (k+1)|⁻¹ ^ 3` is summable (substitute `x ↦ −x` in the
committed `summable_invCube_shift_neg`). -/
theorem summable_invCube_shift_pos (x : ℝ) :
    Summable (fun k : ℕ => |x + (k + 1 : ℕ)|⁻¹ ^ 3) := by
  have h := summable_invCube_shift_neg (-x)
  refine h.congr ?_
  intro k
  rw [show (-x - (k + 1 : ℕ)) = -(x + (k + 1 : ℕ)) by push_cast; ring, abs_neg]

/-! ## §2 — The `infDist`-ball uniform sup bound for the power tails (continuity input) -/

/-- For `x₀ ∉ ℤ`, on the ball `ball x₀ r` (`r = ½ infDist x₀ ℤ`) the negative-shift term
`(y − (k+1))⁻¹ ^ p` is dominated by the summable envelope `2^p · |x₀ − (k+1)|⁻¹ ^ p`, and
the ball avoids ℤ.  This is the `continuousOn_tsum` sup-input (the continuity analogue of
`negTail_localUnifBound`), valid for any power `p`. -/
theorem negShift_pow_localUnifBound {x₀ : ℝ} (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ))
    (p : ℕ) (hp : 2 ≤ p) :
    ∃ r : ℝ, 0 < r ∧ (Metric.ball x₀ r ⊆ (Set.range ((↑) : ℤ → ℝ))ᶜ) ∧
      Summable (fun k : ℕ => (2 : ℝ) ^ p * |x₀ - (k + 1 : ℕ)|⁻¹ ^ p) ∧
      (∀ (k : ℕ) (y : ℝ), y ∈ Metric.ball x₀ r →
        |y - (k + 1 : ℕ)|⁻¹ ^ p ≤ (2 : ℝ) ^ p * |x₀ - (k + 1 : ℕ)|⁻¹ ^ p) := by
  classical
  set s : Set ℝ := Set.range ((↑) : ℤ → ℝ) with hs
  have hsclosed : IsClosed s := Real.isClosed_range_intCast
  have hsne : s.Nonempty := ⟨(0 : ℝ), ⟨0, by simp⟩⟩
  set δ : ℝ := Metric.infDist x₀ s with hδ
  have hδpos : 0 < δ := by
    rw [hδ, ← hsclosed.notMem_iff_infDist_pos hsne]; exact hx₀
  set r : ℝ := δ / 2 with hr
  have hrpos : 0 < r := by positivity
  have hlb₀ : ∀ k : ℕ, δ ≤ |x₀ - (k + 1 : ℕ)| := by
    intro k
    have hmem : ((k + 1 : ℕ) : ℝ) ∈ s := ⟨(k + 1 : ℕ), by push_cast; ring⟩
    have := Metric.infDist_le_dist_of_mem (x := x₀) hmem
    rwa [Real.dist_eq] at this
  refine ⟨r, hrpos, ?_, ?_, ?_⟩
  · intro z hz
    rw [Metric.mem_ball] at hz
    intro hzmem
    obtain ⟨m, hm⟩ := hzmem
    have : δ ≤ dist x₀ z := by rw [hδ]; exact Metric.infDist_le_dist_of_mem ⟨m, hm⟩
    rw [dist_comm] at this; rw [hr] at hz; linarith
  · -- envelope summable: comparison with the square tail using 2 ≤ p and that the base
    -- |x₀−(k+1)| → ∞, so eventually |·|⁻¹ ≤ 1, hence |·|⁻¹^p ≤ |·|⁻¹^2.
    have hsq : Summable (fun k : ℕ => |x₀ - (k + 1 : ℕ)|⁻¹ ^ 2) := by
      refine (summable_invSq_shift_neg x₀).congr ?_
      intro k; rw [← abs_inv, sq_abs]
    have htend : Tendsto (fun k : ℕ => |x₀ - (k + 1 : ℕ)|⁻¹) atTop (𝓝 0) := by
      have hbase : Tendsto (fun k : ℕ => |x₀ - (k + 1 : ℕ)|) atTop atTop := by
        have hlin : Tendsto (fun k : ℕ => ((k : ℝ) + 1) - x₀) atTop atTop := by
          have hc : Tendsto (fun k : ℕ => (k : ℝ) + (1 - x₀)) atTop atTop :=
            Filter.tendsto_atTop_add_const_right atTop (1 - x₀)
              (tendsto_natCast_atTop_atTop (R := ℝ))
          refine hc.congr ?_
          intro k; ring
        refine (tendsto_abs_atTop_atTop.comp hlin).congr ?_
        intro k
        rw [Function.comp_apply]
        rw [show ((k:ℝ) + 1) - x₀ = -(x₀ - ((k + 1 : ℕ) : ℝ)) by push_cast; ring, abs_neg]
      exact (tendsto_inv_atTop_zero).comp hbase
    have hev : ∀ᶠ k in atTop, |x₀ - (k + 1 : ℕ)|⁻¹ ^ p ≤ |x₀ - (k + 1 : ℕ)|⁻¹ ^ 2 := by
      have h1 : ∀ᶠ k in atTop, |x₀ - (k + 1 : ℕ)|⁻¹ ≤ 1 := by
        have := htend.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
        filter_upwards [this] with k hk; exact hk
      filter_upwards [h1] with k hk
      have hnn : (0:ℝ) ≤ |x₀ - (k + 1 : ℕ)|⁻¹ := by positivity
      exact pow_le_pow_of_le_one hnn hk hp
    have hsummp : Summable (fun k : ℕ => |x₀ - (k + 1 : ℕ)|⁻¹ ^ p) := by
      refine summable_of_isBigO_nat hsq ?_
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [hev] with k hk
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ |x₀ - (k + 1 : ℕ)|⁻¹ ^ p),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ |x₀ - (k + 1 : ℕ)|⁻¹ ^ 2)]
      exact hk
    exact hsummp.mul_left _
  · -- uniform sup bound on the ball (mirror of negTail_localUnifBound, for power p)
    intro k y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
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
    have hinv : |y - (k + 1 : ℕ)|⁻¹ ≤ 2 * |x₀ - (k + 1 : ℕ)|⁻¹ := by
      have hhalfpos : (0 : ℝ) < |x₀ - (k + 1 : ℕ)| / 2 := by positivity
      have := inv_anti₀ hhalfpos hge
      calc |y - (k + 1 : ℕ)|⁻¹ ≤ (|x₀ - (k + 1 : ℕ)| / 2)⁻¹ := this
        _ = 2 * |x₀ - (k + 1 : ℕ)|⁻¹ := by rw [inv_div]; ring
    have hpow : |y - (k + 1 : ℕ)|⁻¹ ^ p ≤ (2 * |x₀ - (k + 1 : ℕ)|⁻¹) ^ p :=
      pow_le_pow_left₀ (by positivity) hinv p
    rw [mul_pow] at hpow
    exact hpow

/-! ## §3 — Continuity off ℤ of the negative/positive shift power tails -/

/-- **PROVEN.**  For `x₀ ∉ ℤ`, the negative-shift power tail
`x ↦ ∑'_k (x − (k+1))⁻¹ ^ p` is continuous at `x₀`.  (`continuousOn_tsum` on the
`infDist`-ball `⊆ ℝ∖ℤ`, with the summable sup-envelope of §2; the per-term `(·−(k+1))⁻¹^p`
is continuous on the ball since the ball avoids the poles `{k+1}`.) -/
theorem tsumInvPow_neg_continuousAt {x₀ : ℝ} (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ))
    (p : ℕ) (hp : 2 ≤ p) :
    ContinuousAt (fun x : ℝ => ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ p) x₀ := by
  obtain ⟨r, hrpos, hball_sub, hUsum, hUbound⟩ := negShift_pow_localUnifBound hx₀ p hp
  set t : Set ℝ := Metric.ball x₀ r with ht
  -- each term is continuous on the ball (denominator nonzero there)
  have hcont : ∀ k : ℕ, ContinuousOn (fun x : ℝ => (x - (k + 1 : ℕ))⁻¹ ^ p) t := by
    intro k
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀
    · fun_prop
    · intro y hy
      have hyc : y ∈ (Set.range ((↑) : ℤ → ℝ))ᶜ := hball_sub hy
      intro h
      apply hyc
      refine ⟨(k + 1 : ℕ), ?_⟩
      push_cast; push_cast at h; linarith
  -- sup bound on the ball
  have hsup : ∀ (k : ℕ) (x : ℝ), x ∈ t →
      ‖(x - (k + 1 : ℕ))⁻¹ ^ p‖ ≤ (2 : ℝ) ^ p * |x₀ - (k + 1 : ℕ)|⁻¹ ^ p := by
    intro k x hx
    have hb := hUbound k x hx
    rw [Real.norm_eq_abs]
    calc |(x - (k + 1 : ℕ))⁻¹ ^ p| = |x - (k + 1 : ℕ)|⁻¹ ^ p := by
            rw [← abs_inv, ← abs_pow]
      _ ≤ (2 : ℝ) ^ p * |x₀ - (k + 1 : ℕ)|⁻¹ ^ p := hb
  have hcontOn : ContinuousOn (fun x : ℝ => ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ p) t :=
    continuousOn_tsum hcont hUsum hsup
  exact hcontOn.continuousAt (Metric.ball_mem_nhds x₀ hrpos)

/-- **PROVEN.**  For `x₀ ∉ ℤ`, the positive-shift power tail
`x ↦ ∑'_k (x + (k+1))⁻¹ ^ p` is continuous at `x₀`.  (Reduce to
`tsumInvPow_neg_continuousAt` at `−x₀`: `(x+(k+1)) = −((−x)−(k+1))`, so the positive-shift
series at `x` equals the negative-shift series at `−x`, and `−x₀ ∉ ℤ` since `x₀ ∉ ℤ`.) -/
theorem tsumInvPow_pos_continuousAt {x₀ : ℝ} (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ))
    (p : ℕ) (hp : 2 ≤ p) :
    ContinuousAt (fun x : ℝ => ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ p) x₀ := by
  have hnegmem : (-x₀) ∉ Set.range ((↑) : ℤ → ℝ) := by
    intro ⟨m, hm⟩; apply hx₀; exact ⟨-m, by push_cast; linarith⟩
  have hbase := tsumInvPow_neg_continuousAt hnegmem p hp
  -- (fun x => ∑ (x+(k+1))⁻¹^p) = (fun x => ∑ ((-x)-(k+1))⁻¹^p ) up to sign² (p even/odd)
  -- Use composition with x ↦ -x.  The tsum at -x of neg-shift equals tsum at x of pos-shift
  -- up to (-1)^p; handle by congruence of the function.
  have heq : (fun x : ℝ => ∑' k : ℕ, ((-x) - (k + 1 : ℕ))⁻¹ ^ p)
      = (fun x : ℝ => (-1 : ℝ) ^ p * ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ p) := by
    funext x
    rw [← tsum_mul_left]
    refine tsum_congr ?_
    intro k
    have hstep : ((-x) - (k + 1 : ℕ))⁻¹ ^ p = (-1 : ℝ) ^ p * (x + (k + 1 : ℕ))⁻¹ ^ p := by
      rw [show ((-x) - (k + 1 : ℕ)) = -(x + (k + 1 : ℕ)) by push_cast; ring, inv_neg, neg_pow]
    exact hstep
  have hcomp : ContinuousAt (fun x : ℝ => ∑' k : ℕ, ((-x) - (k + 1 : ℕ))⁻¹ ^ p) x₀ := by
    have hneg : ContinuousAt (fun x : ℝ => -x) x₀ := continuous_neg.continuousAt
    exact hbase.comp hneg
  rw [heq] at hcomp
  have : ContinuousAt (fun x : ℝ => (-1 : ℝ) ^ p * ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ p) x₀ :=
    hcomp
  -- divide out the nonzero constant (-1)^p
  have hc : ((-1 : ℝ) ^ p) ≠ 0 := by positivity
  have := this.div_const ((-1 : ℝ) ^ p)
  refine this.congr ?_
  filter_upwards with x
  field_simp

/-! ## §4 — Continuity of `interpBracket` and of `G` off ℤ -/

/-- **PROVEN.**  `interpBracket` is continuous at every `x₀ ∉ ℤ`.  `interpBracket x =
(∑(x−(k+1))⁻²) − (∑(x+(k+1))⁻²) + 2x⁻¹`; the two `^2` tails are continuous off ℤ (§3,
`p = 2`) and `2x⁻¹` is continuous at `x₀ ≠ 0`. -/
theorem interpBracket_continuousAt {x₀ : ℝ} (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ)) :
    ContinuousAt interpBracket x₀ := by
  have hx0ne : x₀ ≠ 0 := by intro h; apply hx₀; exact ⟨0, by simp [h]⟩
  have h1 := tsumInvPow_neg_continuousAt hx₀ 2 (by norm_num)
  have h2 := tsumInvPow_pos_continuousAt hx₀ 2 (by norm_num)
  have h3 : ContinuousAt (fun x : ℝ => 2 * x⁻¹) x₀ := by
    apply ContinuousAt.const_mul
    exact (continuousAt_inv₀ hx0ne)
  have hsum : ContinuousAt
      (fun x : ℝ => (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2)
        - (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2) + 2 * x⁻¹) x₀ := by
    exact (h1.sub h2).add h3
  refine hsum.congr ?_
  filter_upwards with x
  unfold interpBracket tailSum
  rfl

/-- **PROVEN — the entire off-ℤ continuity of `G` (and `GC`).**  For `x₀ ∉ ℤ`,
`ContinuousAt GC x₀`.  `G` assembles: trig factors (`Real.continuous_sin/cos`, continuous
everywhere), `interpBracket` (continuous off ℤ, §4), the two cube tails `∑ −2(x∓(k+1))⁻²·
(x∓(k+1))⁻¹ = ∑ −2(x∓(k+1))⁻³` (continuous off ℤ, §3 with `p = 3` after re-shaping), and
`2·(−x⁻²)` (continuous at `x₀ ≠ 0`).  `GC = (G : ℂ)` then continuous by `Complex.ofReal`. -/
theorem G_continuousAt_of_notMem {x₀ : ℝ} (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ)) :
    ContinuousAt G x₀ := by
  have hx0ne : x₀ ≠ 0 := by intro h; apply hx₀; exact ⟨0, by simp [h]⟩
  -- trig factors
  have hsin : ContinuousAt (fun x : ℝ => Real.sin (π * x) / π) x₀ := by
    apply ContinuousAt.div_const
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
  have hcos : ContinuousAt (fun x : ℝ => Real.cos (π * x) * π / π) x₀ := by
    apply ContinuousAt.div_const
    apply ContinuousAt.mul_const
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousAt
  -- interpBracket
  have hbr := interpBracket_continuousAt hx₀
  -- first summand of G
  have hfirst : ContinuousAt
      (fun x : ℝ => (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * interpBracket x) x₀ :=
    (hsin.mul hcos).mul hbr
  -- cube tails, re-shaped to (·)⁻¹^3
  have hcubeNeg : ContinuousAt
      (fun x : ℝ => ∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹) x₀ := by
    have h := tsumInvPow_neg_continuousAt hx₀ 3 (by norm_num)
    -- ∑ (x−(k+1))⁻³ ; reshape: −2·(x−(k+1))⁻²·(x−(k+1))⁻¹ = −2·(x−(k+1))⁻³
    have heq : (fun x : ℝ => ∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹)
        = (fun x : ℝ => (-2 : ℝ) * ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 3) := by
      funext x
      rw [← tsum_mul_left]
      refine tsum_congr ?_
      intro k; ring
    rw [heq]
    exact h.const_mul _
  have hcubePos : ContinuousAt
      (fun x : ℝ => ∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹) x₀ := by
    have h := tsumInvPow_pos_continuousAt hx₀ 3 (by norm_num)
    have heq : (fun x : ℝ => ∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹)
        = (fun x : ℝ => (-2 : ℝ) * ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3) := by
      funext x
      rw [← tsum_mul_left]
      refine tsum_congr ?_
      intro k; ring
    rw [heq]
    exact h.const_mul _
  -- the x⁻² term
  have hxsq : ContinuousAt (fun x : ℝ => 2 * (-(x⁻¹ ^ 2))) x₀ := by
    apply ContinuousAt.const_mul
    apply ContinuousAt.neg
    apply ContinuousAt.pow
    exact continuousAt_inv₀ hx0ne
  -- second summand of G : (1/2)·(sin/π)²·( cubeNeg + (−cubePos + 2(−x⁻²)) )
  have hsinsq : ContinuousAt (fun x : ℝ => (Real.sin (π * x) / π) ^ 2) x₀ := hsin.pow 2
  have hinner : ContinuousAt
      (fun x : ℝ => (∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹)
        + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹)
          + 2 * (-(x⁻¹ ^ 2)))) x₀ :=
    hcubeNeg.add (hcubePos.neg.add hxsq)
  have hsecond : ContinuousAt
      (fun x : ℝ => (1 / 2 : ℝ) * (Real.sin (π * x) / π) ^ 2 *
        ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹)
          + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹)
            + 2 * (-(x⁻¹ ^ 2))))) x₀ :=
    ((hsinsq.const_mul (1 / 2 : ℝ)).mul hinner)
  have htot : ContinuousAt
      (fun x : ℝ => ((Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * interpBracket x)
        + ((1 / 2 : ℝ) * (Real.sin (π * x) / π) ^ 2 *
          ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹)
            + (-(∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹)
              + 2 * (-(x⁻¹ ^ 2)))))) x₀ :=
    hfirst.add hsecond
  refine htot.congr ?_
  have hne : ∀ᶠ x : ℝ in nhds x₀, x ≠ 0 :=
    (continuous_id.continuousAt).eventually_ne hx0ne
  filter_upwards [hne] with x hx
  rw [G_eq_of_ne_zero hx]

/-- **PROVEN.**  `ContinuousAt GC x₀` for `x₀ ∉ ℤ`. -/
theorem gC_continuousAt_of_notMem {x₀ : ℝ} (hx₀ : x₀ ∉ Set.range ((↑) : ℤ → ℝ)) :
    ContinuousAt GC x₀ := by
  have := G_continuousAt_of_notMem hx₀
  have hofR : ContinuousAt (fun y : ℝ => (y : ℂ)) (G x₀) :=
    Complex.continuous_ofReal.continuousAt
  exact (hofR.comp this).congr (by filter_upwards with x; simp [Function.comp, GC_apply])

/-! ## §5 — The integer residual and the `GContinuous` assembly -/

/-- **Residual (continuity of `G` AT the integers).**  At each integer `n`, `G` is
continuous.  This is the genuine cancellation: the two singular pieces of `G`,
`(sin πx/π)(cos πx)·(x−n)⁻²` and `½(sin πx/π)²·(−2(x−n)⁻³)`, *individually* blow up like
`(x−n)⁻¹`, but their sum is bounded and `→ 0` (the band-limited `Re J` is continuous with
`Re J(n) = 0`).  Of the same analytic depth as the FT heart `GCFTeqJ`.  A TRUE statement
about the explicit `G`; NOT vacuous, NOT an `axiom`. -/
def GContinuousAtIntegers : Prop := ∀ n : ℤ, ContinuousAt GC (n : ℝ)

/-- **PROVEN — `GContinuous` from `GContinuousAtIntegers`.**  Off ℤ continuity is proven
(`gC_continuousAt_of_notMem`); at the integers it is the named residual.  Together they give
continuity at every point, i.e. `Continuous GC = GContinuous`. -/
theorem gContinuous_of_offInt_of_atInt (hInt : GContinuousAtIntegers) : GContinuous := by
  rw [GContinuous, continuous_iff_continuousAt]
  intro x₀
  by_cases hx : x₀ ∈ Set.range ((↑) : ℤ → ℝ)
  · obtain ⟨n, hn⟩ := hx
    rw [← hn]
    exact hInt n
  · exact gC_continuousAt_of_notMem hx

/-! ## §6 — `GIntegrable` from continuity + decay -/

/-- **Residual (`O((1+x²)⁻¹)` decay of `½H′`).**  Vaaler eq. (2.32): `½H′ = J` is
band-limited with `J(x) = O((1+|x|)⁻²)`, so `‖GC x‖ ≤ C·(1+x²)⁻¹`.  Mirrors the
`vaalerJ`-side `JDecayBound`.  A TRUE statement about the explicit `G`; NOT an `axiom`. -/
def GDecayBound : Prop := ∃ C : ℝ, ∀ x : ℝ, ‖GC x‖ ≤ C * (1 + x ^ 2)⁻¹

/-- **PROVEN.**  `GContinuous → GDecayBound → GIntegrable`.  `Integrable.mono'` against the
Mathlib-integrable majorant `C·(1+x²)⁻¹` (`integrable_inv_one_add_sq`), with
`AEStronglyMeasurable` supplied by continuity.  Mirror of
`VaalerJIntegrable.vaalerJ_integrable_of_decay`. -/
theorem gIntegrable_of_continuous_of_decay (hcont : GContinuous) (hdec : GDecayBound) :
    GIntegrable := by
  obtain ⟨C, hC⟩ := hdec
  have hmaj : Integrable (fun x : ℝ => C * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  have hmeas : AEStronglyMeasurable GC := hcont.aestronglyMeasurable
  refine hmaj.mono' hmeas ?_
  filter_upwards with x
  exact hC x

/-! ## §7 — The full minor-wall assembly from the shrunk residual set -/

/-- **PROVEN — `GCFourierMatch` from the SHRUNK residual set.**  Replaces the two bundled
`G`-side residuals `GContinuous`, `GIntegrable` of `gcFourierMatch_of` by the precise
`GContinuousAtIntegers` (off-ℤ continuity now proven) and `GDecayBound` (with continuity
giving measurability), keeping the FT heart `GCFTeqJ` and the two `vaalerJ`-side residuals.
The entire off-ℤ continuity and the integrability reduction are discharged here. -/
theorem gcFourierMatch_of_shrunk
    (hInt : GContinuousAtIntegers) (hDec : GDecayBound) (hGFT : GCFTeqJ)
    (h1 : MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.VaalerJhatContCornerOne)
    (h2 : MathExtras.NumberTheory.Analysis.VaalerJDecayBound.VaalerJTwoIBPDecay) :
    GCFourierMatch := by
  have hGcont : GContinuous := gContinuous_of_offInt_of_atInt hInt
  have hGint : GIntegrable := gIntegrable_of_continuous_of_decay hGcont hDec
  exact gcFourierMatch_of hGcont hGint hGFT h1 h2

/-- **PROVEN — the minor D-1 wall `GEqReJ` from the SHRUNK residual set.** -/
theorem gEqReJ_of_shrunk
    (hInt : GContinuousAtIntegers) (hDec : GDecayBound) (hGFT : GCFTeqJ)
    (h1 : MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.VaalerJhatContCornerOne)
    (h2 : MathExtras.NumberTheory.Analysis.VaalerJDecayBound.VaalerJTwoIBPDecay) :
    MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ.GEqReJ :=
  gEqReJ_of_match (gcFourierMatch_of_shrunk hInt hDec hGFT h1 h2)

#print axioms summable_invSq_shift_pos
#print axioms summable_invCube_shift_pos
#print axioms negShift_pow_localUnifBound
#print axioms tsumInvPow_neg_continuousAt
#print axioms tsumInvPow_pos_continuousAt
#print axioms interpBracket_continuousAt
#print axioms G_continuousAt_of_notMem
#print axioms gC_continuousAt_of_notMem
#print axioms gContinuous_of_offInt_of_atInt
#print axioms gIntegrable_of_continuous_of_decay
#print axioms gcFourierMatch_of_shrunk
#print axioms gEqReJ_of_shrunk

end MathExtras.NumberTheory.Analysis.VaalerGRegularity

end
