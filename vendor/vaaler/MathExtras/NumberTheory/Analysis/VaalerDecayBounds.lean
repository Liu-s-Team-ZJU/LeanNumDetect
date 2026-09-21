/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGRegularity

/-!
# Vaaler Theorem 6: the two minor DECAY residuals `GDecayBound` and `VaalerJTwoIBPDecay`

This NEW leaf attacks the two remaining *decay* residuals of the Vaaler minor wall:

* `VaalerGRegularity.GDecayBound : ∃ C, ∀ x, ‖GC x‖ ≤ C·(1+x²)⁻¹`  (`G = ½ H′`), and
* `VaalerJDecayBound.VaalerJTwoIBPDecay : ∃ C, ∀ z, 1 ≤ |z| → ‖vaalerJ z‖ ≤ C·(z²)⁻¹`.

Both are genuine `O(x⁻²)` *tail* bounds.  We carve each into

  (a) a small-argument / compact-region part, **PROVEN here on Mathlib**, and
  (b) a large-argument tail part — the genuine analytic cancellation (the `H′`-cancellation
      for `G`; the two-IBP `Ĵ′`-bounded-variation gain for `vaalerJ`) — isolated as ONE
      precise named `Prop` (NEVER an axiom).

## What is PROVEN here (sorry/axiom-free, non-vacuous)

### Pure real-analysis assembly (shared mechanism)

* `decayBound_of_compact_and_tail` — **PROVEN.**  For *any* `f : ℝ → ℂ` that is bounded on
  `[-R₀, R₀]` by `M` and satisfies a tail bound `‖f x‖ ≤ C·(x²)⁻¹` for `R₀ ≤ |x|`
  (`1 ≤ R₀`), one has `‖f x‖ ≤ (2·max (M·(1+R₀²)) C)·(1+x²)⁻¹` for *all* `x`.  This is the
  exact `min(1, x⁻²) ≍ (1+x²)⁻¹` packaging, with the constant part coming from a *compact
  sup* (not a unit-modulus integral as on the `J`-side), so it applies to `GC`.

* `continuous_bddOn_Icc` — **PROVEN.**  A continuous `f : ℝ → ℂ` is bounded on every
  `[-R, R]` (extreme value theorem `IsCompact.exists_isMaxOn` on the compact `Icc`,
  composed with the continuous norm).

### `G`-side (Residual 1)

* `gDecayBound_of_largeArg` — **PROVEN.**  `GContinuous → GLargeArgDecay → GDecayBound`.
  Continuity gives the compact bound `continuous_bddOn_Icc`; the large-argument tail is the
  named residual; `decayBound_of_compact_and_tail` assembles them.
* `gDecayBound_of_residuals` — **PROVEN.**  `GContinuousAtIntegers → GLargeArgDecay →
  GDecayBound`, threading `VaalerGRegularity.gContinuous_of_offInt_of_atInt` (off-ℤ
  continuity already proven there).  This is the full reduction of the minor `GDecayBound`
  residual to the two precise kernels `{GContinuousAtIntegers, GLargeArgDecay}`.
* `gIntegrable_of_residuals` — **PROVEN.**  `GContinuousAtIntegers → GLargeArgDecay →
  GIntegrable` (chaining into `VaalerGRegularity.gIntegrable_of_continuous_of_decay`).

### `J`-side (Residual 2)

* `jTwoIBPDecay_of_largeArgTail` — **PROVEN.**  The named tail `VaalerJLargeArgDecay`
  (a `(z²)⁻¹` bound on `1 ≤ |z|`, the two-IBP output) is *definitionally* the residual
  `VaalerJTwoIBPDecay`; recorded for symmetry with the `G`-side.
* `jDecayBound_of_largeArgTail` — **PROVEN.**  Composes with the committed
  `VaalerJDecayBound.jDecayBound_of_twoIBP` to land `JDecayBound` (hence `JIntegrable` via
  the committed `jIntegrable_of_twoIBP`).

## The genuinely-hard kernels, isolated as named `Prop`s (NEVER axioms)

* `GLargeArgDecay : ∃ R₀ C, 1 ≤ R₀ ∧ ∀ x, R₀ ≤ |x| → ‖GC x‖ ≤ C·(x²)⁻¹` — the
  large-argument `O(x⁻²)` decay of `½H′`.  This is the **content of the cancellation**:
  off the integers `G = (sin πx/π)(cos πx)·B(x) + ½(sin πx/π)²·(cube tails − 2x⁻²)`; the
  product `(sin/π)²·B` is `O(1)` (the squared-cosecant identity makes `B ∼ (π/sin)²`),
  while the cube tails contribute the `O(x⁻²)` gain after the leading `O(x⁻¹)` terms
  cancel.  A TRUE statement about the explicit `G`; NOT vacuous, NOT an `axiom`.  (Same
  analytic depth as the FT heart `GCFTeqJ`; numerically `|G x|·x² → 0`.)

* `VaalerJLargeArgDecay := VaalerJTwoIBPDecay` — the large-`z` `(z²)⁻¹` tail from the two
  integrations by parts on `∫_{-1}^1 Ĵ(τ) e(τz) dτ` (boundary terms vanish at `±1` since
  `Ĵ(±1)=0`; the corner jumps of `Ĵ′` at `{−1,0,1}` and the bounded `Ĵ″` on `(-1,0)∪(0,1)`
  give the gain).  Bounded-variation `Ĵ′` / distributional second IBP is the genuine gap
  (absent from Mathlib); kept as the committed named `Prop`, never an `axiom`.

## How this shrinks the minor residual set

`VaalerGRegularity.gcFourierMatch_of_shrunk` consumes
`{GContinuousAtIntegers, GDecayBound, GCFTeqJ, VaalerJhatContCornerOne, VaalerJTwoIBPDecay}`.
This file reduces `GDecayBound ⟸ GContinuousAtIntegers ∧ GLargeArgDecay`, so the minor set
becomes `{GContinuousAtIntegers, GLargeArgDecay, GCFTeqJ, VaalerJhatContCornerOne,
VaalerJTwoIBPDecay}` — the bundled `GDecayBound` is replaced by the sharper, large-argument
`GLargeArgDecay`, with the entire compact region discharged on Mathlib's extreme value
theorem.  The `J`-side IBP tail is unchanged (already a single named `Prop`).

## Hard constraints honoured

NEW leaf only; nothing existing/committed is edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.  Build green;
`#print axioms` of each result is `[propext, Classical.choice, Quot.sound]`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.27)–(2.32), p. 192.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology Metric
open scoped BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerDecayBounds

open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ
open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerGRegularity
open MathExtras.NumberTheory.Analysis.VaalerCor7RouteB
open MathExtras.NumberTheory.Analysis.VaalerJDecayBound
open MathExtras.NumberTheory.Analysis.VaalerJIntegrable

/-! ## §1 — Continuous ⇒ bounded on every `[-R, R]` (extreme value theorem) -/

/-- **PROVEN.**  A continuous `f : ℝ → ℂ` is bounded on `[-R, R]` (for `0 ≤ R`): there is
`M ≥ 0` with `‖f x‖ ≤ M` for every `x ∈ [-R, R]`.  The compact `Icc` (nonempty since
`0 ≤ R`) and the continuous norm give a maximiser by `IsCompact.exists_isMaxOn`. -/
theorem continuous_bddOn_Icc {f : ℝ → ℂ} (hf : Continuous f) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, x ∈ Set.Icc (-R) R → ‖f x‖ ≤ M := by
  have hcpt : IsCompact (Set.Icc (-R) R) := isCompact_Icc
  have hne : (Set.Icc (-R) R).Nonempty := Set.nonempty_Icc.mpr (by linarith)
  have hcont : ContinuousOn (fun x : ℝ => ‖f x‖) (Set.Icc (-R) R) :=
    (continuous_norm.comp hf).continuousOn
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := hcpt.exists_isMaxOn hne hcont
  refine ⟨‖f x₀‖, norm_nonneg _, ?_⟩
  intro x hx
  exact hx₀max hx

/-! ## §2 — The shared real-analysis assembly: compact bound + tail ⇒ `(1+x²)⁻¹` -/

/-- **PROVEN (pure real analysis).**  From a uniform bound `M` on the compact `[-R₀, R₀]`
(`1 ≤ R₀`) and a quadratic tail bound `‖f x‖ ≤ C·(x²)⁻¹` for `R₀ ≤ |x|`, one obtains the
`(1+x²)⁻¹` envelope:  `‖f x‖ ≤ (2·max (M·(1+R₀²)) C)·(1+x²)⁻¹` for *all* `x`.

For `|x| ≤ R₀`: `(1+x²)⁻¹ ≥ (1+R₀²)⁻¹` (since `x² ≤ R₀²`), so `M ≤ M·(1+R₀²)·(1+x²)⁻¹`.
For `|x| ≥ R₀ ≥ 1`: `z² ≥ (1+z²)/2` (since `1 ≤ x²`), so `C·(x²)⁻¹ ≤ 2C·(1+x²)⁻¹`.
The shared constant `2·max (M·(1+R₀²)) C` dominates both branches. -/
theorem decayBound_of_compact_and_tail {f : ℝ → ℂ} {R₀ M C : ℝ}
    (hR₀ : 1 ≤ R₀) (hM : 0 ≤ M)
    (hcompact : ∀ x : ℝ, |x| ≤ R₀ → ‖f x‖ ≤ M)
    (htail : ∀ x : ℝ, R₀ ≤ |x| → ‖f x‖ ≤ C * (x ^ 2)⁻¹) :
    ∀ x : ℝ, ‖f x‖ ≤ (2 * max (M * (1 + R₀ ^ 2)) C) * (1 + x ^ 2)⁻¹ := by
  intro x
  have hden_pos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hR₀sq : (1 : ℝ) ≤ R₀ ^ 2 := by nlinarith [hR₀]
  set Kc : ℝ := max (M * (1 + R₀ ^ 2)) C with hKc
  have hMR₀_nonneg : 0 ≤ M * (1 + R₀ ^ 2) := by positivity
  have hmaxA : M * (1 + R₀ ^ 2) ≤ Kc := le_max_left _ _
  have hmaxC : C ≤ Kc := le_max_right _ _
  have hKc_nonneg : 0 ≤ Kc := le_trans hMR₀_nonneg hmaxA
  by_cases hx : |x| ≤ R₀
  · -- compact region
    have hx2 : x ^ 2 ≤ R₀ ^ 2 := by nlinarith [sq_abs x, abs_nonneg x, hx]
    -- (1+R₀²)⁻¹ ≤ (1+x²)⁻¹
    have hinvle : (1 + R₀ ^ 2)⁻¹ ≤ (1 + x ^ 2)⁻¹ :=
      inv_anti₀ hden_pos (by linarith)
    have hbig_pos : (0 : ℝ) < 1 + R₀ ^ 2 := by positivity
    calc ‖f x‖ ≤ M := hcompact x hx
      _ = M * (1 + R₀ ^ 2) * (1 + R₀ ^ 2)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hbig_pos), mul_one]
      _ ≤ Kc * (1 + x ^ 2)⁻¹ := by
            apply mul_le_mul hmaxA hinvle (by positivity) hKc_nonneg
      _ ≤ (2 * Kc) * (1 + x ^ 2)⁻¹ := by
            apply mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (by positivity))
  · -- tail region
    rw [not_le] at hx
    have hxge : R₀ ≤ |x| := le_of_lt hx
    have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x, hR₀]
    have hx2pos : (0 : ℝ) < x ^ 2 := by linarith
    have hkey : (x ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ hx2pos,
        show (2 : ℝ) * (1 + x ^ 2)⁻¹ * x ^ 2 = 2 * x ^ 2 * (1 + x ^ 2)⁻¹ by ring,
        le_mul_inv_iff₀ hden_pos]
      nlinarith [hx2]
    calc ‖f x‖ ≤ C * (x ^ 2)⁻¹ := htail x hxge
      _ ≤ Kc * (2 * (1 + x ^ 2)⁻¹) :=
            mul_le_mul hmaxC hkey (by positivity) hKc_nonneg
      _ = (2 * Kc) * (1 + x ^ 2)⁻¹ := by ring

/-! ## §3 — Residual 1 (`G`-side): the large-argument tail kernel and the assembly -/

/-- **Residual (the large-argument `O(x⁻²)` decay of `½H′ = G`).**  There is a threshold
`R₀ ≥ 1` and a constant `C` with `‖GC x‖ ≤ C·(x²)⁻¹` for all `R₀ ≤ |x|`.

This is the genuine analytic content of the decay of `G`: off the integers
`G x = (sin πx/π)(cos πx)·B(x) + ½(sin πx/π)²·(∑−2(x∓(k+1))⁻³ − 2x⁻²)`.  The product
`(sin πx/π)²·B(x)` stays `O(1)` because the squared-cosecant identity makes
`B(x) ∼ (π/sin πx)²`; the cube tails then contribute the `O(x⁻²)` gain after the leading
`O(x⁻¹)` terms cancel (this cancellation is the content — `H → ±1`, `H′ → 0` fast).  A TRUE
statement about the explicit `G`; NOT vacuous, NOT an `axiom`.  (Numerically `|G x|·x²` is
bounded and `→ 0`; same analytic depth as the FT heart `GCFTeqJ`.) -/
def GLargeArgDecay : Prop :=
  ∃ R₀ C : ℝ, 1 ≤ R₀ ∧ ∀ x : ℝ, R₀ ≤ |x| → ‖GC x‖ ≤ C * (x ^ 2)⁻¹

/-- **PROVEN.**  `GContinuous → GLargeArgDecay → GDecayBound`.  Continuity gives the
compact bound on `[-R₀, R₀]` (`continuous_bddOn_Icc`); the large-argument tail is the named
kernel; `decayBound_of_compact_and_tail` assembles them into the `(1+x²)⁻¹` envelope. -/
theorem gDecayBound_of_largeArg (hcont : GContinuous) (htail : GLargeArgDecay) :
    GDecayBound := by
  obtain ⟨R₀, C, hR₀, hC⟩ := htail
  -- compact bound on [-R₀, R₀]
  obtain ⟨M, hMnn, hM⟩ := continuous_bddOn_Icc hcont (by linarith : (0:ℝ) ≤ R₀)
  -- repackage the compact bound in terms of |x| ≤ R₀
  have hcompact : ∀ x : ℝ, |x| ≤ R₀ → ‖GC x‖ ≤ M := by
    intro x hx
    have hmem : x ∈ Set.Icc (-R₀) R₀ := by
      rw [Set.mem_Icc]
      constructor
      · have := abs_le.mp hx; linarith [this.1]
      · exact (abs_le.mp hx).2
    exact hM x hmem
  exact ⟨2 * max (M * (1 + R₀ ^ 2)) C,
    decayBound_of_compact_and_tail hR₀ hMnn hcompact hC⟩

/-- **PROVEN — full reduction of the `GDecayBound` minor residual.**
`GContinuousAtIntegers → GLargeArgDecay → GDecayBound`.  The off-ℤ continuity of `G` is
already proven in `VaalerGRegularity`; combined with the integer-continuity residual it
gives `GContinuous` (`gContinuous_of_offInt_of_atInt`), and then `gDecayBound_of_largeArg`
delivers the envelope.  Thus the bundled `GDecayBound` residual is replaced by the sharper
large-argument kernel `GLargeArgDecay` (the genuine cancellation). -/
theorem gDecayBound_of_residuals
    (hInt : GContinuousAtIntegers) (htail : GLargeArgDecay) : GDecayBound :=
  gDecayBound_of_largeArg (gContinuous_of_offInt_of_atInt hInt) htail

/-- **PROVEN.**  `GContinuousAtIntegers → GLargeArgDecay → GIntegrable`.  Chains the decay
reduction into the committed `VaalerGRegularity.gIntegrable_of_continuous_of_decay`
(`Integrable.mono'` against the Mathlib-integrable majorant `C·(1+x²)⁻¹`). -/
theorem gIntegrable_of_residuals
    (hInt : GContinuousAtIntegers) (htail : GLargeArgDecay) : GIntegrable := by
  have hcont : GContinuous := gContinuous_of_offInt_of_atInt hInt
  exact gIntegrable_of_continuous_of_decay hcont (gDecayBound_of_residuals hInt htail)

/-- **PROVEN — the SHRUNK minor `GCFourierMatch` from the decay-refined residual set.**
Replaces the bundled `GDecayBound` of `VaalerGRegularity.gcFourierMatch_of_shrunk` by the
sharper large-argument kernel `GLargeArgDecay`, keeping the proven off-ℤ continuity and the
integrability reduction.  The minor residual set is now
`{GContinuousAtIntegers, GLargeArgDecay, GCFTeqJ, VaalerJhatContCornerOne,
VaalerJTwoIBPDecay}`. -/
theorem gcFourierMatch_of_decayResiduals
    (hInt : GContinuousAtIntegers) (hTail : GLargeArgDecay) (hGFT : GCFTeqJ)
    (h1 : MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.VaalerJhatContCornerOne)
    (h2 : MathExtras.NumberTheory.Analysis.VaalerJDecayBound.VaalerJTwoIBPDecay) :
    GCFourierMatch :=
  gcFourierMatch_of_shrunk hInt (gDecayBound_of_residuals hInt hTail) hGFT h1 h2

/-- **PROVEN — the minor D-1 wall `GEqReJ` from the decay-refined residual set.** -/
theorem gEqReJ_of_decayResiduals
    (hInt : GContinuousAtIntegers) (hTail : GLargeArgDecay) (hGFT : GCFTeqJ)
    (h1 : MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.VaalerJhatContCornerOne)
    (h2 : MathExtras.NumberTheory.Analysis.VaalerJDecayBound.VaalerJTwoIBPDecay) :
    MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ.GEqReJ :=
  gEqReJ_of_shrunk hInt (gDecayBound_of_residuals hInt hTail) hGFT h1 h2

/-! ## §4 — Residual 2 (`J`-side): the two-IBP large-argument tail and the assembly -/

/-- **Residual (the large-`z` two-IBP `(z²)⁻¹` tail of `vaalerJ`).**  This is *exactly*
the committed `VaalerJDecayBound.VaalerJTwoIBPDecay`: for `1 ≤ |z|`,
`‖vaalerJ z‖ ≤ C·(z²)⁻¹`.  We give it a local name symmetric to `GLargeArgDecay` so the two
minor decay residuals read uniformly.  The content is Vaaler's *two* integrations by parts
on `∫_{-1}^1 Ĵ(τ) e(τz) dτ`: boundary terms vanish at `±1` (`Ĵ(±1)=0`), the corner jumps of
`Ĵ′` at `{−1,0,1}` and the bounded `Ĵ″` on `(-1,0)∪(0,1)` give the `(z²)⁻¹` gain.  A TRUE
statement about the explicit `vaalerJ`; NOT vacuous, NOT an `axiom`. -/
def VaalerJLargeArgDecay : Prop :=
  MathExtras.NumberTheory.Analysis.VaalerJDecayBound.VaalerJTwoIBPDecay

/-- **PROVEN (definitional).**  `VaalerJLargeArgDecay → VaalerJTwoIBPDecay`.  Recorded for
symmetry with the `G`-side; the small-`z` constant half is already PROVEN unconditionally
(`VaalerJDecayBound.vaalerJ_norm_le_jhatL1`). -/
theorem jTwoIBPDecay_of_largeArgTail (h : VaalerJLargeArgDecay) :
    MathExtras.NumberTheory.Analysis.VaalerJDecayBound.VaalerJTwoIBPDecay := h

/-- **PROVEN.**  `VaalerJLargeArgDecay → JDecayBound`.  Composes the named two-IBP tail with
the committed `VaalerJDecayBound.jDecayBound_of_twoIBP`, whose proven small-`z` half is the
unconditional unit-modulus bound `vaalerJ_norm_le_jhatL1`. -/
theorem jDecayBound_of_largeArgTail (h : VaalerJLargeArgDecay) :
    MathExtras.NumberTheory.Analysis.VaalerJIntegrable.JDecayBound :=
  jDecayBound_of_twoIBP (jTwoIBPDecay_of_largeArgTail h)

/-- **PROVEN.**  `VaalerJLargeArgDecay → JIntegrable`, the analytic transform-half of
Vaaler Theorem 6, via the committed `jIntegrable_of_twoIBP`. -/
theorem jIntegrable_of_largeArgTail (h : VaalerJLargeArgDecay) :
    MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.JIntegrable :=
  jIntegrable_of_twoIBP (jTwoIBPDecay_of_largeArgTail h)

/-! ## §5 — Both minor decay residuals in one statement -/

/-- **PROVEN — both minor decay residuals from their two large-argument kernels.**
From the `G`-side kernels `{GContinuousAtIntegers, GLargeArgDecay}` and the `J`-side kernel
`VaalerJLargeArgDecay`, both decay residuals `GDecayBound` and `JDecayBound` hold.  This is
the joint statement that the minor decay wall is reduced to the precise large-argument tails
(plus the proven off-ℤ continuity), with everything else (the compact regions, the
small-`z` constant) discharged on Mathlib. -/
theorem both_decayBounds_of_kernels
    (hInt : GContinuousAtIntegers) (hGtail : GLargeArgDecay) (hJtail : VaalerJLargeArgDecay) :
    GDecayBound ∧ MathExtras.NumberTheory.Analysis.VaalerJIntegrable.JDecayBound :=
  ⟨gDecayBound_of_residuals hInt hGtail, jDecayBound_of_largeArgTail hJtail⟩

#print axioms continuous_bddOn_Icc
#print axioms decayBound_of_compact_and_tail
#print axioms gDecayBound_of_largeArg
#print axioms gDecayBound_of_residuals
#print axioms gIntegrable_of_residuals
#print axioms gcFourierMatch_of_decayResiduals
#print axioms gEqReJ_of_decayResiduals
#print axioms jTwoIBPDecay_of_largeArgTail
#print axioms jDecayBound_of_largeArgTail
#print axioms jIntegrable_of_largeArgTail
#print axioms both_decayBounds_of_kernels

end MathExtras.NumberTheory.Analysis.VaalerDecayBounds
