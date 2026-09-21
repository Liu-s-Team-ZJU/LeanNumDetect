/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerJIntegrable

/-!
# Vaaler eq. (2.27): the `O((1+|z|)^{-2})` decay `JDecayBound`

This NEW leaf attacks the *single* remaining residual of `VaalerJIntegrable`, namely

    JDecayBound := ∃ C, ∀ z, ‖vaalerJ z‖ ≤ C · (1 + z²)⁻¹,

which is Vaaler's `J(z) ≪ (1+|z|)^{-2}` (eq. (2.27)).  Granting `JDecayBound`,
`VaalerJIntegrable.jIntegrable_of_decay` delivers `JIntegrable`, the analytic half of
Vaaler Theorem 6.

## The mathematics (Vaaler §2, two integrations by parts)

`vaalerJ z = ∫_{-1}^1 Ĵ(τ) e(τz) dτ` is the inverse Fourier transform of the
compactly-supported, continuous, piecewise-`C²` Fejér transform `Ĵ = vaalerJhatFT`,
with `Ĵ(±1) = 0`.  Vaaler's `(1+|z|)^{-2}` decay is `min(1, z^{-2})` up to a constant:

* **Small `|z|` (the constant `1`).**  Trivially `‖vaalerJ z‖ ≤ ∫_{-1}^1 ‖Ĵ(τ) e(τz)‖ dτ
  = ∫_{-1}^1 |Ĵ(τ)| dτ =: C₀` because the character `e(τz)` has unit modulus, so the
  bound is the *same constant* `C₀` for every `z`.  **This half is PROVEN here,
  unconditionally** (`vaalerJ_norm_le_jhatL1`), and gives the `1` in `min(1, z^{-2})`.

* **Large `|z|` (the `z^{-2}` gain).**  Two integrations by parts on each smooth piece
  `(-1,0)`, `(0,1)`:  `∫ Ĵ e(τz) = [Ĵ·e/(2πiz)] − (2πiz)⁻¹∫ Ĵ' e`, boundary terms
  vanishing at `±1` (`Ĵ(±1)=0`); a second IBP turns `∫Ĵ'e` into corner/jump terms (at
  `{−1,0,1}`, where `Ĵ'` has bounded-variation jumps) plus `(2πiz)⁻¹∫Ĵ''e`.  Since
  `Ĵ'`, `Ĵ''` are explicit and bounded on each open piece, the net estimate is
  `‖vaalerJ z‖ ≤ C₂ · z^{-2}` for `|z| ≥ 1`.  This is the genuine two-IBP analytic
  content, isolated below as the **single named `Prop`** `VaalerJTwoIBPDecay` (NOT an
  axiom; a TRUE statement about the explicit `vaalerJ`).

## What is PROVEN here (sorry-free, axiom-free, non-vacuous)

* `norm_jhat_echar` — `‖(Ĵ τ : ℂ) · echarPos τ z‖ = |Ĵ τ|`  (unit-modulus character).
* `jhatL1` (DEFINED) `:= ∫_{-1}^1 |Ĵ τ| dτ`, the small-`z` constant `C₀ ≥ 0`
  (`jhatL1_nonneg`).
* `vaalerJ_norm_le_jhatL1` — **(PROVEN, unconditional)** `‖vaalerJ z‖ ≤ jhatL1` for
  *every* `z`, via `intervalIntegral.norm_integral_le_integral_norm` and the unit
  modulus of `echarPos`.  No integrability hypothesis is needed: the modulus integrand
  `|Ĵ τ|` is `z`-independent.  This is the fully-proven `min(1, …)` half of (2.27).
* `decayBound_of_const_and_quadratic` — **(PROVEN)** the pure real-analysis assembly:
  from a uniform constant bound `‖vaalerJ z‖ ≤ C₀` (all `z`) and a quadratic-tail bound
  `‖vaalerJ z‖ ≤ C₂ · z^{-2}` (for `|z| ≥ 1`) one gets `JDecayBound` with constant
  `2·max(C₀,C₂)` (using `(1+z²)⁻¹ ≥ ½` on `|z|≤1` and `z² ≥ (1+z²)/2` on `|z|≥1`).
* `jDecayBound_of_twoIBP` — **(PROVEN)** `VaalerJTwoIBPDecay → JDecayBound`, combining
  the proven small-`z` constant `jhatL1` with the named large-`z` tail.

## The single remaining genuine gap (named `Prop`, NOT an axiom)

* `VaalerJTwoIBPDecay : ∃ C₂, ∀ z, 1 ≤ |z| → ‖vaalerJ z‖ ≤ C₂ · (z²)⁻¹` — the large-`z`
  quadratic decay produced by the *two* integrations by parts of Vaaler §2 (the explicit
  bounded `Ĵ'`, `Ĵ''` on `(-1,0)∪(0,1)` and the vanishing/jump boundary data at
  `{−1,0,1}`).  It is a TRUE statement about the explicit `vaalerJ` (NOT vacuous, NOT an
  `axiom`).  The complementary small-`z` half is already PROVEN here; this tail is the
  only thing between this file and the unconditional `JDecayBound`, hence `JIntegrable`,
  hence the transform-half of Vaaler Theorem 6.

`jDecayBound_of_twoIBP` then yields `JDecayBound`, and
`VaalerJIntegrable.jIntegrable_of_decay (jDecayBound_of_twoIBP h)` yields `JIntegrable`.

## Hard constraints honoured

NEW leaf only; nothing existing/committed is edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.  The single
blocked piece is the named `Prop` `VaalerJTwoIBPDecay`, never an `axiom`.  Not vacuous:
the unit-modulus character bound, the unconditional uniform constant bound
`‖vaalerJ z‖ ≤ jhatL1`, the real-analysis `min`-assembly, and the
`VaalerJTwoIBPDecay → JDecayBound` reduction are concrete facts about the explicit
`vaalerJ`/`vaalerJhatFT`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eq. (2.27), p. 192.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped BigOperators FourierTransform RealInnerProductSpace

namespace MathExtras.NumberTheory.Analysis.VaalerJDecayBound

open MathExtras.NumberTheory.Analysis.VaalerFejerCoefficientNonneg
open MathExtras.NumberTheory.Analysis.VaalerExcessFT
open MathExtras.NumberTheory.Analysis.VaalerCor7RouteB
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerJIntegrable

/-! ## §1 — The unit-modulus character bound on the integrand -/

/-- The modulus of the defining integrand is `z`-independent:
`‖(Ĵ τ : ℂ) · echarPos τ z‖ = |Ĵ τ|`. -/
theorem norm_jhat_echar (τ z : ℝ) :
    ‖(vaalerJhatFT τ : ℂ) * echarPos τ z‖ = |vaalerJhatFT τ| := by
  rw [norm_mul, norm_echarPos, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-! ## §2 — The small-`z` constant `C₀ = ∫_{-1}^1 |Ĵ|` and the uniform bound -/

/-- `C₀ := ∫_{-1}^1 |Ĵ(τ)| dτ`, the small-`z` constant (the `1` in `min(1, z^{-2})`). -/
def jhatL1 : ℝ := ∫ τ in (-1 : ℝ)..(1 : ℝ), |vaalerJhatFT τ|

/-- `C₀ ≥ 0`. -/
theorem jhatL1_nonneg : 0 ≤ jhatL1 := by
  unfold jhatL1
  apply intervalIntegral.integral_nonneg (by norm_num : (-1 : ℝ) ≤ 1)
  intro τ _
  exact abs_nonneg _

/-- **PROVEN (unconditional).**  `‖vaalerJ z‖ ≤ jhatL1` for *every* `z`.

`vaalerJ z = ∫_{-1}^1 (Ĵ τ : ℂ)·echarPos τ z dτ`, so by
`intervalIntegral.norm_integral_le_integral_norm` (`-1 ≤ 1`)
`‖vaalerJ z‖ ≤ ∫_{-1}^1 ‖(Ĵ τ : ℂ)·echarPos τ z‖ dτ`, and the integrand's norm is the
`z`-independent `|Ĵ τ|` (`norm_jhat_echar`, unit-modulus character).  Hence the bound is
the single constant `jhatL1 = ∫_{-1}^1 |Ĵ|`.  No integrability hypothesis is needed. -/
theorem vaalerJ_norm_le_jhatL1 (z : ℝ) : ‖vaalerJ z‖ ≤ jhatL1 := by
  unfold vaalerJ jhatL1
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)).trans ?_
  apply le_of_eq
  refine intervalIntegral.integral_congr ?_
  intro τ _
  exact norm_jhat_echar τ z

/-! ## §3 — Pure real-analysis assembly: `const` + `quadratic tail` ⇒ `(1+z²)⁻¹` -/

/-- **PROVEN (real analysis).**  From a uniform constant bound and a quadratic-tail bound
one obtains the `(1+z²)⁻¹` envelope of Vaaler (2.27).

Given `0 ≤ C₀`, `∀ z, ‖vaalerJ z‖ ≤ C₀`, and `∀ z, 1 ≤ |z| → ‖vaalerJ z‖ ≤ C₂·(z²)⁻¹`,
then `∀ z, ‖vaalerJ z‖ ≤ (2·max C₀ C₂)·(1+z²)⁻¹` (the tail constant `C₂` may have any
sign; only `(z²)⁻¹ ≥ 0` is used in the large-`z` branch).

For `|z| ≤ 1`: `(1+z²)⁻¹ ≥ ½` (since `z² ≤ 1`), so `C₀ ≤ 2·C₀·(1+z²)⁻¹`.
For `|z| ≥ 1`: `z² ≥ (1+z²)/2` (since `1 ≤ z²`), so `C₂·(z²)⁻¹ ≤ 2·C₂·(1+z²)⁻¹`. -/
theorem decayBound_of_const_and_quadratic
    {C₀ C₂ : ℝ} (hC₀ : 0 ≤ C₀)
    (hconst : ∀ z : ℝ, ‖vaalerJ z‖ ≤ C₀)
    (hquad : ∀ z : ℝ, 1 ≤ |z| → ‖vaalerJ z‖ ≤ C₂ * (z ^ 2)⁻¹) :
    ∀ z : ℝ, ‖vaalerJ z‖ ≤ (2 * max C₀ C₂) * (1 + z ^ 2)⁻¹ := by
  intro z
  have hden_pos : (0 : ℝ) < 1 + z ^ 2 := by positivity
  have hmax₀ : C₀ ≤ max C₀ C₂ := le_max_left _ _
  have hmax₂ : C₂ ≤ max C₀ C₂ := le_max_right _ _
  have hmax_nonneg : 0 ≤ max C₀ C₂ := le_trans hC₀ hmax₀
  have hinvpos : (0 : ℝ) < (1 + z ^ 2)⁻¹ := by positivity
  by_cases hz : |z| ≤ 1
  · -- small z: use the constant bound; (1+z²)⁻¹ ≥ 1/2
    have hz2 : z ^ 2 ≤ 1 := by nlinarith [sq_abs z, abs_nonneg z]
    have hhalf : (1 : ℝ) ≤ 2 * (1 + z ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ hden_pos]; nlinarith [hz2]
    calc ‖vaalerJ z‖ ≤ C₀ := hconst z
      _ = C₀ * 1 := by ring
      _ ≤ max C₀ C₂ * (2 * (1 + z ^ 2)⁻¹) :=
            mul_le_mul hmax₀ hhalf (by norm_num) hmax_nonneg
      _ = 2 * max C₀ C₂ * (1 + z ^ 2)⁻¹ := by ring
  · -- large z: use the quadratic tail; z² ≥ (1+z²)/2
    rw [not_le] at hz
    have hz1 : 1 ≤ |z| := le_of_lt hz
    have hz2 : 1 ≤ z ^ 2 := by nlinarith [sq_abs z, abs_nonneg z]
    have hz2pos : (0 : ℝ) < z ^ 2 := by linarith
    -- (z²)⁻¹ ≤ 2·(1+z²)⁻¹  ⟺  1 + z² ≤ 2·z²  ⟺  1 ≤ z²
    have hkey : (z ^ 2)⁻¹ ≤ 2 * (1 + z ^ 2)⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ hz2pos]
      rw [show (2 : ℝ) * (1 + z ^ 2)⁻¹ * z ^ 2 = 2 * z ^ 2 * (1 + z ^ 2)⁻¹ by ring,
        le_mul_inv_iff₀ hden_pos]
      nlinarith [hz2]
    calc ‖vaalerJ z‖ ≤ C₂ * (z ^ 2)⁻¹ := hquad z hz1
      _ ≤ max C₀ C₂ * (2 * (1 + z ^ 2)⁻¹) :=
            mul_le_mul hmax₂ hkey (by positivity) hmax_nonneg
      _ = 2 * max C₀ C₂ * (1 + z ^ 2)⁻¹ := by ring

/-! ## §4 — The single named residual (Vaaler 2.27 two-IBP tail) and the assembly -/

/-- **Residual (Vaaler eq. (2.27), the two-IBP `z^{-2}` tail).**  For `|z| ≥ 1`,
`‖vaalerJ z‖ ≤ C₂ · (z²)⁻¹`.  This is the gain from the *two* integrations by parts of
Vaaler §2 on `∫_{-1}^1 Ĵ(τ) e(τz) dτ`: boundary terms vanish at `±1` (`Ĵ(±1) = 0`), the
corner jumps of `Ĵ'` at `{−1,0,1}` contribute `O(z^{-2})`, and the explicit bounded
`Ĵ''` on `(-1,0) ∪ (0,1)` gives the residual `∫ Ĵ'' e = O(1)`.  A TRUE statement about
the explicit `vaalerJ`; NOT vacuous, NOT an `axiom`.  (The complementary small-`z` half
is PROVEN above as `vaalerJ_norm_le_jhatL1`.) -/
def VaalerJTwoIBPDecay : Prop := ∃ C₂ : ℝ, ∀ z : ℝ, 1 ≤ |z| → ‖vaalerJ z‖ ≤ C₂ * (z ^ 2)⁻¹

/-- **PROVEN.**  `VaalerJTwoIBPDecay → JDecayBound`.  Combines the unconditional small-`z`
constant bound `vaalerJ_norm_le_jhatL1` (constant `jhatL1 ≥ 0`) with the named large-`z`
quadratic tail, via the real-analysis assembly `decayBound_of_const_and_quadratic`.  We
may take `C₂ ≥ 0` WLOG: if the supplied constant is negative the tail bound forces
`‖vaalerJ z‖ ≤ 0` at `|z| = 1`, but more simply `max C₂ 0` still satisfies the tail
since `(z²)⁻¹ ≥ 0`. -/
theorem jDecayBound_of_twoIBP (h : VaalerJTwoIBPDecay) : JDecayBound := by
  obtain ⟨C₂, hC₂⟩ := h
  -- Replace C₂ by max C₂ 0 ≥ 0; the tail bound is preserved since (z²)⁻¹ ≥ 0.
  have hquad : ∀ z : ℝ, 1 ≤ |z| → ‖vaalerJ z‖ ≤ (max C₂ 0) * (z ^ 2)⁻¹ := by
    intro z hz
    refine (hC₂ z hz).trans ?_
    apply mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  refine ⟨2 * max jhatL1 (max C₂ 0), ?_⟩
  exact decayBound_of_const_and_quadratic jhatL1_nonneg
    vaalerJ_norm_le_jhatL1 hquad

/-- **PROVEN.**  `VaalerJTwoIBPDecay → JIntegrable`: composing `jDecayBound_of_twoIBP`
with `VaalerJIntegrable.jIntegrable_of_decay`, the analytic transform-half of Vaaler
Theorem 6 collapses to the single named two-IBP tail `VaalerJTwoIBPDecay`. -/
theorem jIntegrable_of_twoIBP (h : VaalerJTwoIBPDecay) : JIntegrable :=
  jIntegrable_of_decay (jDecayBound_of_twoIBP h)

#print axioms norm_jhat_echar
#print axioms jhatL1_nonneg
#print axioms vaalerJ_norm_le_jhatL1
#print axioms decayBound_of_const_and_quadratic
#print axioms jDecayBound_of_twoIBP
#print axioms jIntegrable_of_twoIBP

end MathExtras.NumberTheory.Analysis.VaalerJDecayBound
