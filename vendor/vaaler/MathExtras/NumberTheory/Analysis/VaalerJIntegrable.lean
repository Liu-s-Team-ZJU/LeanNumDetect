/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT

/-!
# Vaaler Theorem 6, transform-half: `J = 𝓕(Ĵ) ∈ L¹(ℝ)`  (`JIntegrable`)

This NEW leaf attacks the remaining *analytic* residual of `VaalerTheorem6JFT`:

    JIntegrable := Integrable (𝓕 vaalerJCcont).

Here `vaalerJ z = ∫_{-1}^1 Ĵ(τ) e(τz) dτ` (`VaalerCor7RouteB.vaalerJ`) is the inverse
Fourier transform of the compactly-supported `Ĵ = vaalerJhatFT`, and (Vaaler eq. 2.27)
`J(z) ≪ (1+|z|)^{-2}` because `Ĵ` is continuous, piecewise-`C¹`, and vanishes at the
endpoints `±1` (integration by parts gains two factors of `1/z`).  An
`O((1+|z|)^{-2})` bound is integrable on `ℝ` (`(1+z²)^{-1}` majorant), so `J ∈ L¹`.

## What is PROVEN here (sorry-free, axiom-free, non-vacuous)

* `vaalerJ_measurable` — `vaalerJ` is `AEStronglyMeasurable` (the defining interval
  integral, written as a full-line integral of an indicator and pushed through the
  Fubini measurability lemma `AEStronglyMeasurable.integral_prod_right'`).  This is a
  *self-contained* fact, **not** routed through the (still-open) corner-continuity
  residual of `VaalerTheorem6JFT`.
* `norm_echarPos` — `‖e(τz)‖ = 1`, the unit-modulus character fact.
* `fourier_vaalerJCcont_eq_vaalerJ` — **(PROVEN)** `𝓕 vaalerJCcont = vaalerJ` as functions
  on `ℝ`: `𝓕⁻ f w = 𝓕 f (−w)` (Mathlib `fourierInv_eq_fourier_neg`) combined with the
  PROVEN bridge `vaalerJ = 𝓕⁻ vaalerJCcont` (`vaalerJ_eq_fourierInv_cont`) and the PROVEN
  evenness `vaalerJ_even`.  This is the load-bearing identification of the Theorem-6
  transform with the concrete `vaalerJ`.
* `jIntegrable_iff_vaalerJ_integrable` — **(PROVEN)** `JIntegrable ↔ Integrable vaalerJ`.
  Reduces the named residual `VaalerTheorem6JFT.JIntegrable` to integrability of the
  *concrete* `vaalerJ`.
* `JDecayBound` (named `Prop`, NOT axiom) — the `O((1+|z|)^{-2})` decay
  `∃ C, ∀ z, ‖vaalerJ z‖ ≤ C·(1+z²)⁻¹`, the genuine remaining IBP estimate (Vaaler 2.27).
* `vaalerJ_integrable_of_decay` — **(PROVEN)** `JDecayBound → Integrable vaalerJ`
  (`Integrable.mono'` against the Mathlib-integrable majorant `(1+z²)⁻¹`,
  `integrable_inv_one_add_sq`, using `vaalerJ_measurable`).
* `jIntegrable_of_decay` — **(PROVEN)** `JDecayBound → JIntegrable`, hence the analytic
  residual of Theorem 6 collapses to the single decay estimate `JDecayBound`.

## The single remaining genuine gap (named `Prop`, NOT an axiom)

* `JDecayBound` — `‖vaalerJ z‖ ≤ C·(1+z²)⁻¹` for all `z`.  This is precisely Vaaler's
  `J(z) ≪ (1+|z|)^{-2}` (eq. 2.27): two integrations by parts on
  `∫_{-1}^1 Ĵ(τ) e(τz) dτ`, with boundary terms vanishing because `Ĵ(±1) = 0` and `Ĵ`
  is continuous, and the resulting `∫ Ĵ''(τ) e(τz)` bounded since `Ĵ` is piecewise-`C²`
  away from the corners `{−1,0,1}`.  It is a TRUE statement about the explicit `vaalerJ`
  (NOT a vacuous hypothesis), and the *only* thing standing between this file and the
  unconditional `JIntegrable`.

Granting `JDecayBound`, `jIntegrable_of_decay` delivers `JIntegrable` outright, which
together with `VaalerTheorem6JFT.fourier_vaalerJ_eq_of` (and its corner-continuity
residual) gives Vaaler Theorem 6.

## Hard constraints honoured

NEW leaf only; nothing existing/committed is edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.  Blocked
content is the named `Prop` `JDecayBound`, never an `axiom`.  Not vacuous: the
measurability, the unit-modulus character, the `𝓕 vaalerJCcont = vaalerJ` identification, the
`JIntegrable ↔ Integrable vaalerJ` reduction, and the `decay ⇒ integrable` implication
are concrete facts about the explicit `vaalerJ`/`vaalerJCcont`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.27)–(2.32), p. 192.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped BigOperators FourierTransform RealInnerProductSpace

namespace MathExtras.NumberTheory.Analysis.VaalerJIntegrable

open MathExtras.NumberTheory.Analysis.VaalerFejerCoefficientNonneg
open MathExtras.NumberTheory.Analysis.VaalerExcessFT
open MathExtras.NumberTheory.Analysis.VaalerCor7RouteB
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT

/-! ## §1 — Measurability of the integrand pieces -/

/-- `vaalerJhatFT` is measurable (rewrite `cot = cos/sin` so `fun_prop` succeeds). -/
theorem vaalerJhatFT_measurable : Measurable vaalerJhatFT := by
  unfold vaalerJhatFT
  apply Measurable.ite
  · exact measurableSet_lt (by fun_prop) measurable_const
  · have : (fun t : ℝ => vaalerJhat |t|)
        = (fun t : ℝ => Real.pi * |t| * (1 - |t|) *
            (Real.cos (Real.pi * |t|) / Real.sin (Real.pi * |t|)) + |t|) := by
      funext t; rw [vaalerJhat, Real.cot_eq_cos_div_sin]
    rw [this]; fun_prop
  · fun_prop

/-- `vaalerJC = (vaalerJhatFT · : ℂ)` is measurable. -/
theorem vaalerJC_measurable : Measurable vaalerJC := by
  have : vaalerJC = fun t : ℝ => (vaalerJhatFT t : ℂ) := rfl
  rw [this]
  exact Complex.measurable_ofReal.comp vaalerJhatFT_measurable

/-- The kernel `echarPos τ z = exp(2πi τz)` is jointly continuous in `(z, τ)`. -/
theorem echarPos_continuous : Continuous (fun p : ℝ × ℝ => echarPos p.2 p.1) := by
  unfold echarPos
  fun_prop

/-! ## §2 — `vaalerJ` is `AEStronglyMeasurable` (self-contained) -/

/-- `vaalerJ z = ∫ τ, (Ioc (-1) 1).indicator (fun τ => Ĵ(τ)·e(τz)) τ`: the defining
interval integral, rewritten as a full-line Bochner integral of an indicator (over the
measurable set `Ioc (-1) 1`).  This is the form on which the Fubini measurability lemma
applies. -/
theorem vaalerJ_eq_indicator_integral (z : ℝ) :
    vaalerJ z = ∫ τ, (Set.Ioc (-1 : ℝ) 1).indicator
      (fun τ => (vaalerJhatFT τ : ℂ) * echarPos τ z) τ := by
  unfold vaalerJ
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]

/-- **PROVEN (self-contained).**  `vaalerJ` is `AEStronglyMeasurable`.  The integrand
`(z, τ) ↦ 1_{Ioc(-1,1)}(τ)·Ĵ(τ)·e(τz)` is `AEStronglyMeasurable` on the product (the
indicator of a measurable set applied to a measurable-in-`τ`, continuous-in-`z` product),
so `z ↦ ∫ τ, …` is `AEStronglyMeasurable` by `AEStronglyMeasurable.integral_prod_right'`.
Crucially this does **not** use the open corner-continuity residual. -/
theorem vaalerJ_measurable : AEStronglyMeasurable vaalerJ := by
  -- joint measurability of the integrand `g (z, τ) = 1_{Ioc} τ · Ĵ τ · e(τ z)`
  have hmeas_prod : Measurable
      (fun p : ℝ × ℝ => (Set.Ioc (-1 : ℝ) 1).indicator
        (fun τ => (vaalerJhatFT τ : ℂ) * echarPos τ p.1) p.2) := by
    -- the inner product `Ĵ(τ)·e(τ z)` is measurable jointly (meas in τ × cont in z)
    have h1 : Measurable (fun p : ℝ × ℝ => (vaalerJhatFT p.2 : ℂ)) :=
      vaalerJC_measurable.comp measurable_snd
    have h2 : Measurable (fun p : ℝ × ℝ => echarPos p.2 p.1) :=
      echarPos_continuous.measurable
    have hprod : Measurable
        (fun p : ℝ × ℝ => (vaalerJhatFT p.2 : ℂ) * echarPos p.2 p.1) := h1.mul h2
    -- indicator in the τ = p.2 coordinate of the measurable set `Ioc (-1) 1`
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioc (-1 : ℝ) 1} :=
      measurable_snd measurableSet_Ioc
    -- `Measurable.indicator` gives measurability of `{p | p.2 ∈ Ioc}.indicator g`
    have hind := hprod.indicator hset
    -- the indicator over the set `{p | p.2 ∈ Ioc}` agrees with the target form
    have hfun : ({p : ℝ × ℝ | p.2 ∈ Set.Ioc (-1 : ℝ) 1}.indicator
          (fun p => (vaalerJhatFT p.2 : ℂ) * echarPos p.2 p.1))
        = (fun p : ℝ × ℝ => (Set.Ioc (-1 : ℝ) 1).indicator
            (fun τ => (vaalerJhatFT τ : ℂ) * echarPos τ p.1) p.2) := by
      funext p
      by_cases hp : p.2 ∈ Set.Ioc (-1 : ℝ) 1
      · rw [Set.indicator_of_mem (by exact hp), Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem (by exact hp), Set.indicator_of_notMem hp]
    rw [hfun] at hind
    exact hind
  -- push through Fubini measurability
  have hAE := hmeas_prod.aestronglyMeasurable.integral_prod_right'
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  -- rewrite `vaalerJ` into that integral form
  refine hAE.congr ?_
  filter_upwards with z
  rw [vaalerJ_eq_indicator_integral z]

/-! ## §3 — `‖echarPos τ z‖ = 1` (the character has unit modulus) -/

/-- The character `echarPos τ z = exp(2πi τz)` has unit modulus. -/
theorem norm_echarPos (τ z : ℝ) : ‖echarPos τ z‖ = 1 := by
  unfold echarPos
  rw [show (2 : ℂ) * π * Complex.I * τ * z
        = ((2 * π * (τ * z) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.norm_exp_ofReal_mul_I]

/-! ## §4 — `𝓕 vaalerJCcont = vaalerJ`  and the residual reduction -/

/-- **PROVEN.**  `𝓕 vaalerJCcont = vaalerJ` as functions on `ℝ`.

`𝓕⁻ vaalerJCcont w = 𝓕 vaalerJCcont (−w)` (`fourierInv_eq_fourier_neg`).  With the PROVEN
bridge `vaalerJ = 𝓕⁻ vaalerJCcont` (`vaalerJ_eq_fourierInv_cont`) this gives
`vaalerJ w = 𝓕 vaalerJCcont (−w)`, and replacing `w ↦ −t` plus evenness `vaalerJ (−t) =
vaalerJ t` (`vaalerJ_even`) yields `𝓕 vaalerJCcont t = vaalerJ t`. -/
theorem fourier_vaalerJCcont_eq_vaalerJ : 𝓕 vaalerJCcont = vaalerJ := by
  funext t
  have hbridge : vaalerJ (-t) = 𝓕 vaalerJCcont (-(-t)) := by
    rw [vaalerJ_eq_fourierInv_cont]; exact fourierInv_eq_fourier_neg vaalerJCcont (-t)
  rw [neg_neg] at hbridge
  rw [← hbridge, vaalerJ_even]

/-- **PROVEN.**  `JIntegrable ↔ Integrable vaalerJ`.  Direct rewrite by
`fourier_vaalerJCcont_eq_vaalerJ`. -/
theorem jIntegrable_iff_vaalerJ_integrable : JIntegrable ↔ Integrable vaalerJ := by
  unfold JIntegrable
  rw [fourier_vaalerJCcont_eq_vaalerJ]

/-! ## §5 — The named decay residual, and `decay ⇒ Integrable` -/

/-- **Residual (`O((1+|z|)^{-2})` decay).**  Vaaler eq. (2.27):
`‖J(z)‖ ≤ C·(1+z²)⁻¹` for some constant `C`.  `Ĵ` is continuous, piecewise-`C¹`/`C²`,
and `Ĵ(±1) = 0`, so two integrations by parts on `∫_{-1}^1 Ĵ(τ) e(τz) dτ` (boundary
terms vanishing) give `J(z) = O(z^{-2})`.  TRUE statement about the explicit `vaalerJ`;
NOT an axiom, NOT vacuous. -/
def JDecayBound : Prop := ∃ C : ℝ, ∀ z : ℝ, ‖vaalerJ z‖ ≤ C * (1 + z ^ 2)⁻¹

/-- **PROVEN.**  `JDecayBound → Integrable vaalerJ`.  `Integrable.mono'` against the
Mathlib-integrable majorant `C·(1+z²)⁻¹` (`integrable_inv_one_add_sq`), using the
self-contained `vaalerJ_measurable`. -/
theorem vaalerJ_integrable_of_decay (h : JDecayBound) : Integrable vaalerJ := by
  obtain ⟨C, hC⟩ := h
  have hmaj : Integrable (fun z : ℝ => C * (1 + z ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  refine hmaj.mono' vaalerJ_measurable ?_
  filter_upwards with z
  exact hC z

/-- **PROVEN.**  `JDecayBound → JIntegrable`: the analytic residual of Vaaler Theorem 6
collapses to the single decay estimate `JDecayBound`. -/
theorem jIntegrable_of_decay (h : JDecayBound) : JIntegrable :=
  jIntegrable_iff_vaalerJ_integrable.mpr (vaalerJ_integrable_of_decay h)

#print axioms vaalerJhatFT_measurable
#print axioms vaalerJC_measurable
#print axioms echarPos_continuous
#print axioms vaalerJ_eq_indicator_integral
#print axioms vaalerJ_measurable
#print axioms norm_echarPos
#print axioms fourier_vaalerJCcont_eq_vaalerJ
#print axioms jIntegrable_iff_vaalerJ_integrable
#print axioms vaalerJ_integrable_of_decay
#print axioms jIntegrable_of_decay

end MathExtras.NumberTheory.Analysis.VaalerJIntegrable
