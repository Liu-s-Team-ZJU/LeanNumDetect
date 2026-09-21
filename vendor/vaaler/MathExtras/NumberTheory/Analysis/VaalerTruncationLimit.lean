/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerHNAssembly
import Mathlib.Analysis.Fourier.Inversion

/-!
# Vaaler Theorem 6, the truncation limit: `∃ Gc, GcEqVaalerJ Gc` ⇒ `GEqReJ` (minor D-1)

This NEW leaf closes the SINGLE remaining minor residual of the `H_N` shifted-Fejér
route — the truncation limit `HNDerivConverges := ∃ Gc, GcEqVaalerJ Gc` — *modulo one
correctly-stated analytic `Prop`*, and threads it through the already-proven
`VaalerJFTviaHN.GcEqVaalerJ_of_HN_backbone` to obtain `GEqReJ`, the entire `H′ = 2J`
minor wall.

## What `GcEqVaalerJ` needs, and the chosen witness

`GcEqVaalerJ Gc := (∀ x, (Gc x).re = G x) ∧ Gc = vaalerJ` (`VaalerJFourierTransform`).
We take the witness `Gc := vaalerJ`, so the second conjunct is `rfl`, and the WHOLE
content collapses to the **real-part identity**

    (vaalerJ x).re = G x      for every `x`,                                   (RP)

where `G = ½ H′` is the explicit half-derivative (`VaalerHPrimeEqTwoJ.G`) and
`vaalerJ z = ∫_{-1}^1 Ĵ(τ) e(τz) dτ` is the band-limited inverse transform of Vaaler's
`Ĵ` (`VaalerCor7RouteB.vaalerJ`).

## The genuine analytic step, isolated as ONE named `Prop`

(RP) is Vaaler eq. (2.31)→(2.32): the explicit `½H′` equals the inverse-FT evaluation
`Re ∫_{-1}^1 Ĵ e`.  The derivative-level Fourier mechanism is FULLY PROVEN upstream
(`VaalerHNAssembly`: `HNcore_deriv_FT_eq`, `derivLevelTotal_eq_vaalerJhat`,
`halfDeriv_FT_eq_mul`, `tailDeriv_collapse`; `VaalerOscillatoryRemainder`: Riemann–
Lebesgue `osc_N → 0`).  What remains is the `N → ∞` limit interchange producing
`𝓕(½H′) = Ĵ = 𝓕 vaalerJ`, plus the regularity (`G` continuous + `L¹`, `𝓕 G ∈ L¹`)
that makes the Fourier transform **injective** (Mathlib `Continuous.fourierInv_fourier_eq`,
`𝓕⁻(𝓕 f) = f`).  We bundle EXACTLY this — the FT-equality together with the regularity
hypotheses of Fourier inversion for the complexification `GC x := (G x : ℂ)` and for
`vaalerJ` — into the single named `Prop` `GCFourierMatch`.  It is a TRUE statement
(Theorem 6 + the explicit derivative + the `1/x²` decay of `½H′`), NOT an axiom, and is
genuinely *more primitive* than (RP): we DERIVE the function match `GC = vaalerJ` (hence
(RP)) from it by Mathlib's Fourier-inversion injectivity.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `GC` (DEFINED) — the complexification `GC x = (G x : ℂ)` of the explicit `½H′`.
* `GC_re` — `(GC x).re = G x` (the real part is `G`, by `Complex.ofReal_re`).
* `GCFourierMatch` (named `Prop`, NOT an axiom) — the bundled analytic step: `GC` and
  `vaalerJ` are continuous and `L¹` with `L¹` transforms, and `𝓕 GC = 𝓕 vaalerJ`.
* `gc_eq_vaalerJ_of_match` — **PROVEN**: from `GCFourierMatch`, FT-injectivity gives
  `GC = vaalerJ` (functions).
* `gcEqVaalerJ_exists_of_match` — **PROVEN**: from `GCFourierMatch`, the truncation limit
  `∃ Gc, GcEqVaalerJ Gc` holds (witness `Gc := vaalerJ`).
* `gEqReJ_of_match` — **PROVEN**: from `GCFourierMatch`, `GEqReJ` (the minor D-1 wall)
  via `VaalerHNAssembly.gEqReJ_of_truncationLimit`.
* `derivInterpHEqTwoJ_of_match` — **PROVEN**: the bundled D-1 residual, likewise.

## Honest status

The whole minor D-1 wall now rests on the SINGLE named analytic `Prop` `GCFourierMatch`
(FT-equality `𝓕 GC = 𝓕 vaalerJ` + the Fourier-inversion regularity).  Everything else —
the reduction of `GcEqVaalerJ` to the function match, the FT-injectivity passage, and the
wiring to `GEqReJ` — is FULLY PROVEN here on top of Mathlib's `Continuous.fourierInv_fourier_eq`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.27)–(2.32), p. 192; Mathlib `Analysis.Fourier.Inversion`
(`Continuous.fourierInv_fourier_eq`, `𝓕⁻(𝓕 f) = f`).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped BigOperators FourierTransform

namespace MathExtras.NumberTheory.Analysis.VaalerTruncationLimit

open MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ
open MathExtras.NumberTheory.Analysis.VaalerCor7RouteB
open MathExtras.NumberTheory.Analysis.VaalerJFourierTransform
open MathExtras.NumberTheory.Analysis.VaalerJFTviaHN

/-! ## §1 — The complexification `GC` of the explicit half-derivative `G` -/

/-- **`GC` (DEFINED): the complexification `GC x = (G x : ℂ)`** of the explicit
half-derivative `G = ½ H′` (`VaalerHPrimeEqTwoJ.G`).  This is the complex extension of
`G` whose Fourier transform we match against `vaalerJ`'s. -/
def GC (x : ℝ) : ℂ := (G x : ℂ)

@[simp] theorem GC_apply (x : ℝ) : GC x = (G x : ℂ) := rfl

/-- **PROVEN.**  `(GC x).re = G x`: the real part of the complexification is `G` itself
(`Complex.ofReal_re`).  This is the first conjunct of `GcEqVaalerJ` for the complex
witness — and, after the function match `GC = vaalerJ`, for the `vaalerJ` witness. -/
theorem GC_re (x : ℝ) : (GC x).re = G x := by
  rw [GC_apply, Complex.ofReal_re]

/-! ## §2 — The single named analytic `Prop`: the Fourier-transform match -/

/-- **The single remaining analytic step, ONE named `Prop` (never an `axiom`).**

The Fourier transforms of the complexified explicit half-derivative `GC = (½H′ : ℂ)`
and of the band-limited `vaalerJ` agree, **and** both functions satisfy the regularity
hypotheses of Mathlib's Fourier-inversion injectivity (continuous, `L¹`, with `L¹`
Fourier transform):

* `Continuous GC`, `Integrable GC`, `Integrable (𝓕 GC)`;
* `Continuous vaalerJ`, `Integrable vaalerJ`, `Integrable (𝓕 vaalerJ)`;
* `𝓕 GC = 𝓕 vaalerJ`.

This is Vaaler eq. (2.31)→(2.32): the derivative-level Fourier mechanism `𝓕(½H_N′) → Ĵ`
is PROVEN upstream (`VaalerHNAssembly`, `VaalerOscillatoryRemainder`); what remains is the
`N → ∞` limit interchange `𝓕(½H′) = Ĵ = 𝓕 vaalerJ` together with the `1/x²` decay of
`½H′` giving the `L¹` regularity.  It is a TRUE statement, genuinely more primitive than
the real-part identity (RP): (RP) is DERIVED from it below via Fourier injectivity. -/
structure GCFourierMatch : Prop where
  /-- `GC` is continuous (the explicit `½H′` is continuous off ℤ and the kernel removes
  the apparent poles; Vaaler eq. (2.32)). -/
  contGC : Continuous GC
  /-- `GC ∈ L¹(ℝ)` (the `1/x²` decay of `½H′`, Vaaler eq. (2.32)). -/
  intGC : Integrable GC
  /-- `𝓕 GC ∈ L¹(ℝ)` (it equals `𝓕 vaalerJ = Ĵ`, supported on `[−1,1]`). -/
  intFTGC : Integrable (𝓕 GC)
  /-- `vaalerJ` is continuous. -/
  contJ : Continuous vaalerJ
  /-- `vaalerJ ∈ L¹(ℝ)`. -/
  intJ : Integrable vaalerJ
  /-- `𝓕 vaalerJ ∈ L¹(ℝ)` (it equals the compactly-supported `Ĵ`). -/
  intFTJ : Integrable (𝓕 vaalerJ)
  /-- the Fourier transforms agree (the analytic heart, `𝓕(½H′) = Ĵ = 𝓕 vaalerJ`). -/
  ftEq : 𝓕 GC = 𝓕 vaalerJ

/-! ## §3 — From the FT-match to the function match (Fourier injectivity, PROVEN) -/

/-- **PROVEN — the function match `GC = vaalerJ` from `GCFourierMatch`.**

Mathlib's Fourier-inversion injectivity `Continuous.fourierInv_fourier_eq`
(`𝓕⁻(𝓕 f) = f` for continuous `f` with `f, 𝓕 f ∈ L¹`) applied to both `GC` and
`vaalerJ`, combined with the FT-equality `𝓕 GC = 𝓕 vaalerJ`, forces `GC = vaalerJ`:

    GC = 𝓕⁻(𝓕 GC) = 𝓕⁻(𝓕 vaalerJ) = vaalerJ. -/
theorem gc_eq_vaalerJ_of_match (h : GCFourierMatch) : GC = vaalerJ := by
  have hGC : 𝓕⁻ (𝓕 GC) = GC := h.contGC.fourierInv_fourier_eq h.intGC h.intFTGC
  have hJ : 𝓕⁻ (𝓕 vaalerJ) = vaalerJ := h.contJ.fourierInv_fourier_eq h.intJ h.intFTJ
  calc GC = 𝓕⁻ (𝓕 GC) := hGC.symm
    _ = 𝓕⁻ (𝓕 vaalerJ) := by rw [h.ftEq]
    _ = vaalerJ := hJ

/-! ## §4 — The truncation limit and the minor D-1 wall (PROVEN from the match) -/

/-- **PROVEN — `GcEqVaalerJ vaalerJ` from `GCFourierMatch`.**

With the function match `GC = vaalerJ` (`gc_eq_vaalerJ_of_match`), the witness
`Gc := vaalerJ` satisfies both conjuncts of `GcEqVaalerJ`:
* `(vaalerJ x).re = G x`: from `vaalerJ x = GC x = (G x : ℂ)` and `GC_re`;
* `vaalerJ = vaalerJ`: `rfl`. -/
theorem gcEqVaalerJ_vaalerJ_of_match (h : GCFourierMatch) :
    GcEqVaalerJ vaalerJ := by
  have hfun : GC = vaalerJ := gc_eq_vaalerJ_of_match h
  refine ⟨fun x => ?_, rfl⟩
  -- `(vaalerJ x).re = (GC x).re = G x`
  rw [← hfun, GC_re]

/-- **PROVEN — the truncation limit `∃ Gc, GcEqVaalerJ Gc` from `GCFourierMatch`.**
This is exactly `VaalerJFTviaHN.HNDerivConverges`, the single remaining minor residual
of the `H_N` route. -/
theorem gcEqVaalerJ_exists_of_match (h : GCFourierMatch) :
    ∃ Gc : ℝ → ℂ, GcEqVaalerJ Gc :=
  ⟨vaalerJ, gcEqVaalerJ_vaalerJ_of_match h⟩

/-- **PROVEN — the minor D-1 wall `GEqReJ` from `GCFourierMatch`.**

Threads the truncation limit through the proven `H_N` backbone reduction
`VaalerHNAssembly.gEqReJ_of_truncationLimit`
(`= VaalerJFTviaHN.GcEqVaalerJ_of_HN_backbone`), closing the entire `H′ = 2J` minor
wall modulo the single analytic `Prop` `GCFourierMatch`. -/
theorem gEqReJ_of_match (h : GCFourierMatch) :
    MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ.GEqReJ :=
  MathExtras.NumberTheory.Analysis.VaalerHNAssembly.gEqReJ_of_truncationLimit
    (gcEqVaalerJ_exists_of_match h)

/-- **PROVEN — the bundled D-1 residual `DerivInterpHEqTwoJ` from `GCFourierMatch`.** -/
theorem derivInterpHEqTwoJ_of_match (h : GCFourierMatch) :
    MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail.DerivInterpHEqTwoJ :=
  MathExtras.NumberTheory.Analysis.VaalerHNAssembly.derivInterpHEqTwoJ_of_truncationLimit
    (gcEqVaalerJ_exists_of_match h)

#print axioms GC_re
#print axioms gc_eq_vaalerJ_of_match
#print axioms gcEqVaalerJ_vaalerJ_of_match
#print axioms gcEqVaalerJ_exists_of_match
#print axioms gEqReJ_of_match
#print axioms derivInterpHEqTwoJ_of_match

end MathExtras.NumberTheory.Analysis.VaalerTruncationLimit

end
