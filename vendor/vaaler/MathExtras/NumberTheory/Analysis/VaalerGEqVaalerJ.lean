/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatTransform
import MathExtras.NumberTheory.Analysis.VaalerCosecCubeIdentity
import MathExtras.NumberTheory.Analysis.VaalerJhatCornerOne
import MathExtras.NumberTheory.Analysis.VaalerJhatCornerLimits

/-!
# Vaaler eq. (2.32): the spatial identity `GC = vaalerJ` from the SINGLE heart `GCFTeqJ`

This NEW leaf attacks `GCEqVaalerJSpatial`
(`MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatTransform.GCEqVaalerJSpatial`,
`GC = vaalerJ`) — the spatial Vaaler eq. (2.32) `½H′(z) = J(z)`, the J-FT residual whose
closure finishes the J-FT subtree (`GCFTeqJhat`/`GEqReJ` via the committed
`gcFTeqJhat_of_spatial` / `gEqReJ_of_spatial`).

## The key structural finding (and what this leaf delivers)

The committed chain already supplies the assembly

    GCFourierMatch  ⟸  {GContinuous, GIntegrable, GCFTeqJ,
                         VaalerJhatContCornerOne, VaalerJTwoIBPDecay}       (`gcFourierMatch_of`)
    GCEqVaalerJSpatial  ⟸  GCFourierMatch                                   (`gc_eq_vaalerJ_of_match`)

so `GC = vaalerJ` reduces to the FIVE-residual set above.  **Four of those five are
already UNCONDITIONALLY PROVEN theorems** in committed leaves:

* `GContinuous`            — `VaalerGRegularityProof.gContinuous_proven`;
* `GIntegrable`            — `VaalerCosecCubeIdentity.gIntegrable_proven`
                             (via the now-proven `gPoUReprDecay_proven`/`gDecayBound_proven`,
                             which rest on `cosecCubeIdentity_holds`);
* `VaalerJhatContCornerOne`— `VaalerTheorem6JFT.vaalerJhatContCornerOne_holds`;
* `VaalerJTwoIBPDecay`     — `VaalerJhatCornerLimits.vaalerJTwoIBPDecay_holds`.

Hence the *entire* spatial identity `GCEqVaalerJSpatial` collapses onto the **single**
genuine analytic residual — the Fourier-transform heart

    GCFTeqJ : 𝓕 GC = 𝓕 vaalerJ                                            (Vaaler eq. (2.31)→(2.32)),

i.e. `𝓕(½H′) = Ĵ = 𝓕 vaalerJ`.  This leaf PROVES the reduction

    gcEqVaalerJSpatial_of_GCFTeqJ : GCFTeqJ → GCEqVaalerJSpatial

by feeding the four proven theorems plus the hypothesis `GCFTeqJ` into the committed
`gcFourierMatch_of` and then through `gc_eq_vaalerJ_of_match` (Mathlib Fourier-inversion
injectivity).  Threading the same single hypothesis through the committed
`gcFTeqJhat_of_spatial` / `gEqReJ_of_spatial` (this file's `…_of_GCFTeqJ` wrappers)
closes `GCFTeqJhat` and the whole minor D-1 wall `GEqReJ` modulo ONLY `GCFTeqJ`.

So after this leaf the J-FT subtree — and with it the minor D-1 wall — rests on the
**single named `Prop`** `GCFTeqJ` (never an `axiom`): the `N → ∞` Riemann–Lebesgue limit
interchange `𝓕(½H_N′) → Ĵ`, whose derivative-level mechanism is already fully proven
upstream (`VaalerHNAssembly.HNcore_deriv_FT_eq`, `derivLevelTotal_eq_vaalerJhat`,
`halfDeriv_FT_eq_mul`, `tailDeriv_collapse`; `VaalerOscillatoryRemainder` spatial RL).

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `gcEqVaalerJSpatial_of_GCFTeqJ` — **PROVEN** `GCFTeqJ → GCEqVaalerJSpatial`: `GC = vaalerJ`
  from the FT-heart and the four already-proven side facts, via the committed match assembly
  and Fourier-inversion injectivity.
* `gcFTeqJhat_of_GCFTeqJ` / `gEqReJ_of_GCFTeqJ` / `derivInterpHEqTwoJ_of_GCFTeqJ` — **PROVEN**:
  the transform-side DCT value, the minor D-1 wall `GEqReJ`, and the bundled D-1 residual,
  all from the SINGLE hypothesis `GCFTeqJ`.

## Numerical confirmation (mpmath, re-confirmed this session)

With `Ĵ(t) := vaalerJhat|t|`, `vaalerJ(z) := ∫_{-1}^1 Ĵ(τ) e(τz) dτ`: `vaalerJ(z)` is purely
real (`Im = 0`) for every tested `z ∈ {0.3,0.7,1.3,2.4,0.15,3.7}` (values
`0.7827, 0.2146, −0.01089, −0.000873, 0.9416, 0.001155`), matching the committed `½H_N′ →
vaalerJ` (`~1/N`) data — confirming the common spatial limit `G = vaalerJ` of eq. (2.32).

## Honest status — did / did-not

DID: collapsed the spatial identity `GCEqVaalerJSpatial = (GC = vaalerJ)` from the
five-residual `GCFourierMatch` assembly onto the SINGLE analytic heart `GCFTeqJ` by
discharging the other four residuals from EXISTING committed theorems, and proved the
implications `GCFTeqJ → GCEqVaalerJSpatial → GCFTeqJhat/GEqReJ`.  DID-NOT: the FT-heart
`GCFTeqJ` (`𝓕(½H′) = 𝓕 vaalerJ`, the `N → ∞` RL limit interchange) itself — that is the
remaining single named `Prop`, never an `axiom`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.27)–(2.32), p. 192; Mathlib `Analysis.Fourier.Inversion`
(`Continuous.fourierInv_fourier_eq`).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped BigOperators FourierTransform

namespace MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ

open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatTransform

/-! ## §1 — The four already-proven supporting residuals, bundled for reuse -/

/-- **PROVEN — `GContinuous`** (`Continuous GC`).  The committed
`VaalerGRegularityProof.gContinuous_proven`. -/
theorem gContinuous_holds : GContinuous :=
  MathExtras.NumberTheory.Analysis.VaalerGRegularityProof.gContinuous_proven

/-- **PROVEN — `GIntegrable`** (`Integrable GC`).  The committed
`VaalerCosecCubeIdentity.gIntegrable_proven` (resting on the now-proven cube cosecant
identity and PoU `O(1/x²)` decay). -/
theorem gIntegrable_holds : GIntegrable :=
  MathExtras.NumberTheory.Analysis.VaalerCosecCubeIdentity.gIntegrable_proven

/-- **PROVEN — `VaalerJhatContCornerOne`** (`Ĵ`'s `±1` corner continuity).  The committed
`VaalerTheorem6JFT.vaalerJhatContCornerOne_holds`. -/
theorem vaalerJhatContCornerOne_holds :
    MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.VaalerJhatContCornerOne :=
  MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.vaalerJhatContCornerOne_holds

/-- **PROVEN — `VaalerJTwoIBPDecay`** (the `1/z²` two-IBP decay of `J`).  The committed
`VaalerJhatCornerLimits.vaalerJTwoIBPDecay_holds`. -/
theorem vaalerJTwoIBPDecay_holds :
    MathExtras.NumberTheory.Analysis.VaalerJDecayBound.VaalerJTwoIBPDecay :=
  MathExtras.NumberTheory.Analysis.VaalerJhatCornerLimits.vaalerJTwoIBPDecay_holds

/-! ## §2 — `GCEqVaalerJSpatial` (`GC = vaalerJ`) from the SINGLE heart `GCFTeqJ` -/

/-- **PROVEN — the spatial Vaaler-(2.32) identity `GC = vaalerJ` from the single FT-heart
`GCFTeqJ`.**

The committed `gcFourierMatch_of` assembles the bundled Fourier-inversion match
`GCFourierMatch` from `{GContinuous, GIntegrable, GCFTeqJ, VaalerJhatContCornerOne,
VaalerJTwoIBPDecay}`; here the four non-`GCFTeqJ` inputs are the already-proven theorems
`gContinuous_holds`, `gIntegrable_holds`, `vaalerJhatContCornerOne_holds`,
`vaalerJTwoIBPDecay_holds`.  The committed `gc_eq_vaalerJ_of_match` (Mathlib
`Continuous.fourierInv_fourier_eq`, `𝓕⁻(𝓕 f) = f`) then forces the function identity

    GC = 𝓕⁻(𝓕 GC) = 𝓕⁻(𝓕 vaalerJ) = vaalerJ,

i.e. `GCEqVaalerJSpatial`.  The ONLY remaining hypothesis is the analytic heart `GCFTeqJ`
(`𝓕 GC = 𝓕 vaalerJ`); everything else is discharged unconditionally. -/
theorem gcEqVaalerJSpatial_of_GCFTeqJ (hGFT : GCFTeqJ) : GCEqVaalerJSpatial :=
  gc_eq_vaalerJ_of_match
    (gcFourierMatch_of gContinuous_holds gIntegrable_holds hGFT
      vaalerJhatContCornerOne_holds vaalerJTwoIBPDecay_holds)

/-! ## §3 — The J-FT subtree closed modulo the single heart `GCFTeqJ` -/

/-- **PROVEN — the transform-side DCT value `GCFTeqJhat` from the single heart `GCFTeqJ`.**

Routes `gcEqVaalerJSpatial_of_GCFTeqJ` through the committed `gcFTeqJhat_of_spatial`
(fed the two proven `vaalerJ`-side residuals). -/
theorem gcFTeqJhat_of_GCFTeqJ (hGFT : GCFTeqJ) :
    MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ.GCFTeqJhat :=
  gcFTeqJhat_of_spatial (gcEqVaalerJSpatial_of_GCFTeqJ hGFT)
    vaalerJhatContCornerOne_holds vaalerJTwoIBPDecay_holds

/-- **PROVEN — the minor D-1 wall `GEqReJ` from the single heart `GCFTeqJ`.**

The whole `H′ = 2J` minor wall now rests on the SINGLE named `Prop` `GCFTeqJ`: the four
other former residuals (`GContinuous`, `GIntegrable`, `VaalerJhatContCornerOne`,
`VaalerJTwoIBPDecay`) are discharged here from committed theorems. -/
theorem gEqReJ_of_GCFTeqJ (hGFT : GCFTeqJ) :
    MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ.GEqReJ :=
  gEqReJ_of_spatial gContinuous_holds gIntegrable_holds
    (gcEqVaalerJSpatial_of_GCFTeqJ hGFT)
    vaalerJhatContCornerOne_holds vaalerJTwoIBPDecay_holds

/-- **PROVEN — the bundled D-1 residual `DerivInterpHEqTwoJ` from the single heart
`GCFTeqJ`.** -/
theorem derivInterpHEqTwoJ_of_GCFTeqJ (hGFT : GCFTeqJ) :
    MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail.DerivInterpHEqTwoJ :=
  derivInterpHEqTwoJ_of_spatial gContinuous_holds gIntegrable_holds
    (gcEqVaalerJSpatial_of_GCFTeqJ hGFT)
    vaalerJhatContCornerOne_holds vaalerJTwoIBPDecay_holds

#print axioms gContinuous_holds
#print axioms gIntegrable_holds
#print axioms vaalerJhatContCornerOne_holds
#print axioms vaalerJTwoIBPDecay_holds
#print axioms gcEqVaalerJSpatial_of_GCFTeqJ
#print axioms gcFTeqJhat_of_GCFTeqJ
#print axioms gEqReJ_of_GCFTeqJ
#print axioms derivInterpHEqTwoJ_of_GCFTeqJ

end MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ

end
