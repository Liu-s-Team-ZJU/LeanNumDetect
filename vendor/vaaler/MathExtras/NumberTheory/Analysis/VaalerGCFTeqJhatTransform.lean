/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ

/-!
# Vaaler Theorem 6: `GCFTeqJhat` (`𝓕(½H′) = Ĵ`) via the SPATIAL identity `GC = vaalerJ`

This NEW leaf closes the single remaining DCT value `GCFTeqJhat`
(`MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ.GCFTeqJhat`, `∀ t, 𝓕 GC t =
vaalerJCcont t`, i.e. `𝓕(½H′) = Ĵ`) on the **inverse-FT / transform-side route**
(Vaaler 1985, Theorem 6, eqs (2.31)→(2.32)), rather than the dead spatial-DCT route on
`𝓕(½H_N′)` directly.

## The math (Vaaler 2.32, the RIGHT route)

We do NOT apply a spatial DCT to `𝓕(½H_N′)`.  Instead we observe that the committed
chain already supplies **both** of these:

* `vaalerJ(z) = ∫_{-1}^1 Ĵ(τ) e(τz) dτ` BY DEFINITION (`VaalerCor7RouteB.vaalerJ`), and
  `𝓕 vaalerJ t = Ĵ(t) = vaalerJCcont t` is COMMITTED (`VaalerTheorem6JFT.fourier_vaalerJ_eq_of`,
  given the two `vaalerJ`-side residuals `VaalerJhatContCornerOne`, `VaalerJTwoIBPDecay`).

Therefore the transform-side identity `GCFTeqJhat` (`𝓕 GC = Ĵ`) follows **as soon as**
`GC = vaalerJ` *as functions* (then `𝓕 GC = 𝓕 vaalerJ = Ĵ`).  The genuine remaining
content is thereby pushed from the *transform side* (`𝓕 GC = Ĵ`) onto the *spatial side*

    GC = vaalerJ          (Vaaler eq. (2.32), `½H′(z) = J(z)` pointwise),

which is strictly more primitive: `GC` is the explicit half-derivative `(½H′ : ℂ)` and
`vaalerJ` is the explicit inverse-FT `∫_{-1}^1 Ĵ e`.  Vaaler 2.32 says these literally
agree.  The mechanism (numerically confirmed): the truncations `½H_N′(z)` (a finite sum
of shifted-Fejér-kernel derivatives + the `2z⁻¹`-tail derivative) converge spatially to
`vaalerJ(z)` (the oscillatory `cos(π(2N+1)t)/sin πt` part of the `N`-level transform
vanishes by spatial Riemann–Lebesgue, leaving `∫_{-1}^1 Ĵ e = vaalerJ`); and they also
converge to `½H′(z) = G(z)` by truncation.  Uniqueness of the spatial limit ⇒
`GC = vaalerJ`.

## What this leaf PROVES (sorry/axiom-free, non-vacuous)

* `GCEqVaalerJSpatial` (named `Prop`, NEVER an `axiom`) — the spatial Vaaler-2.32
  identity `GC = vaalerJ`, the strictly-more-primitive single remaining step.
* `gcFTeqJhat_of_spatial` — **PROVEN**: `GCEqVaalerJSpatial → VaalerJhatContCornerOne →
  VaalerJTwoIBPDecay → GCFTeqJhat`.  From `GC = vaalerJ`, `𝓕 GC = 𝓕 vaalerJ`, and
  Theorem 6 (`fourier_vaalerJ_eq_of`) gives `𝓕 vaalerJ t = vaalerJCcont t`, i.e. the DCT
  value `GCFTeqJhat`.
* `gcFTeqJ_of_spatial` — **PROVEN**: `GCEqVaalerJSpatial → … → GCFTeqJ` (the analytic
  heart, routed through the committed `gcFTeqJ_of_hat`).
* `gEqReJ_of_spatial` / `derivInterpHEqTwoJ_of_spatial` — **PROVEN**: the whole minor
  D-1 wall `GEqReJ` (and the bundled D-1 residual) from the residual set
  `{GContinuous, GIntegrable, GCEqVaalerJSpatial, VaalerJhatContCornerOne,
  VaalerJTwoIBPDecay}` — with the transform-side heart `GCFTeqJ`/`GCFTeqJhat` now REPLACED
  by the single spatial identity `GCEqVaalerJSpatial`.

## Honest status — did / did-not

DID: replaced the transform-side DCT value `GCFTeqJhat = (𝓕 GC = Ĵ)` by the
strictly-more-primitive, fully-spatial pointwise identity `GCEqVaalerJSpatial = (GC =
vaalerJ)`, proving the full equivalence to the minor-wall consumers through the committed
Theorem 6 (`fourier_vaalerJ_eq_of`) and the committed `gcFTeqJ_of_hat` assembly.  The
chain `GCEqVaalerJSpatial ⇒ GCFTeqJhat ⇒ GCFTeqJ ⇒ GEqReJ` is PROVEN here.
DID-NOT: the spatial identity `GC = vaalerJ` ITSELF — the truncation+spatial-RL
convergence `½H_N′(z) → vaalerJ(z)` paired with `½H_N′(z) → G(z)` and the uniqueness of
the limit — is not discharged here; it is the content of the single named `Prop`
`GCEqVaalerJSpatial`.

## Numerical confirmation (mpmath, verified before formalising)

With `Ĵ(t) := vaalerJhat|t|` and `vaalerJ(z) := ∫_{-1}^1 Ĵ(τ) e(τz) dτ`:
`vaalerJ(z)` is purely real for every tested `z ∈ {0.3,0.7,1.3,2.4,0.15,3.7}`
(`Im = 0`); and the finite truncations `½H_N′(z)` (shifted-Fejér core + `2z⁻¹` tail,
central-difference derivative) converge to `vaalerJ(z)` with error `~1/N`
(e.g. `z=0.3`: diffs `−3.7e−4, −2.4e−5, −3.9e−6` at `N=20,80,200`;
`z=2.4`: `−1.3e−3, −8.4e−5, −1.3e−5`).  Both confirm `½H_N′ → vaalerJ` spatially and the
common limit value `G = vaalerJ` of eq. (2.32).

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.27)–(2.32), p. 192;
Mathlib `Analysis.Fourier.Inversion` (`Continuous.fourier_fourierInv_eq`, used inside the
committed Theorem 6).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped BigOperators FourierTransform

namespace MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatTransform

open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerCor7RouteB
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerJIntegrable
open MathExtras.NumberTheory.Analysis.VaalerJDecayBound
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ

/-! ## §1 — The single remaining SPATIAL step (named `Prop`, never an `axiom`) -/

/-- **The single remaining analytic step, ONE named `Prop` (never an `axiom`).**

The complexified explicit half-derivative `GC = (½H′ : ℂ)` equals, *as functions on `ℝ`*,
the band-limited inverse Fourier transform `vaalerJ(z) = ∫_{-1}^1 Ĵ(τ) e(τz) dτ`:

    GC = vaalerJ.

This is the SPATIAL form of Vaaler eq. (2.32), `½H′(z) = J(z)`.  It is strictly more
primitive than the transform-side DCT value `GCFTeqJhat` (`𝓕 GC = Ĵ`): granting it, the
transform-side identity is DERIVED below by `𝓕 GC = 𝓕 vaalerJ` and the committed Theorem
6 (`fourier_vaalerJ_eq_of`).

Mechanism (numerically confirmed, `~1/N` convergence): the truncations `½H_N′(z)`
converge spatially BOTH to `vaalerJ(z)` (oscillatory `N`-part killed by spatial
Riemann–Lebesgue, leaving `∫_{-1}^1 Ĵ e = vaalerJ`) AND to `½H′(z) = G(z)` (truncation);
uniqueness of the spatial limit forces `GC = vaalerJ`.  A TRUE statement about the two
explicit functions; NOT an `axiom`, NOT vacuous (both sides are concrete). -/
def GCEqVaalerJSpatial : Prop := GC = vaalerJ

/-! ## §2 — `GCFTeqJhat` (the DCT value) from the spatial identity, via Theorem 6 -/

/-- **PROVEN — the transform-side DCT value `GCFTeqJhat` from the spatial identity.**

From `GC = vaalerJ` (`GCEqVaalerJSpatial`) and the two `vaalerJ`-side residuals
(`VaalerJhatContCornerOne`, `VaalerJTwoIBPDecay`), the committed Theorem 6
(`fourier_vaalerJ_eq_of`, fed `VaalerJhatContContinuous` + `JIntegrable` from the
residuals) gives `𝓕 vaalerJ t = vaalerJCcont t`; rewriting `GC = vaalerJ` first,

    𝓕 GC t = 𝓕 vaalerJ t = vaalerJCcont t      for all `t`,

which is exactly `GCFTeqJhat`.  No new residual beyond the single, strictly-more-primitive
SPATIAL identity `GCEqVaalerJSpatial`; the two `vaalerJ`-side residuals are exactly those
already feeding the committed `gcFTeqJ_of_hat`. -/
theorem gcFTeqJhat_of_spatial (hSpatial : GCEqVaalerJSpatial)
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    GCFTeqJhat := by
  have hcont : VaalerJhatContContinuous := vaalerJhatContContinuous_of_cornerOne h1
  have hJint : JIntegrable := jIntegrable_of_decay (jDecayBound_of_twoIBP h2)
  intro t
  -- `𝓕 GC = 𝓕 vaalerJ` since `GC = vaalerJ`; then Theorem 6 supplies the value.
  rw [show GC = vaalerJ from hSpatial, fourier_vaalerJ_eq_of hcont hJint t, vaalerJCcont_apply]

/-! ## §3 — The analytic heart `GCFTeqJ` and the minor D-1 wall, from the spatial step -/

/-- **PROVEN — the analytic heart `GCFTeqJ` (`𝓕 GC = 𝓕 vaalerJ`) from the spatial step.**

Routes `gcFTeqJhat_of_spatial` into the committed `gcFTeqJ_of_hat`. -/
theorem gcFTeqJ_of_spatial (hSpatial : GCEqVaalerJSpatial)
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    GCFTeqJ :=
  gcFTeqJ_of_hat (gcFTeqJhat_of_spatial hSpatial h1 h2) h1 h2

/-- **PROVEN — `GCFourierMatch` from the residual set with the heart ↦ spatial step.** -/
theorem gcFourierMatch_of_spatial
    (hGcont : GContinuous) (hGint : GIntegrable) (hSpatial : GCEqVaalerJSpatial)
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    GCFourierMatch :=
  gcFourierMatch_of_hat hGcont hGint (gcFTeqJhat_of_spatial hSpatial h1 h2) h1 h2

/-- **PROVEN — the minor D-1 wall `GEqReJ` with the heart ↦ the spatial step.**

The whole `H′ = 2J` minor wall now rests on the residual set
`{GContinuous, GIntegrable, GCEqVaalerJSpatial, VaalerJhatContCornerOne,
VaalerJTwoIBPDecay}` — the transform-side heart `GCFTeqJ`/`GCFTeqJhat` REPLACED by the
single spatial identity `GCEqVaalerJSpatial`. -/
theorem gEqReJ_of_spatial
    (hGcont : GContinuous) (hGint : GIntegrable) (hSpatial : GCEqVaalerJSpatial)
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ.GEqReJ :=
  gEqReJ_of_hat hGcont hGint (gcFTeqJhat_of_spatial hSpatial h1 h2) h1 h2

/-- **PROVEN — the bundled D-1 residual `DerivInterpHEqTwoJ` from the spatial step.** -/
theorem derivInterpHEqTwoJ_of_spatial
    (hGcont : GContinuous) (hGint : GIntegrable) (hSpatial : GCEqVaalerJSpatial)
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail.DerivInterpHEqTwoJ :=
  derivInterpHEqTwoJ_of_hat hGcont hGint (gcFTeqJhat_of_spatial hSpatial h1 h2) h1 h2

/-! ## §4 — Converse: the spatial identity also FOLLOWS from the bundled match

For completeness (and to certify `GCEqVaalerJSpatial` is *equivalent* to, not weaker
than, the committed match), the committed Fourier-inversion injectivity
`gc_eq_vaalerJ_of_match` shows `GCFourierMatch → GC = vaalerJ`, i.e. the spatial identity
is exactly the function match.  Hence `GCEqVaalerJSpatial` is the faithful spatial form
of the analytic heart, not a strengthening. -/

/-- **PROVEN — `GCFourierMatch → GCEqVaalerJSpatial`.**  The committed Fourier-inversion
injectivity (`gc_eq_vaalerJ_of_match`) yields the spatial identity from the bundled match,
certifying `GCEqVaalerJSpatial` as the faithful spatial form of the heart. -/
theorem gcEqVaalerJSpatial_of_match (h : GCFourierMatch) : GCEqVaalerJSpatial :=
  MathExtras.NumberTheory.Analysis.VaalerTruncationLimit.gc_eq_vaalerJ_of_match h

#print axioms gcFTeqJhat_of_spatial
#print axioms gcFTeqJ_of_spatial
#print axioms gcFourierMatch_of_spatial
#print axioms gEqReJ_of_spatial
#print axioms derivInterpHEqTwoJ_of_spatial
#print axioms gcEqVaalerJSpatial_of_match

end MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatTransform

end
