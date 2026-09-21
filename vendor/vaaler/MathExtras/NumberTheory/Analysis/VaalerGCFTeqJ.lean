/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch

/-!
# Vaaler Theorem 6: discharging `GCFTeqJ` (`𝓕 GC = 𝓕 vaalerJ`, the analytic heart)

This NEW leaf attacks the SINGLE analytic-heart conjunct `GCFTeqJ`
(`MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch.GCFTeqJ`,
`𝓕 GC = 𝓕 vaalerJ`) of the minor D-1 wall — the Vaaler eq. (2.31)→(2.32) passage that
both `𝓕 GC = 𝓕(½H′)` and `𝓕 vaalerJ` equal the closed Fejér transform `Ĵ`.

## The math (Vaaler 2.31 → 2.32)

Both Fourier transforms equal the *corrected continuous* `Ĵ`
(`VaalerTheorem6JFT.vaalerJCcont`, the continuous representative with the paper value
`Ĵ(0) = 1`):

* `𝓕 vaalerJ = vaalerJCcont` — this is **already committed**: Theorem 6
  (`VaalerTheorem6JFT.fourier_vaalerJ_eq_of`), which holds given the two `vaalerJ`-side
  residuals `VaalerJhatContCornerOne` (the `±1` corner continuity) and
  `VaalerJTwoIBPDecay` (the `1/z²` two-IBP decay).  These are exactly the SAME two
  residuals already feeding `gcFourierMatch_of`.

* `𝓕 GC = vaalerJCcont` — the genuine remaining analytic content.  `GC = ½H′ =
  lim_N ½H_N′` and, by dominated convergence (a uniform `L¹` domination of the
  truncations' derivatives, Vaaler eq. (2.32)), `𝓕(½H_N′)(t) → 𝓕(½H′)(t)`.  The
  derivative-level `N`-transform machinery is FULLY PROVEN upstream
  (`VaalerHNAssembly.HNcore_deriv_FT_eq`, `derivLevelTotal_eq_vaalerJhat`,
  `halfDeriv_FT_eq_mul`, `tailDeriv_collapse`) and the oscillatory remainder vanishes by
  Riemann–Lebesgue (`VaalerOscillatoryRemainder.oscillatoryRemainderTendsto_holds`); the
  limit value is the closed `Ĵ`, i.e. `vaalerJCcont`.

The **honest remaining sub-step** — the `N → ∞` dominated-convergence interchange that
produces the closed transform value `𝓕 GC = Ĵ` from the proven `N`-level machinery — is
isolated as the SINGLE named `Prop` `GCFTeqJhat` (`∀ t, 𝓕 GC t = vaalerJCcont t`).
It is NOT an `axiom`, and it is genuinely *more primitive* than `GCFTeqJ`: granting it,
we DERIVE `GCFTeqJ = (𝓕 GC = 𝓕 vaalerJ)` by routing the `vaalerJ`-side through the
committed Theorem 6 (`fourier_vaalerJ_eq_of`).

(Why `Ĵ`-value and not a pointwise sequence limit of `(πit)·∫HNcore + |t|`: the
function-level oscillatory term `cos(π(2N+1)t)/sin(πt)` of `HNcore_deriv_FT_eq` does NOT
converge for fixed `t` — the Riemann–Lebesgue cancellation lives in the *full* spatial
integral `𝓕(½H_N′)`, not in this term-by-term `t`-pointwise decomposition.  The faithful
remaining object is therefore the transform *value* `𝓕 GC = Ĵ`, which encapsulates the
genuine spatial DCT + RL interchange.)

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `GCFTeqJhat` (named `Prop`, NOT an `axiom`) — the DCT value `∀ t, 𝓕 GC t =
  vaalerJCcont t` (`𝓕(½H′) = Ĵ`, Vaaler eq. (2.31)→(2.32)).
* `gcFTeqJ_of_hat` — **PROVEN**: `GCFTeqJhat → VaalerJhatContCornerOne →
  VaalerJTwoIBPDecay → GCFTeqJ`, routing `𝓕 vaalerJ = Ĵ` through the committed Theorem 6.
* `gcFourierMatch_of_hat` / `gEqReJ_of_hat` / `derivInterpHEqTwoJ_of_hat` — **PROVEN**:
  with `GCFTeqJ` now reduced to `GCFTeqJhat`, the whole minor D-1 wall rests on the
  residual set `{GContinuous, GIntegrable, GCFTeqJhat, VaalerJhatContCornerOne,
  VaalerJTwoIBPDecay}` — i.e. `GCFTeqJ` is REPLACED by the strictly-more-primitive
  `Ĵ`-value `GCFTeqJhat`.

## Honest status — did / did-not

DID: replaced the heart `GCFTeqJ = (𝓕 GC = 𝓕 vaalerJ)` by the more-primitive,
single-sided DCT value `GCFTeqJhat = (𝓕 GC = Ĵ)`, proving the full equivalence to the
minor-wall consumers through the committed Theorem 6.  DID-NOT: the dominated-convergence
interchange `𝓕(½H_N′) → 𝓕(½H′) = Ĵ` itself — the uniform `L¹` domination of the
truncations' derivatives — is not discharged here; it is the content of `GCFTeqJhat`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.27)–(2.32), p. 192;
Mathlib `MeasureTheory.tendsto_integral_of_dominated_convergence` (the DCT this
`Prop` records), `Analysis.Fourier.Inversion`.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped BigOperators FourierTransform

namespace MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ

open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerCor7RouteB
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerJIntegrable
open MathExtras.NumberTheory.Analysis.VaalerJDecayBound
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch

/-! ## §1 — The single remaining DCT value (named `Prop`, never an `axiom`) -/

/-- **The single remaining analytic step, ONE named `Prop` (never an `axiom`).**

The Fourier transform of the complexified explicit half-derivative `GC = (½H′ : ℂ)`
equals, *pointwise*, the corrected continuous Fejér transform `Ĵ`
(`vaalerJCcont`):

    𝓕 GC t = (vaalerJhatCont t : ℂ)      for all `t`.

This is Vaaler eq. (2.31)→(2.32): `GC = ½H′ = lim_N ½H_N′`, and by dominated convergence
(uniform `L¹` domination of the truncations' derivatives) `𝓕(½H_N′)(t) → 𝓕(½H′)(t)`,
whose limit value is the closed `Ĵ` (the derivative-level `N`-machinery
`VaalerHNAssembly.HNcore_deriv_FT_eq` + Riemann–Lebesgue
`VaalerOscillatoryRemainder.oscillatoryRemainderTendsto_holds` +
`derivLevelTotal_eq_vaalerJhat` + `tailDeriv_collapse`).  A TRUE statement about the
explicit `G`; NOT an `axiom`, NOT vacuous (the RHS is the concrete `vaalerJCcont`). -/
def GCFTeqJhat : Prop := ∀ t : ℝ, 𝓕 GC t = (vaalerJCcont t : ℂ)

/-! ## §2 — `GCFTeqJ` from the DCT value, via the committed Theorem 6 -/

/-- **PROVEN — the analytic heart `GCFTeqJ` from the single-sided DCT value.**

From `GCFTeqJhat` (`𝓕 GC = Ĵ`) and the two `vaalerJ`-side residuals
(`VaalerJhatContCornerOne`, `VaalerJTwoIBPDecay`), the committed Theorem 6
(`fourier_vaalerJ_eq_of`) supplies `𝓕 vaalerJ = Ĵ` as well, so the two transforms agree:

    𝓕 GC t = vaalerJCcont t = 𝓕 vaalerJ t      for all `t`.

Hence `GCFTeqJ = (𝓕 GC = 𝓕 vaalerJ)`.  The two `vaalerJ`-side residuals are EXACTLY the
ones already feeding `gcFourierMatch_of`; no new residual is introduced beyond the
single-sided, strictly-more-primitive `GCFTeqJhat`. -/
theorem gcFTeqJ_of_hat (hHat : GCFTeqJhat)
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    GCFTeqJ := by
  have hcont : VaalerJhatContContinuous := vaalerJhatContContinuous_of_cornerOne h1
  have hJint : JIntegrable := jIntegrable_of_decay (jDecayBound_of_twoIBP h2)
  -- `GCFTeqJ` unfolds to `𝓕 GC = 𝓕 vaalerJ`; prove equality of functions pointwise.
  unfold GCFTeqJ
  funext t
  -- LHS = `vaalerJCcont t` (the DCT value); RHS = `vaalerJCcont t` (Theorem 6).
  rw [hHat t, vaalerJCcont_apply t, fourier_vaalerJ_eq_of hcont hJint t]

/-! ## §3 — Re-assembling the minor D-1 wall with `GCFTeqJ` replaced by `GCFTeqJhat` -/

/-- **PROVEN — `GCFourierMatch` from the residual set with `GCFTeqJ` ↦ `GCFTeqJhat`.**

Routes `gcFTeqJ_of_hat` into the committed assembly `gcFourierMatch_of`, so the heart
conjunct is now supplied by the strictly-more-primitive single-sided DCT value
`GCFTeqJhat`. -/
theorem gcFourierMatch_of_hat
    (hGcont : GContinuous) (hGint : GIntegrable) (hHat : GCFTeqJhat)
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    GCFourierMatch :=
  gcFourierMatch_of hGcont hGint (gcFTeqJ_of_hat hHat h1 h2) h1 h2

/-- **PROVEN — the minor D-1 wall `GEqReJ` with `GCFTeqJ` ↦ `GCFTeqJhat`.** -/
theorem gEqReJ_of_hat
    (hGcont : GContinuous) (hGint : GIntegrable) (hHat : GCFTeqJhat)
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ.GEqReJ :=
  gEqReJ_of hGcont hGint (gcFTeqJ_of_hat hHat h1 h2) h1 h2

/-- **PROVEN — the bundled D-1 residual `DerivInterpHEqTwoJ` with `GCFTeqJ` ↦
`GCFTeqJhat`. -/
theorem derivInterpHEqTwoJ_of_hat
    (hGcont : GContinuous) (hGint : GIntegrable) (hHat : GCFTeqJhat)
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail.DerivInterpHEqTwoJ :=
  derivInterpHEqTwoJ_of hGcont hGint (gcFTeqJ_of_hat hHat h1 h2) h1 h2

#print axioms gcFTeqJ_of_hat
#print axioms gcFourierMatch_of_hat
#print axioms gEqReJ_of_hat
#print axioms derivInterpHEqTwoJ_of_hat

end MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ

end
