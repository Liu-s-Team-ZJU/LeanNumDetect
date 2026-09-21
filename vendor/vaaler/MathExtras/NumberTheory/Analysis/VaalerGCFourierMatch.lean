/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
import MathExtras.NumberTheory.Analysis.VaalerJDecayBound
import MathExtras.NumberTheory.Analysis.VaalerJIntegrable

/-!
# Vaaler Theorem 6: discharging `GCFourierMatch` (the LAST minor analytic residual)

This NEW leaf attacks the SINGLE bundled residual `GCFourierMatch`
(`VaalerTruncationLimit`) — the Fourier-transform match
`𝓕 GC = 𝓕 vaalerJ` together with the Fourier-inversion regularity of both
`GC = (G : ℂ) = (½H′ : ℂ)` and `vaalerJ` — which is the last analytic step between the
proven `H_N` backbone and the entire `H′ = 2J` minor wall `GEqReJ`.

## The structure of `GCFourierMatch` and what we reduce it to

`GCFourierMatch` bundles SEVEN conjuncts:

* `contGC : Continuous GC`, `intGC : Integrable GC`, `intFTGC : Integrable (𝓕 GC)`;
* `contJ : Continuous vaalerJ`, `intJ : Integrable vaalerJ`, `intFTJ : Integrable (𝓕 vaalerJ)`;
* `ftEq : 𝓕 GC = 𝓕 vaalerJ` (the analytic heart).

We **fully reduce the entire `vaalerJ`-side** (`contJ`, `intJ`, `intFTJ`) and the
`GC`-side `intFTGC` to ALREADY-COMMITTED named residuals plus the heart `ftEq`:

* `contJ` ⟸ `VaalerTheorem6JFT.VaalerJhatContCornerOne` (the `±1` corner continuity of
  `Ĵ`):  `vaalerJ = 𝓕 vaalerJCcont` (`VaalerJIntegrable.fourier_vaalerJCcont_eq_vaalerJ`)
  is the Fourier integral of the `L¹` (continuous + compact support) `vaalerJCcont`,
  hence continuous (`VectorFourier.fourierIntegral_continuous`).
* `intJ` ⟸ `VaalerJDecayBound.VaalerJTwoIBPDecay` (the `1/z²` two-IBP decay):
  `VaalerJIntegrable.vaalerJ_integrable_of_decay (jDecayBound_of_twoIBP …)`.
* `intFTJ` ⟸ corner: `𝓕 vaalerJ = vaalerJCcont` (Theorem 6,
  `VaalerTheorem6JFT.fourier_vaalerJ_eq_of`), continuous with compact support ⇒ `L¹`.
* `intFTGC` ⟸ `ftEq`: `𝓕 GC = 𝓕 vaalerJ`, and the RHS is `L¹` (just shown).

So `GCFourierMatch` is assembled from EXACTLY THREE genuinely-new analytic facts about
the explicit half-derivative `G = ½H′`, isolated as correctly-stated named `Prop`s
(never `axiom`s), plus the two already-existing `vaalerJ`-side residuals:

* `GContinuous : Continuous GC` — `G = ½H′` is continuous (the apparent poles of the
  cube-tail series at the integers are *removable*: the `(sin πx/π)²` prefactor and the
  derivative structure cancel them; numerically `G` is continuous and `→ 0` at integers).
* `GIntegrable : Integrable GC` — `G(x) = O((1+x²)⁻¹)` (Vaaler eq. (2.27)/(2.32):
  `½H′ = J`, which has the band-limited `1/x²` decay), hence `∈ L¹`.  Mirrors the
  `vaalerJ` side `VaalerJTwoIBPDecay`.
* `GCFTeqJ : 𝓕 GC = 𝓕 vaalerJ` — the analytic heart, Vaaler eq. (2.31)→(2.32):
  `𝓕(½H′) = limₙ 𝓕(½Hₙ′) = (1−|t|)₊ πt cotC t + |t| = Ĵ = 𝓕 vaalerJ`, the
  derivative-level `N`-transform `HNcore_deriv_FT_eq` + Riemann–Lebesgue
  (`VaalerOscillatoryRemainder`) + the proven `fourier_vaalerJ_eq_of`.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `vaalerJ_continuous_of_corner` — **PROVEN** `VaalerJhatContCornerOne → Continuous vaalerJ`.
* `vaalerJ_integrable_of_twoIBP` — **PROVEN** `VaalerJTwoIBPDecay → Integrable vaalerJ`.
* `fourierVaalerJ_integrable_of` — **PROVEN** `VaalerJhatContCornerOne → VaalerJTwoIBPDecay
  → Integrable (𝓕 vaalerJ)` (Theorem 6 + compact support).
* `gcFourierMatch_of` — **PROVEN** assembly: from the three `G`-side `Prop`s and the two
  `vaalerJ`-side residuals, `GCFourierMatch` holds.
* `gEqReJ_of` / `derivInterpHEqTwoJ_of` — **PROVEN** the minor D-1 wall `GEqReJ` (and the
  bundled D-1 residual) from the SAME five inputs, via the committed `gEqReJ_of_match`.

## Honest status

The whole minor D-1 wall now rests on the *minimal* residual set
`{GContinuous, GIntegrable, GCFTeqJ, VaalerJhatContCornerOne, VaalerJTwoIBPDecay}` —
three genuinely-new analytic facts about the explicit `G = ½H′` and the two pre-existing
`Ĵ`-corner/`J`-decay residuals.  EVERYTHING ELSE — the entire `vaalerJ`-side regularity,
the `𝓕 GC` integrability, and the wiring to `GEqReJ` — is FULLY PROVEN here on top of
Mathlib (`VectorFourier.fourierIntegral_continuous`, `Continuous.fourierInv_fourier_eq`)
and the committed leaves.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.27)–(2.32), p. 192.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped BigOperators FourierTransform RealInnerProductSpace

namespace MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch

open MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ
open MathExtras.NumberTheory.Analysis.VaalerCor7RouteB
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerJIntegrable
open MathExtras.NumberTheory.Analysis.VaalerJDecayBound
open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit

/-! ## §1 — A reusable continuity helper for the Fourier integral of an `L¹` function -/

/-- **PROVEN helper.**  The Fourier transform `𝓕 f` of an integrable `f : ℝ → ℂ` is
continuous.  This is Mathlib's `VectorFourier.fourierIntegral_continuous` specialised to
the real-line instance `𝓕 f = VectorFourier.fourierIntegral 𝐞 volume (innerSL ℝ) f`. -/
theorem fourier_continuous_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

/-! ## §2 — The `vaalerJ`-side regularity, reduced to the committed residuals -/

/-- **PROVEN.**  `VaalerJhatContCornerOne → Continuous vaalerJ`.

`vaalerJ = 𝓕 vaalerJCcont` (`fourier_vaalerJCcont_eq_vaalerJ`), and `vaalerJCcont` is the
continuous (given the `±1` corner residual `VaalerJhatContCornerOne`), compactly-supported
`Ĵ`, hence `L¹` (`vaalerJCcont_integrable_of_continuous`).  The Fourier integral of an
`L¹` function is continuous (`fourier_continuous_of_integrable`). -/
theorem vaalerJ_continuous_of_corner (h1 : VaalerJhatContCornerOne) :
    Continuous vaalerJ := by
  have hcont : Continuous vaalerJCcont := vaalerJCcont_continuous_of_cornerOne h1
  have hint : Integrable vaalerJCcont := vaalerJCcont_integrable_of_continuous hcont
  have : Continuous (𝓕 vaalerJCcont) := fourier_continuous_of_integrable hint
  rwa [fourier_vaalerJCcont_eq_vaalerJ] at this

/-- **PROVEN.**  `VaalerJTwoIBPDecay → Integrable vaalerJ` (the `1/z²` two-IBP decay of
the band-limited `J`, via the committed `jDecayBound_of_twoIBP` and
`vaalerJ_integrable_of_decay`). -/
theorem vaalerJ_integrable_of_twoIBP (h : VaalerJTwoIBPDecay) : Integrable vaalerJ :=
  vaalerJ_integrable_of_decay (jDecayBound_of_twoIBP h)

/-- **PROVEN.**  `VaalerJhatContCornerOne → VaalerJTwoIBPDecay → Integrable (𝓕 vaalerJ)`.

By Theorem 6 (`fourier_vaalerJ_eq_of`, which consumes the corner-continuity residual and
`JIntegrable`, here supplied through `jIntegrable_of_decay (jDecayBound_of_twoIBP …)`),
`𝓕 vaalerJ = vaalerJCcont` pointwise; `vaalerJCcont` is continuous (corner) with compact
support, hence `L¹` (`vaalerJCcont_integrable_of_continuous`).  Transport the integrability
across the pointwise identity. -/
theorem fourierVaalerJ_integrable_of
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    Integrable (𝓕 vaalerJ) := by
  have hcont : VaalerJhatContContinuous := vaalerJhatContContinuous_of_cornerOne h1
  have hJint : JIntegrable := jIntegrable_of_decay (jDecayBound_of_twoIBP h2)
  -- 𝓕 vaalerJ t = vaalerJCcont t for all t (Theorem 6)
  have hFT : ∀ t : ℝ, 𝓕 vaalerJ t = vaalerJCcont t := by
    intro t
    rw [fourier_vaalerJ_eq_of hcont hJint t, vaalerJCcont_apply]
  have hfun : 𝓕 vaalerJ = vaalerJCcont := funext hFT
  rw [hfun]
  exact vaalerJCcont_integrable_of_continuous hcont

/-! ## §3 — The three genuinely-new analytic `Prop`s about `G = ½H′` (NOT axioms) -/

/-- **Residual 1 (continuity of `½H′`).**  `GC = (G : ℂ)` is continuous on `ℝ`.

`G = ½H′` is the explicit half-derivative (`VaalerHPrimeEqTwoJ.G`).  Off ℤ it is the
proven closed-form derivative (`hasDerivAt_interpH`, so in particular continuous there);
at the integers the apparent poles of the cube-tail series are *removable* — the
`(sin πx/π)²` prefactor vanishes to second order and the derivative structure cancels the
singularity, so `G` extends continuously (numerically `G → 0` at the integers, matching
the band-limited `Re J`).  A TRUE statement about the explicit `G`; NOT an `axiom`,
NOT vacuous. -/
def GContinuous : Prop := Continuous GC

/-- **Residual 2 (`O((1+x²)⁻¹)` decay / integrability of `½H′`).**  `GC = (G : ℂ) ∈ L¹(ℝ)`.

By Vaaler eq. (2.27)/(2.32), `½H′ = J` is band-limited with `J(x) = O((1+|x|)⁻²)`, so
`G ∈ L¹`.  Mirrors the `vaalerJ`-side decay `VaalerJTwoIBPDecay`.  A TRUE statement about
the explicit `G`; NOT an `axiom`, NOT vacuous. -/
def GIntegrable : Prop := Integrable GC

/-- **Residual 3 (the analytic heart, Vaaler eq. (2.31)→(2.32)).**  `𝓕 GC = 𝓕 vaalerJ`.

Both equal `Ĵ`:  `𝓕 GC = 𝓕(½H′) = limₙ 𝓕(½Hₙ′)` (dominated convergence) `= limₙ
(1−|t|)₊·(πt cotC t + osc_N)` (`VaalerHNAssembly.HNcore_deriv_FT_eq`) `= (1−|t|)₊ πt cotC t
+ |t| = Ĵ` (Riemann–Lebesgue kills `osc_N`, `VaalerOscillatoryRemainder`; the `+|t|` from
the `2z⁻¹` tail, `tailDeriv_collapse`; closed `derivLevelTotal_eq_vaalerJhat`), and
`𝓕 vaalerJ = Ĵ` (`fourier_vaalerJ_eq_of`, Theorem 6).  A TRUE statement; NOT an `axiom`. -/
def GCFTeqJ : Prop := 𝓕 GC = 𝓕 vaalerJ

/-! ## §4 — The assembly of `GCFourierMatch` from the minimal residual set -/

/-- **PROVEN — `GCFourierMatch` from the minimal residual set.**

From the three genuinely-new analytic facts about `G = ½H′`
(`GContinuous`, `GIntegrable`, `GCFTeqJ`) together with the two pre-existing
`vaalerJ`-side residuals (`VaalerJhatContCornerOne`, `VaalerJTwoIBPDecay`), all SEVEN
conjuncts of `GCFourierMatch` are supplied:

* `contGC`/`intGC` are the `G`-side `Prop`s `GContinuous`/`GIntegrable`;
* `contJ`/`intJ`/`intFTJ` are PROVEN from the `vaalerJ`-side residuals here;
* `intFTGC = Integrable (𝓕 GC)` is `Integrable (𝓕 vaalerJ)` rewritten through `GCFTeqJ`;
* `ftEq` is `GCFTeqJ`. -/
theorem gcFourierMatch_of
    (hGcont : GContinuous) (hGint : GIntegrable) (hGFT : GCFTeqJ)
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    GCFourierMatch where
  contGC := hGcont
  intGC := hGint
  intFTGC := by rw [show (𝓕 GC) = 𝓕 vaalerJ from hGFT]
                exact fourierVaalerJ_integrable_of h1 h2
  contJ := vaalerJ_continuous_of_corner h1
  intJ := vaalerJ_integrable_of_twoIBP h2
  intFTJ := fourierVaalerJ_integrable_of h1 h2
  ftEq := hGFT

/-! ## §5 — The minor D-1 wall `GEqReJ` from the minimal residual set -/

/-- **PROVEN — the minor D-1 wall `GEqReJ` from the minimal residual set.**

Assembles `GCFourierMatch` (`gcFourierMatch_of`) and threads it through the committed
`VaalerTruncationLimit.gEqReJ_of_match`, closing the entire `H′ = 2J` minor wall modulo
ONLY the five named residuals. -/
theorem gEqReJ_of
    (hGcont : GContinuous) (hGint : GIntegrable) (hGFT : GCFTeqJ)
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ.GEqReJ :=
  gEqReJ_of_match (gcFourierMatch_of hGcont hGint hGFT h1 h2)

/-- **PROVEN — the bundled D-1 residual `DerivInterpHEqTwoJ` from the minimal set.** -/
theorem derivInterpHEqTwoJ_of
    (hGcont : GContinuous) (hGint : GIntegrable) (hGFT : GCFTeqJ)
    (h1 : VaalerJhatContCornerOne) (h2 : VaalerJTwoIBPDecay) :
    MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail.DerivInterpHEqTwoJ :=
  derivInterpHEqTwoJ_of_match (gcFourierMatch_of hGcont hGint hGFT h1 h2)

#print axioms fourier_continuous_of_integrable
#print axioms vaalerJ_continuous_of_corner
#print axioms vaalerJ_integrable_of_twoIBP
#print axioms fourierVaalerJ_integrable_of
#print axioms gcFourierMatch_of
#print axioms gEqReJ_of
#print axioms derivInterpHEqTwoJ_of

end MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch

end
