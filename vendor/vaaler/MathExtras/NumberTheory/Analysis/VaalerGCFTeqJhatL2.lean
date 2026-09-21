/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
import AnalyticNT.Diophantine.FourierL1L2Agreement
import MathExtras.NumberTheory.Analysis.VaalerJhatCornerOne
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Vaaler Theorem 6: `GCFTeqJhat` via the Plancherel / L² route

This NEW leaf attacks the deepest minor residual `GCFTeqJhat`
(`MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ.GCFTeqJhat`, `∀ t, 𝓕 GC t =
vaalerJCcont t`, i.e. `𝓕(½H′) = Ĵ`, Vaaler 1985 eq. (2.31)→(2.32)) by the **Plancherel /
L²** route, replacing the dead spatial-DCT / uniform-`L¹`-envelope route (no uniform `L¹`
dominator for the truncations' derivatives).

## The route

The integral Fourier transform `𝓕 GC` (Real.fourierIntegral) and the **L²-extension**
`Lp.fourierTransformₗᵢ ℝ ℂ` (the Plancherel isometry) agree `a.e.` for the `L¹∩L²`
function `GC = (½H′ : ℂ)` — this is the just-proven, generic
`FourierL1L2Agreement.fourierIntegral_ae_eq_fourierTransformₗᵢ`.  The isometry is
**continuous**, so it commutes with `L²`-limits: if the truncations `G_N = ½H_N′`
converge to `GC` in `L²(ℝ)` (numerically confirmed; the shifted-Fejér tails are square
integrable) and their transforms converge to `vaalerJCcont` in `L²`, then by uniqueness of
the `L²`-limit `Lp.fourierTransformₗᵢ (GC.toLp 2) = vaalerJCcont.toLp 2` (as `L²`
elements), hence `𝓕 GC =ᵐ vaalerJCcont`.  Finally, since BOTH `𝓕 GC` (continuous by
`GIntegrable` + Riemann–Lebesgue) and `vaalerJCcont` (continuous, **unconditionally**
proven `VaalerJhatCornerOne.vaalerJhatCont_continuous_holds`) are continuous, an `a.e.`
equality is an everywhere equality (`Continuous.ae_eq_iff_eq`), giving `GCFTeqJhat`.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `GCFourierAeEqJCcont` (named `Prop`, NEVER an `axiom`) — the `a.e.` identity
  `𝓕 GC =ᵐ[volume] vaalerJCcont`, the single-sided `L²`-route content (strictly more
  primitive than `GCFTeqJhat`, since `vaalerJCcont` is continuous so `a.e.`-from-everywhere
  is the only loss).
* `gcFTeqJhat_of_aeEq` — **PROVEN** `GIntegrable → GCFourierAeEqJCcont → GCFTeqJhat`:
  upgrade the `a.e.` identity to everywhere via continuity of both sides.
* `GCFourierEqJCcontL2` (named `Prop`, NEVER an `axiom`) — the `L²`-LEVEL identity
  `Lp.fourierTransformₗᵢ ℝ ℂ (hMem.toLp GC) = (hJMem.toLp vaalerJCcont)`, the genuine
  Plancherel-limit content (the `N → ∞` Riemann–Lebesgue interchange, now living in the
  `L²` norm where the oscillatory remainder vanishes).
* `gcFourierAeEqJCcont_of_l2` — **PROVEN** `GCFourierEqJCcontL2 → GCFourierAeEqJCcont`
  (given the `L¹∩L²` memberships): transport the `L²`-element identity to the `a.e.`
  function identity through the just-proven `L¹∩L²` agreement
  (`fourierIntegral_ae_eq_fourierTransformₗᵢ`) and `MemLp.coeFn_toLp`.
* `gcFTeqJhat_of_l2` — **PROVEN** the full reduction
  `GIntegrable → (memberships) → GCFourierEqJCcontL2 → GCFTeqJhat`.

## Honest status — did / did-not

DID: routed `GCFTeqJhat` through the Plancherel `L²` isometry, reducing it to the
`L²`-level limit identity `GCFourierEqJCcontL2`, with EVERY linking step proven
(`L¹∩L²` agreement, `a.e.`-to-everywhere via continuity, `MemLp.coeFn_toLp` transport).
The `GC`-side `L¹∩L²` memberships are taken as hypotheses (matching the existing
`GIntegrable` residual pattern).  DID-NOT: the `L²`-convergence of the core derivatives
and their transforms — i.e. the construction witnessing `GCFourierEqJCcontL2` — is the
single remaining content, isolated as that named `Prop`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.27)–(2.32), p. 192; Mathlib `MeasureTheory.Lp.fourierTransformₗᵢ`
(Plancherel), `Continuous.ae_eq_iff_eq`.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform

namespace MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2

open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
open MathExtras.NumberTheory.Analysis.FourierL1L2Agreement

/-! ## §1 — The single-sided `a.e.` identity and the upgrade to `GCFTeqJhat` -/

/-- **Named `Prop` (NEVER an `axiom`): the `a.e.` `L²`-route identity.**

`𝓕 GC =ᵐ[volume] vaalerJCcont`.  Strictly more primitive than `GCFTeqJhat`: the only
difference is `a.e.`-vs-everywhere, recoverable from the (unconditional) continuity of
`vaalerJCcont` and the `GIntegrable`-continuity of `𝓕 GC`. -/
def GCFourierAeEqJCcont : Prop := (𝓕 GC) =ᵐ[volume] vaalerJCcont

/-- **PROVEN — `GCFTeqJhat` from the `a.e.` identity, via continuity of both sides.**

Given `GIntegrable` (so `𝓕 GC` is continuous by Riemann–Lebesgue) and the `a.e.` identity
`GCFourierAeEqJCcont`, the two CONTINUOUS functions `𝓕 GC` and `vaalerJCcont`
(`vaalerJCcont` is unconditionally continuous, `VaalerJhatCornerOne`) agree everywhere
(`Continuous.ae_eq_iff_eq`), i.e. `GCFTeqJhat`. -/
theorem gcFTeqJhat_of_aeEq (hGint : GIntegrable) (hAe : GCFourierAeEqJCcont) :
    GCFTeqJhat := by
  have hcGC : Continuous (𝓕 GC) := fourier_continuous_of_integrable hGint
  have hcJ : Continuous vaalerJCcont :=
    MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.vaalerJhatCont_continuous_holds
  have hEq : (𝓕 GC) = vaalerJCcont := (hcGC.ae_eq_iff_eq volume hcJ).mp hAe
  intro t
  rw [hEq]

/-! ## §2 — The `L²`-level Plancherel identity and its transport to the `a.e.` identity -/

/-- **Named `Prop` (NEVER an `axiom`): the `L²`-LEVEL Plancherel identity.**

The Plancherel `L²`-extension of `GC` equals (as an `L²` element) the `L²`-class of the
corrected continuous transform `vaalerJCcont`:

    Lp.fourierTransformₗᵢ ℝ ℂ (hMem.toLp GC) = hJMem.toLp vaalerJCcont.

This is the genuine `N → ∞` Riemann–Lebesgue interchange, now living in the `L²` norm: the
truncations `G_N → GC` in `L²` ⇒ (isometry continuity) `𝓕 G_N → 𝓕 GC` in `L²`, and
`𝓕 G_N → vaalerJCcont` in `L²` (the oscillatory remainder vanishes in the `L²_t` norm).
Carries the `L¹∩L²` memberships of `GC` and `vaalerJCcont` as parameters. -/
def GCFourierEqJCcontL2
    (hMem : MemLp GC 2) (hJMem : MemLp vaalerJCcont 2) : Prop :=
  MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hMem.toLp GC) = hJMem.toLp vaalerJCcont

/-- **PROVEN — the `a.e.` identity from the `L²`-level identity.**

From the `L²`-element identity `GCFourierEqJCcontL2` and the just-proven `L¹∩L²` agreement
(`fourierIntegral_ae_eq_fourierTransformₗᵢ`), transport to the `a.e.` function identity:

    𝓕 GC =ᵐ ⇑(Lp.fourierTransformₗᵢ (GC.toLp)) =ᵐ ⇑(vaalerJCcont.toLp) =ᵐ vaalerJCcont.

The first `=ᵐ` is `fourierIntegral_ae_eq_fourierTransformₗᵢ` (needs `GC ∈ L¹∩L²`); the
middle is the `L²`-identity (coercions of equal `L²` elements are `=ᵐ`); the last is
`MemLp.coeFn_toLp`. -/
theorem gcFourierAeEqJCcont_of_l2
    (hGint : GIntegrable) (hMem : MemLp GC 2) (hJMem : MemLp vaalerJCcont 2)
    (hL2 : GCFourierEqJCcontL2 hMem hJMem) :
    GCFourierAeEqJCcont := by
  -- `𝓕 GC =ᵐ ⇑(Lp.fourierTransformₗᵢ (GC.toLp))`  (L¹∩L² agreement, symm)
  have h1 : (𝓕 GC) =ᵐ[volume]
      (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hMem.toLp GC)) : ℝ → ℂ) :=
    (fourierIntegral_ae_eq_fourierTransformₗᵢ hGint hMem).symm
  -- `⇑(Lp.fourierTransformₗᵢ (GC.toLp)) =ᵐ ⇑(vaalerJCcont.toLp)`  (equal L² elements)
  have h2 : (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hMem.toLp GC)) : ℝ → ℂ)
      =ᵐ[volume] (⇑(hJMem.toLp vaalerJCcont) : ℝ → ℂ) := by
    rw [hL2]
  -- `⇑(vaalerJCcont.toLp) =ᵐ vaalerJCcont`  (`coeFn_toLp`)
  have h3 : (⇑(hJMem.toLp vaalerJCcont) : ℝ → ℂ) =ᵐ[volume] vaalerJCcont :=
    hJMem.coeFn_toLp
  exact h1.trans (h2.trans h3)

/-- **PROVEN — `GCFTeqJhat` from the `L²`-level Plancherel identity.**

The full Plancherel-route reduction: `GIntegrable`, the `L¹∩L²` memberships, and the
`L²`-level identity `GCFourierEqJCcontL2` together discharge `GCFTeqJhat`. -/
theorem gcFTeqJhat_of_l2
    (hGint : GIntegrable) (hMem : MemLp GC 2) (hJMem : MemLp vaalerJCcont 2)
    (hL2 : GCFourierEqJCcontL2 hMem hJMem) :
    GCFTeqJhat :=
  gcFTeqJhat_of_aeEq hGint (gcFourierAeEqJCcont_of_l2 hGint hMem hJMem hL2)

#print axioms gcFTeqJhat_of_aeEq
#print axioms gcFourierAeEqJCcont_of_l2
#print axioms gcFTeqJhat_of_l2

end MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2
