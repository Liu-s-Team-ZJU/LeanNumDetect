/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2

/-!
# Vaaler Theorem 6: the `L²`-level Plancherel identity as a convergence limit

This NEW leaf reduces the `L²`-level identity `GCFourierEqJCcontL2`
(`MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2.GCFourierEqJCcontL2`,
`Lp.fourierTransformₗᵢ ℝ ℂ (GC.toLp) = vaalerJCcont.toLp`) to the two genuine
**`L²`-convergence** facts of the Plancherel route, using only the **continuity** of the
Fourier isometry (`Lp.fourierTransformₗᵢ` is a `LinearIsometryEquiv`, hence continuous) and
uniqueness of limits in the Hausdorff space `L²`.

## The reduction

Let `gN : ℕ → Lp ℂ 2` be the `L²`-classes of the truncations `G_N = ½H_N′` (plus the
`L²` tail piece).  Suppose:

* (C1) `gN → GC.toLp` in `L²`             (the truncations converge to `GC` in `L²`);
* (C2) `𝓕 gN → vaalerJCcont.toLp` in `L²` (their transforms converge to `Ĵ` in `L²`).

The isometry `𝓕 = Lp.fourierTransformₗᵢ` is continuous, so from (C1)
`𝓕 gN → 𝓕 (GC.toLp)` in `L²`.  Together with (C2) and uniqueness of the `L²`-limit,
`𝓕 (GC.toLp) = vaalerJCcont.toLp`, i.e. `GCFourierEqJCcontL2`.

This is exactly where the Plancherel route earns its keep: the `N → ∞` Riemann–Lebesgue
interchange that fails *pointwise* (the oscillatory remainder
`cos(π(2N+1)t)/sin(π t)` does not converge for fixed `t`) succeeds in the `L²` **norm**,
where that remainder vanishes.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `GCCoreL2Tendsto` (named `Prop`, NEVER an `axiom`) — (C1): there is an `L²` truncation
  family `gN` with `gN → GC.toLp` in `L²`.  Bundled existentially with the transform limit.
* `GCFourierCoreL2Tendsto` — (C2) bundled inside the same existential.
* `GCPlancherelLimitData (hMem) (hJMem)` (named `Prop`, NEVER an `axiom`) — the bundled
  existential `∃ gN, (gN → GC.toLp in L²) ∧ (𝓕 gN → vaalerJCcont.toLp in L²)`, the genuine
  remaining Plancherel content.
* `gcFourierEqJCcontL2_of_plancherelLimit` — **PROVEN**
  `GCPlancherelLimitData hMem hJMem → GCFourierEqJCcontL2 hMem hJMem`, by isometry
  continuity + limit uniqueness.
* `gcFTeqJhat_of_plancherelLimit` — **PROVEN** the full chain
  `GIntegrable → (memberships) → GCPlancherelLimitData → GCFTeqJhat`, composing with the
  committed `VaalerGCFTeqJhatL2.gcFTeqJhat_of_l2`.

## Honest status — did / did-not

DID: reduced the `L²`-level identity to the existence of an `L²`-convergent truncation
family whose transforms converge to `Ĵ` in `L²` — the textbook Plancherel-limit data —
proving the implication outright from isometry continuity.  DID-NOT: construct the explicit
family `gN` and verify the two `L²`-convergences (the square-integrable shifted-Fejér tails
and the `L²`-vanishing of the oscillatory remainder); that is the content of
`GCPlancherelLimitData`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.31)–(2.32); Plancherel `MeasureTheory.Lp.fourierTransformₗᵢ`.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform

namespace MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2Limit

open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2

/-! ## §0 — The `vaalerJCcont` `L²`-membership is unconditional -/

/-- **PROVEN (unconditional) — `vaalerJCcont ∈ L²`.**

`vaalerJCcont` is continuous (`VaalerTheorem6JFT.vaalerJhatCont_continuous_holds`,
unconditional) and compactly supported (`vaalerJCcont_support_subset ⊆ [-1,1]`), hence
`MemLp 2` (`Continuous.memLp_of_hasCompactSupport`).  This discharges the `Ĵ`-side `L²`
hypothesis of the whole Plancherel route. -/
theorem memLp_vaalerJCcont_two : MemLp vaalerJCcont 2 := by
  have hcont : Continuous vaalerJCcont :=
    MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.vaalerJhatCont_continuous_holds
  have hsupp : HasCompactSupport vaalerJCcont := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro x hx
    by_contra hne
    exact hx (MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.vaalerJCcont_support_subset hne)
  exact hcont.memLp_of_hasCompactSupport hsupp

/-! ## §1 — The bundled Plancherel-limit data -/

/-- **Named `Prop` (NEVER an `axiom`): the Plancherel-limit data.**

There exists an `L²` truncation family `gN : ℕ → Lp ℂ 2` such that

* `gN → GC.toLp` in `L²` (the truncations converge to `GC` in the `L²` norm); and
* `𝓕 gN → vaalerJCcont.toLp` in `L²` (their `L²`-transforms converge to `Ĵ`).

`𝓕` here is the Plancherel `L²`-isometry `Lp.fourierTransformₗᵢ ℝ ℂ`.  This bundles the two
genuine `L²`-convergences of Vaaler eq. (2.31)→(2.32). -/
def GCPlancherelLimitData (hMem : MemLp GC 2) (hJMem : MemLp vaalerJCcont 2) : Prop :=
  ∃ gN : ℕ → Lp (α := ℝ) ℂ 2,
    Filter.Tendsto gN Filter.atTop (nhds (hMem.toLp GC)) ∧
    Filter.Tendsto (fun N => MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (gN N))
      Filter.atTop (nhds (hJMem.toLp vaalerJCcont))

/-! ## §2 — The `L²`-level identity from the Plancherel-limit data -/

/-- **PROVEN — `GCFourierEqJCcontL2` from the Plancherel-limit data.**

Given an `L²`-convergent truncation family `gN → GC.toLp` whose transforms
`𝓕 gN → vaalerJCcont.toLp` (both in `L²`), the continuity of the Fourier isometry
`Lp.fourierTransformₗᵢ ℝ ℂ` transports the first limit to `𝓕 gN → 𝓕 (GC.toLp)`; uniqueness
of the `L²`-limit against the second gives `𝓕 (GC.toLp) = vaalerJCcont.toLp`. -/
theorem gcFourierEqJCcontL2_of_plancherelLimit
    (hMem : MemLp GC 2) (hJMem : MemLp vaalerJCcont 2)
    (hData : GCPlancherelLimitData hMem hJMem) :
    GCFourierEqJCcontL2 hMem hJMem := by
  obtain ⟨gN, hC1, hC2⟩ := hData
  -- transport (C1) through the continuous isometry
  have hFT : Filter.Tendsto
      (fun N => MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (gN N)) Filter.atTop
      (nhds (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hMem.toLp GC))) :=
    ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).continuous.tendsto (hMem.toLp GC)).comp hC1
  -- uniqueness of the L²-limit
  exact tendsto_nhds_unique hFT hC2

/-! ## §3 — `GCFTeqJhat` from the Plancherel-limit data (full chain) -/

/-- **PROVEN — `GCFTeqJhat` from the Plancherel-limit data.**

Composes `gcFourierEqJCcontL2_of_plancherelLimit` with the committed
`VaalerGCFTeqJhatL2.gcFTeqJhat_of_l2`: the deepest minor residual `GCFTeqJhat`
(`𝓕(½H′) = Ĵ`) now rests on `GIntegrable`, the `L¹∩L²` memberships of `GC`/`vaalerJCcont`,
and the single Plancherel-limit datum `GCPlancherelLimitData`. -/
theorem gcFTeqJhat_of_plancherelLimit
    (hGint : GIntegrable) (hMem : MemLp GC 2) (hJMem : MemLp vaalerJCcont 2)
    (hData : GCPlancherelLimitData hMem hJMem) :
    GCFTeqJhat :=
  gcFTeqJhat_of_l2 hGint hMem hJMem
    (gcFourierEqJCcontL2_of_plancherelLimit hMem hJMem hData)

/-- **PROVEN — `GCFTeqJhat` with the `Ĵ`-side `L²` membership discharged.**

Streamlined entry point: since `MemLp vaalerJCcont 2` is unconditional
(`memLp_vaalerJCcont_two`), the deepest minor residual `GCFTeqJhat` rests on just
`GIntegrable`, the single `GC`-side `L²` membership `MemLp GC 2`, and the Plancherel-limit
datum `GCPlancherelLimitData hMem memLp_vaalerJCcont_two`. -/
theorem gcFTeqJhat_of_plancherelLimit'
    (hGint : GIntegrable) (hMem : MemLp GC 2)
    (hData : GCPlancherelLimitData hMem memLp_vaalerJCcont_two) :
    GCFTeqJhat :=
  gcFTeqJhat_of_plancherelLimit hGint hMem memLp_vaalerJCcont_two hData

#print axioms memLp_vaalerJCcont_two
#print axioms gcFourierEqJCcontL2_of_plancherelLimit
#print axioms gcFTeqJhat_of_plancherelLimit
#print axioms gcFTeqJhat_of_plancherelLimit'

end MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2Limit
