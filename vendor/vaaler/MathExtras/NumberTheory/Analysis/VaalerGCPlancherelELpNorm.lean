/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Vaaler Theorem 6: the Plancherel-limit data as elementary `eLpNorm`-convergences

This NEW leaf restates the bundled Plancherel-limit datum `GCPlancherelLimitData`
(`MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2Limit.GCPlancherelLimitData`, the
existence of an `L²` truncation family `gN → GC.toLp` with `𝓕 gN → vaalerJCcont.toLp` in
`L²`) in the most **elementary, numerically-checkable** form: two
`eLpNorm (· - ·) 2 → 0` convergences of a family of plain `L²` functions.

This is purely a *restatement* (an `iff`-style reduction proved outright), pushing the
residual to the most primitive shape so that the remaining analytic work — the spatial
`L²`-convergence of the shifted-Fejér core derivatives and the `L²`-vanishing of the
oscillatory transform remainder — is stated directly as `eLpNorm`-limits.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `GCPlancherelELpNormData (hMem hJMem)` (named `Prop`, NEVER an `axiom`) — there is a
  family `g : ℕ → ℝ → ℂ` with each `g N ∈ L²`, such that
    `eLpNorm (g N - GC) 2 → 0`  and
    `eLpNorm (⇑(𝓕 ((hg N).toLp (g N))) - vaalerJCcont) 2 → 0`,
  where `𝓕 = Lp.fourierTransformₗᵢ ℝ ℂ` (Plancherel isometry).
* `gcPlancherelLimitData_of_eLpNorm` — **PROVEN** `GCPlancherelELpNormData hMem hJMem →
  GCPlancherelLimitData hMem hJMem`, via Mathlib's
  `Lp.tendsto_Lp_iff_tendsto_eLpNorm''` / `tendsto_Lp_of_tendsto_eLpNorm`.
* `gcFTeqJhat_of_eLpNormData` — **PROVEN** the full chain to `GCFTeqJhat` from
  `{GIntegrable, GCBounded, GCPlancherelELpNormData}`.

## Honest status — did / did-not

DID: restated the Plancherel-limit datum as two elementary `eLpNorm → 0` convergences of a
single `L²` truncation family, proving the equivalence-direction outright.  DID-NOT:
exhibit the truncation family and prove the two `eLpNorm`-limits (the genuine spatial-`L²`
shifted-Fejér convergence and the `L²` Riemann–Lebesgue vanishing); that is the content of
`GCPlancherelELpNormData`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.31)–(2.32); Mathlib `MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''`.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal

namespace MathExtras.NumberTheory.Analysis.VaalerGCPlancherelELpNorm

open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2Limit
open MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo

/-! ## §1 — The elementary `eLpNorm`-convergence form of the Plancherel-limit data -/

/-- **Named `Prop` (NEVER an `axiom`): the elementary `eLpNorm` form.**

There is a truncation family `g : ℕ → ℝ → ℂ` and `L²`-memberships `hg N : MemLp (g N) 2`
such that

* `eLpNorm (g N - GC) 2 volume → 0`  (the truncations converge to `GC` in `L²`); and
* `eLpNorm (⇑(Lp.fourierTransformₗᵢ ℝ ℂ ((hg N).toLp (g N))) - vaalerJCcont) 2 volume → 0`
  (their Plancherel transforms converge to `Ĵ` in `L²`).

Carries the `L¹∩L²` memberships of `GC` and `vaalerJCcont` as parameters for the
downstream identification of the limit `L²` classes. -/
def GCPlancherelELpNormData
    (hMem : MemLp GC 2 (volume : Measure ℝ))
    (hJMem : MemLp MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.vaalerJCcont 2
      (volume : Measure ℝ)) : Prop :=
  ∃ (g : ℕ → ℝ → ℂ) (hg : ∀ N, MemLp (g N) 2 (volume : Measure ℝ)),
    Filter.Tendsto (fun N => eLpNorm (fun x : ℝ => g N x - GC x) 2 (volume : Measure ℝ))
        Filter.atTop (nhds (0 : ℝ≥0∞)) ∧
    Filter.Tendsto
      (fun N => eLpNorm
        ((fun x : ℝ =>
            (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
              ((hg N).toLp (g N) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) x
              - MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.vaalerJCcont x))
        2 (volume : Measure ℝ))
      Filter.atTop (nhds (0 : ℝ≥0∞))

/-! ## §2 — The bundled limit data from the elementary `eLpNorm` form -/

/-- **PROVEN — `GCPlancherelLimitData` from the elementary `eLpNorm` form.**

`Lp.tendsto_Lp_iff_tendsto_eLpNorm''` turns the spatial `eLpNorm (g N - GC) → 0` into the
`L²`-`Tendsto` `(hg N).toLp (g N) → GC.toLp`; `tendsto_Lp_of_tendsto_eLpNorm` turns the
transform-side `eLpNorm (⇑(𝓕 (g N).toLp) - vaalerJCcont) → 0` into
`𝓕 ((hg N).toLp (g N)) → vaalerJCcont.toLp`.  Witness the existential of
`GCPlancherelLimitData` with `gN := (hg N).toLp (g N)`. -/
theorem gcPlancherelLimitData_of_eLpNorm
    (hMem : MemLp GC 2 (volume : Measure ℝ))
    (hJMem : MemLp MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.vaalerJCcont 2
      (volume : Measure ℝ))
    (hData : GCPlancherelELpNormData hMem hJMem) :
    GCPlancherelLimitData hMem hJMem := by
  obtain ⟨g, hg, hC1, hC2⟩ := hData
  refine ⟨fun N => (hg N).toLp (g N), ?_, ?_⟩
  · -- spatial L²-convergence ⇒ Tendsto to `GC.toLp`
    exact (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg GC hMem).mpr hC1
  · -- transform-side: `𝓕 ((hg N).toLp (g N)) → vaalerJCcont.toLp`
    exact MeasureTheory.Lp.tendsto_Lp_of_tendsto_eLpNorm
      MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.vaalerJCcont hJMem hC2

/-! ## §3 — `GCFTeqJhat` from the elementary `eLpNorm` data (full chain) -/

/-- **PROVEN — `GCFTeqJhat` from the elementary `eLpNorm` Plancherel data.**

The deepest minor residual `GCFTeqJhat` (`𝓕(½H′) = Ĵ`, Vaaler eq. (2.31)→(2.32)) now rests
on `{GIntegrable, GCBounded, GCPlancherelELpNormData}` — the last being two elementary
`eLpNorm → 0` convergences of an `L²` truncation family. -/
theorem gcFTeqJhat_of_eLpNormData
    (hGint : GIntegrable) (hBdd : GCBounded)
    (hData : GCPlancherelELpNormData (memLp_GC_two_of hGint hBdd) memLp_vaalerJCcont_two) :
    GCFTeqJhat :=
  gcFTeqJhat_of_plancherelLimit_of_bounded hGint hBdd
    (gcPlancherelLimitData_of_eLpNorm (memLp_GC_two_of hGint hBdd) memLp_vaalerJCcont_two hData)

#print axioms gcPlancherelLimitData_of_eLpNorm
#print axioms gcFTeqJhat_of_eLpNormData

end MathExtras.NumberTheory.Analysis.VaalerGCPlancherelELpNorm
