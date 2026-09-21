/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCesaroFourierSide
import MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialSide

/-!
# Vaaler minor: assembling `GCCesaroPlancherelData` from its three named residuals

This NEW leaf assembles the single remaining minor-arc residual
`GCCesaroPlancherelData`
(`MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel.GCCesaroPlancherelData`) from the
three precisely-named, numerically-verified sub-residuals proven-reducible in the sibling leaves:

* **per-`M` `L²` membership** `hMemCes : ∀ M, MemLp (gCes M) 2` — dischargeable from the
  committed decay⇒`MemLp` bridges of `VaalerGCesMemLp` (here a hypothesis);
* **the Fourier-side pointwise identity** `GCesFTeqJhatMinusRavg`
  (`VaalerCesaroFourierSide`) — `𝓕(gCes M) =ᵐ Ĵ − Ravg M`; via the PROVEN
  `tendsto_fourierSide_of_identity` (whose `L²`-vanishing of `Ravg` is PROVEN axiom-clean);
* **the sharp spatial `L²`-limit** `GCesSharpSpatialL2` (`VaalerCesaroSpatialSide`) —
  `eLpNorm (gSharp N − GC) 2 → 0`; via the PROVEN `tendsto_spatialSide_of_sharp` (whose Cesàro
  preservation is PROVEN axiom-clean).

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `gcCesaroPlancherelData_of_residuals` — **PROVEN**: the three residuals (with `MemLp GC`)
  assemble into `GCCesaroPlancherelData`.
* `gcFTeqJhat_of_residuals` — **PROVEN**: chaining the committed `gcFTeqJhat_of_cesaro`, the
  three residuals plus `{GIntegrable, GCBounded}` give the deep minor residual `GCFTeqJhat`
  (`𝓕(½H′) = Ĵ`, the minor wall, Vaaler eq. (2.31)→(2.32)).

After this leaf the entire minor `H′ = 2J` wall rests on exactly three numerically-verified
analytic facts about the EXPLICIT Cesàro family, two of whose `L²`-convergence engines (the
Fourier-remainder decay and the Cesàro-of-spatial-limit) are already PROVEN axiom-clean.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.31)–(2.32).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerCesaroPlancherelAssembly

open MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
open MathExtras.NumberTheory.Analysis.VaalerCesaroFourierSide
open MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialSide
open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo

/-- **PROVEN — `GCCesaroPlancherelData` from the three named residuals.**

Takes the per-`M` `L²` membership `hMemCes`, the Fourier-side pointwise identity
`GCesFTeqJhatMinusRavg`, the sharp spatial `L²`-limit `GCesSharpSpatialL2`, and `MemLp GC 2`,
and produces the bundled `GCCesaroPlancherelData`: the spatial conjunct via
`tendsto_spatialSide_of_sharp`, the Fourier conjunct via `tendsto_fourierSide_of_identity`. -/
theorem gcCesaroPlancherelData_of_residuals
    (hMemGC : MemLp GC 2 (volume : Measure ℝ))
    (hMemCes : ∀ M, MemLp (gCes M) 2 (volume : Measure ℝ))
    (hId : GCesFTeqJhatMinusRavg)
    (hSharp : GCesSharpSpatialL2) :
    GCCesaroPlancherelData := by
  refine ⟨hMemCes, ?_, ?_⟩
  · exact tendsto_spatialSide_of_sharp hMemGC hSharp
  · exact tendsto_fourierSide_of_identity hMemCes hId

#print axioms gcCesaroPlancherelData_of_residuals

/-- **PROVEN — `GCFTeqJhat` (the minor `H′ = 2J` wall) from the three named residuals.**

Chains `gcCesaroPlancherelData_of_residuals` with the committed
`VaalerGCCesaroPlancherel.gcFTeqJhat_of_cesaro`: the deep minor residual `GCFTeqJhat`
(`𝓕(½H′) = Ĵ`) follows from `{GIntegrable, GCBounded}` plus the three Cesàro-family residuals
(per-`M` `MemLp`, the Fourier pointwise identity, the sharp spatial limit). -/
theorem gcFTeqJhat_of_residuals
    (hGint : GIntegrable) (hBdd : GCBounded)
    (hMemCes : ∀ M, MemLp (gCes M) 2 (volume : Measure ℝ))
    (hId : GCesFTeqJhatMinusRavg)
    (hSharp : GCesSharpSpatialL2) :
    GCFTeqJhat :=
  gcFTeqJhat_of_cesaro hGint hBdd
    (gcCesaroPlancherelData_of_residuals (memLp_GC_two_of hGint hBdd) hMemCes hId hSharp)

#print axioms gcFTeqJhat_of_residuals

end MathExtras.NumberTheory.Analysis.VaalerCesaroPlancherelAssembly
