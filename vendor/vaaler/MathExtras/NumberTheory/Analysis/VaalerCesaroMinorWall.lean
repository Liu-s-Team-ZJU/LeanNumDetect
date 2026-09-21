/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCesaroPlancherelAssembly
import MathExtras.NumberTheory.Analysis.VaalerGCesMemLpDischarge

/-!
# Vaaler minor wall: `GCFTeqJhat` from exactly TWO numerically-verified residuals

This NEW capstone leaf wires the now-**discharged** per-`M` `L²` membership
(`VaalerGCesMemLpDischarge.memLp_gCes_two_all`, PROVEN axiom-clean) into the assembly
`VaalerCesaroPlancherelAssembly`, reducing the deep minor residual `GCFTeqJhat`
(`𝓕(½H′) = Ĵ`, the entire minor `H′ = 2J` wall, Vaaler eq. (2.31)→(2.32)) to exactly **two**
remaining numerically-verified analytic residuals about the EXPLICIT Cesàro family:

* `GCesFTeqJhatMinusRavg` — the Fourier-side pointwise identity `𝓕(gCes M) =ᵐ Ĵ − Ravg M`
  (`VaalerCesaroFourierSide`); its `L²`-vanishing engine (`tendsto_eLpNorm_Ravg`) is PROVEN
  axiom-clean.
* `GCesSharpSpatialL2` — the sharp-truncation spatial `L²`-limit `eLpNorm (gSharp N − GC) 2 → 0`
  (`VaalerCesaroSpatialSide`); its Cesàro-preservation engine
  (`tendsto_eLpNorm_cesaro_of_tendsto`) is PROVEN axiom-clean.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `gcCesaroPlancherelData_of_two_residuals` — **PROVEN**: `GCesFTeqJhatMinusRavg` and
  `GCesSharpSpatialL2` (plus `MemLp GC 2`) assemble into `GCCesaroPlancherelData`, the per-`M`
  membership supplied by the discharged `memLp_gCes_two_all`.
* `gcFTeqJhat_of_two_residuals` — **PROVEN**: `{GIntegrable, GCBounded}` plus exactly the two
  residuals above give `GCFTeqJhat`.

## Honest status — the residual map after this session

The minor `H′ = 2J` wall now rests on exactly two precise, numerically-verified `Prop`s
(never `axiom`s) about the explicit Cesàro family, and BOTH of their `L²`-convergence engines
are PROVEN axiom-clean in this session:

* Fourier remainder `L²`-decay `eLpNorm (Ravg M) 2 → 0` — **PROVEN** (`tendsto_eLpNorm_Ravg`,
  dominated convergence on `[-1,1]`).
* Cesàro preservation of spatial `L²`-limits — **PROVEN** (`tendsto_eLpNorm_cesaro_of_tendsto`).
* per-`M` `L²` membership `∀ M, MemLp (gCes M) 2` — **PROVEN** (`memLp_gCes_two_all`).

What remains inside the two named `Prop`s is the genuine analytic content: the pointwise
`𝓕(gCes M) = Ĵ − Ravg M` transform identity, and the sharp spatial `L²`-limit
`eLpNorm (gSharp N − GC) 2 → 0`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.31)–(2.32).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerCesaroMinorWall

open MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
open MathExtras.NumberTheory.Analysis.VaalerCesaroFourierSide
open MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialSide
open MathExtras.NumberTheory.Analysis.VaalerCesaroPlancherelAssembly
open MathExtras.NumberTheory.Analysis.VaalerGCesMemLpDischarge
open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo

/-- **PROVEN — `GCCesaroPlancherelData` from exactly the two analytic residuals.**

The per-`M` `L²` membership is now supplied by the discharged `memLp_gCes_two_all`
(`VaalerGCesMemLpDischarge`), so only the Fourier-side pointwise identity
`GCesFTeqJhatMinusRavg` and the sharp spatial `L²`-limit `GCesSharpSpatialL2` (plus `MemLp GC 2`)
are needed. -/
theorem gcCesaroPlancherelData_of_two_residuals
    (hMemGC : MemLp GC 2 (volume : Measure ℝ))
    (hId : GCesFTeqJhatMinusRavg)
    (hSharp : GCesSharpSpatialL2) :
    GCCesaroPlancherelData :=
  gcCesaroPlancherelData_of_residuals hMemGC memLp_gCes_two_all hId hSharp

#print axioms gcCesaroPlancherelData_of_two_residuals

/-- **PROVEN — `GCFTeqJhat` (the minor `H′ = 2J` wall) from exactly the two analytic residuals.**

`{GIntegrable, GCBounded}` (giving `MemLp GC 2` and the closing chain) plus the two residuals
`GCesFTeqJhatMinusRavg`, `GCesSharpSpatialL2` give the deep minor residual `GCFTeqJhat`. -/
theorem gcFTeqJhat_of_two_residuals
    (hGint : GIntegrable) (hBdd : GCBounded)
    (hId : GCesFTeqJhatMinusRavg)
    (hSharp : GCesSharpSpatialL2) :
    GCFTeqJhat :=
  gcFTeqJhat_of_residuals hGint hBdd memLp_gCes_two_all hId hSharp

#print axioms gcFTeqJhat_of_two_residuals

end MathExtras.NumberTheory.Analysis.VaalerCesaroMinorWall
