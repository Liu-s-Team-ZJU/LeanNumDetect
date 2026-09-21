/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialL2DecayCore
import MathExtras.NumberTheory.Analysis.VaalerCesaroFTMinorAssembly
import MathExtras.NumberTheory.Analysis.VaalerGCBoundedProof
import MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ

/-!
# Vaaler minor: the `GCFTeqJhat` wall on the SINGLE spatial residual `GCesSpatialL2DecayBound`

This NEW leaf assembles the deep minor residual `GCFTeqJhat` (the minor `H′ = 2J` wall,
`𝓕(½H′) = Ĵ`, Vaaler eq. (2.31)→(2.32)) on the **smallest genuine residual set**, by combining
three streams that are already PROVEN/discharged in the repo with the single remaining quantitative
spatial estimate.

## Why the residual set collapses to `{GCesSpatialL2DecayBound}`

The committed `GCFTeqJhat` reduction `VaalerGCCesaroPlancherel.gcFTeqJhat_of_cesaro` consumes
`{GIntegrable, GCBounded, GCCesaroPlancherelData}`, and `GCCesaroPlancherelData` bundles three
conjuncts:

* **per-`M` `L²` membership** `∀ M, MemLp (gCes M) 2` — PROVEN unconditionally
  (`VaalerGCesMemLpDischarge.memLp_gCes_two_all`).
* **the Fourier-side conjunct** `eLpNorm (𝓕_Lp(gCes M) − vaalerJCcont) 2 → 0` — PROVEN
  unconditionally: `VaalerCesaroFTMinorAssembly.tendsto_fourierSide_pos` granting `TailFTeqJtail`,
  and `TailFTeqJtail` is itself PROVEN (`VaalerCesaroFTPieces.tailFT_eq_jTail`).  The core piece
  `coreFT_eq_principal_plus_Ravg_pos` is PROVEN; the `M = 0` falsity of the committed `∀ M` Fourier
  residuals is bypassed via the `atTop` limit.  **No `GCesFTeqJhatMinusRavg` hypothesis is needed.**
* **the spatial-side conjunct** `eLpNorm (gCes M − GC) 2 → 0` — this is the one genuinely remaining
  analytic input, supplied here from the single quantitative decay `Prop`
  `VaalerCesaroSpatialL2DecayCore.GCesSpatialL2DecayBound` via `tendsto_decayBound`.

And `GIntegrable`, `GCBounded` are both PROVEN (`VaalerGEqVaalerJ.gIntegrable_holds`,
`VaalerGCBoundedProof.gCBounded_proven`).  Hence the entire minor `H′ = 2J` wall `GCFTeqJhat` rests
on the **single** named `Prop` `GCesSpatialL2DecayBound` — the Cesàro/Fejér `M^{-1/2}` spatial `L²`
decay (true, numerically verified, NEVER an `axiom`).  The FALSE sharp residual `GCesSharpSpatialL2`
is entirely absent from this chain.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `gcCesaroPlancherelData_spatialClosed` — **PROVEN**: `GCCesaroPlancherelData` from
  `GCesSpatialL2DecayBound` (membership + discharged Fourier conjunct + decay-bound spatial
  conjunct).  No Fourier-side hypothesis.
* `gcFTeqJhat_spatialClosed` — **PROVEN**: the minor wall `GCFTeqJhat` from
  `GCesSpatialL2DecayBound` ALONE (the proven `GIntegrable`/`GCBounded` supplied internally).

## Honest status — did / did-not

DID: collapsed the minor wall `GCFTeqJhat` onto the single quantitative spatial residual
`GCesSpatialL2DecayBound`, discharging the Fourier side (`tailFT_eq_jTail` +
`tendsto_fourierSide_pos`), the membership (`memLp_gCes_two_all`), and the `GC` integrability /
boundedness (`gIntegrable_holds`, `gCBounded_proven`) — all already PROVEN in the repo.
DID-NOT (isolated, in `VaalerCesaroSpatialL2DecayCore`, as the named `Prop` `GCesSpatialL2DecayBound`):
the `M^{-1/2}` Cesàro spatial `L²` estimate itself.  (A parallel track, `VaalerFejerDerivAutocorr`,
reduces the shifted-Fejér almost-orthogonality input to a single autocorrelation closed-form `Prop`;
that track is the route toward eventually proving `GCesSpatialL2DecayBound` from first principles.)

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.31)–(2.32).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerMinorWallSpatialClosed

open MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
open MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialL2DecayCore
open MathExtras.NumberTheory.Analysis.VaalerCesaroFTMinorAssembly
open MathExtras.NumberTheory.Analysis.VaalerCesaroFTPieces
open MathExtras.NumberTheory.Analysis.VaalerGCesMemLpDischarge
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerGCBoundedProof
open MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ

/-! ## §1 — `GCCesaroPlancherelData` with the Fourier side discharged -/

/-- **PROVEN — `GCCesaroPlancherelData` from the single spatial decay `Prop`.**

Bundles the three conjuncts of `GCCesaroPlancherelData`:
* membership `memLp_gCes_two_all` (proven);
* spatial `eLpNorm (gCes M − GC) 2 → 0` from `tendsto_decayBound` (the decay `Prop`);
* Fourier `eLpNorm (𝓕_Lp(gCes M) − vaalerJCcont) 2 → 0` from `tendsto_fourierSide_pos` applied to
  the PROVEN `tailFT_eq_jTail`.

No `GCesFTeqJhatMinusRavg` hypothesis: the Fourier side is unconditional. -/
theorem gcCesaroPlancherelData_spatialClosed
    (hDecay : GCesSpatialL2DecayBound) :
    GCCesaroPlancherelData :=
  ⟨memLp_gCes_two_all, tendsto_decayBound hDecay, tendsto_fourierSide_pos tailFT_eq_jTail⟩

#print axioms gcCesaroPlancherelData_spatialClosed

/-! ## §2 — The minor wall `GCFTeqJhat` on the single spatial residual -/

/-- **PROVEN — the minor `H′ = 2J` wall `GCFTeqJhat` from `GCesSpatialL2DecayBound` ALONE.**

`GIntegrable` (`gIntegrable_holds`) and `GCBounded` (`gCBounded_proven`) are supplied internally
from the repo's proven discharges; the Fourier side is discharged inside
`gcCesaroPlancherelData_spatialClosed`.  Thus the entire deep minor residual `GCFTeqJhat`
(`𝓕(½H′) = Ĵ`, Vaaler eq. (2.31)→(2.32)) rests on the single quantitative Cesàro/Fejér spatial
`L²`-decay `Prop` `GCesSpatialL2DecayBound`. -/
theorem gcFTeqJhat_spatialClosed
    (hDecay : GCesSpatialL2DecayBound) :
    GCFTeqJhat :=
  gcFTeqJhat_of_cesaro gIntegrable_holds gCBounded_proven
    (gcCesaroPlancherelData_spatialClosed hDecay)

#print axioms gcFTeqJhat_spatialClosed

end MathExtras.NumberTheory.Analysis.VaalerMinorWallSpatialClosed
