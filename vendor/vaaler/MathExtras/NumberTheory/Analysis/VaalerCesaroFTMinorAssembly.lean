/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCesaroFTPieces

/-!
# Vaaler minor: assembling the corrected Fourier identity from the two `L²`-FT pieces

This NEW leaf wires the PROVEN core sub-residual
`VaalerCesaroFTPieces.coreFT_eq_principal_plus_Ravg_pos` (the `M ≥ 1`, analytically-correct
form of `CoreFTeqPrincipalPlusRavg`) together with the tail sub-residual `TailFTeqJtail`
into the Fourier-side conjunct of `VaalerGCCesaroPlancherel.GCCesaroPlancherelData`, and from
there to the minor wall `GCFTeqJhat`.

## The `M = 0` defect and why the wall still closes

The committed `Prop` `VaalerCesaroFTDecomposition.CoreFTeqPrincipalPlusRavg` is stated `∀ M`
but is FALSE at `M = 0` (`gCore 0 = 0`, so `𝓕(gCore 0) = 0`, while `jPrincipalCoreC ≠ 0` and
`Ravg 0 = 0`).  Correspondingly the committed `VaalerCesaroFTSignCorrection.GCesFTeqJhatPlusRavg`
is also false at `M = 0` (`𝓕(gCes 0) = 𝓕(gTail) = jTailC ≠ vaalerJCcont`).  We therefore do
NOT prove those `∀ M` `Prop`s; instead we prove the `M ≥ 1` identity and feed it through the
`atTop` limit, for which `M = 0` is immaterial (`eLpNorm`-convergence depends only on the tail).

## What this file PROVES (sorry/axiom-free)

* `gcesFT_eq_vaalerJC_plus_Ravg_pos` — **PROVEN (`M ≥ 1`)**: `𝓕_Lp(gCes M) =ᵐ vaalerJCcont + Ravg M`,
  from the split `lp_fourier_gCes_eq_add`, the proven core piece `coreFT_eq_principal_plus_Ravg_pos`,
  the tail piece `TailFTeqJtail`, and the telescoping `jPrincipalCore_add_jTail_eq_vaalerJCcont`.
* `tendsto_fourierSide_pos` — **PROVEN**: granting `TailFTeqJtail`, the Fourier-side conjunct
  `eLpNorm(𝓕(gCes M) − vaalerJCcont) → 0` (via the `M ≥ 1` identity and `tendsto_eLpNorm_ofReal_Ravg`).
* `gcCesaroPlancherelData_corrected`, `gcFTeqJhat_corrected` — **PROVEN**: assemble
  `GCCesaroPlancherelData` and the minor wall `GCFTeqJhat` from `{GIntegrable, GCBounded,
  GCesSharpSpatialL2, TailFTeqJtail}`.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerCesaroFTMinorAssembly

open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
open MathExtras.NumberTheory.Analysis.VaalerGCesMemLpDischarge
open MathExtras.NumberTheory.Analysis.VaalerCesaroRemainderL2
open MathExtras.NumberTheory.Analysis.VaalerCesaroFourierSide
open MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialSide
open MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerCesaroFTDecomposition
open MathExtras.NumberTheory.Analysis.VaalerCesaroFTPieces

/-! ## §1 — The `M ≥ 1` full Cesàro Fourier identity -/

/-- **PROVEN (`M ≥ 1`) — `𝓕_Lp(gCes M) =ᵐ vaalerJCcont + Ravg M`.**

Split `𝓕_Lp(gCes M) =ᵐ 𝓕_Lp(gCore M) + 𝓕_Lp(gTail)` (`lp_fourier_gCes_eq_add`); substitute the
PROVEN core piece (`coreFT_eq_principal_plus_Ravg_pos`, `M ≥ 1`) and the tail piece
(`TailFTeqJtail`); telescope `jPrincipalCore + jTail = vaalerJCcont`. -/
theorem gcesFT_eq_vaalerJC_plus_Ravg_pos (hTailId : TailFTeqJtail) {M : ℕ} (hM : 0 < M)
    (hCes : MemLp (gCes M) 2 (volume : Measure ℝ)) :
    (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
        (hCes.toLp (gCes M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] fun t : ℝ => vaalerJCcont t + (Ravg M t : ℂ) := by
  have hsplit := lp_fourier_gCes_eq_add M hCes (memLp_gCore_two M) memLp_gTail_two
  have hc := coreFT_eq_principal_plus_Ravg_pos hM (memLp_gCore_two M)
  have ht := hTailId memLp_gTail_two
  filter_upwards [hsplit, hc, ht] with t hsp hct htt
  rw [hsp, hct, htt]
  -- (jPrincipalCoreC + Ravg) + jTailC = vaalerJCcont + Ravg
  have hsum := jPrincipalCore_add_jTail_eq_vaalerJCcont t
  rw [show jPrincipalCoreC t + (Ravg M t : ℂ) + jTailC t
        = (jPrincipalCoreC t + jTailC t) + (Ravg M t : ℂ) by ring, hsum]

/-! ## §2 — The Fourier-side conjunct (`atTop`, `M = 0` immaterial) -/

/-- **PROVEN — the Fourier-side conjunct of `GCCesaroPlancherelData`.**

For `M ≥ 1` the integrand `𝓕(gCes M) − vaalerJCcont` is a.e. `+(Ravg M ·)`
(`gcesFT_eq_vaalerJC_plus_Ravg_pos`), so its `eLpNorm` equals `eLpNorm(Ravg M)`; for `M = 0` the
value is irrelevant to the `atTop` limit.  The eventual equality plus the PROVEN
`tendsto_eLpNorm_ofReal_Ravg` gives the conjunct. -/
theorem tendsto_fourierSide_pos (hTailId : TailFTeqJtail) :
    Filter.Tendsto
      (fun M => eLpNorm
        ((fun t : ℝ =>
            (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
              ((memLp_gCes_two_all M).toLp (gCes M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) t
              - vaalerJCcont t))
        2 (volume : Measure ℝ))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  -- eventually (M ≥ 1) the integrand eLpNorm equals eLpNorm (Ravg M ·)
  have hev : (fun M => eLpNorm
        ((fun t : ℝ =>
            (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
              ((memLp_gCes_two_all M).toLp (gCes M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) t
              - vaalerJCcont t))
        2 (volume : Measure ℝ))
      =ᶠ[Filter.atTop]
      (fun M => eLpNorm (fun t : ℝ => (Ravg M t : ℂ)) 2 (volume : Measure ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with M hM1
    have hM : 0 < M := hM1
    have hae := gcesFT_eq_vaalerJC_plus_Ravg_pos hTailId hM (memLp_gCes_two_all M)
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae] with t ht
    rw [ht]; ring
  rw [Filter.tendsto_congr' hev]
  exact tendsto_eLpNorm_ofReal_Ravg

/-! ## §3 — `GCCesaroPlancherelData` and the minor wall `GCFTeqJhat` -/

/-- **PROVEN — `GCCesaroPlancherelData` from the corrected pieces.** -/
theorem gcCesaroPlancherelData_corrected
    (hMemGC : MemLp GC 2 (volume : Measure ℝ))
    (hSharp : GCesSharpSpatialL2)
    (hTailId : TailFTeqJtail) :
    GCCesaroPlancherelData := by
  refine ⟨memLp_gCes_two_all, tendsto_spatialSide_of_sharp hMemGC hSharp, ?_⟩
  exact tendsto_fourierSide_pos hTailId

/-- **PROVEN — the minor `H′ = 2J` wall `GCFTeqJhat` from `{GIntegrable, GCBounded,
GCesSharpSpatialL2, TailFTeqJtail}`.**

The corrected, `M = 0`-defect-free assembly: `coreFT_eq_principal_plus_Ravg_pos` (PROVEN here)
supplies the core Fourier piece, `TailFTeqJtail` the tail piece, and the `atTop` limit absorbs
the `M = 0` value mismatch of the committed `∀ M` residuals. -/
theorem gcFTeqJhat_corrected
    (hGint : GIntegrable) (hBdd : GCBounded)
    (hSharp : GCesSharpSpatialL2)
    (hTailId : TailFTeqJtail) :
    GCFTeqJhat :=
  gcFTeqJhat_of_cesaro hGint hBdd
    (gcCesaroPlancherelData_corrected (memLp_GC_two_of hGint hBdd) hSharp hTailId)

/-! ## §4 — Tail discharged: the wall from `{GIntegrable, GCBounded, GCesSharpSpatialL2}` -/

/-- **PROVEN — `GCCesaroPlancherelData` with the tail residual discharged.**

Both `L²`-FT sub-residuals are now PROVEN: the core by `coreFT_eq_principal_plus_Ravg_pos`
(`M ≥ 1`) and the tail by `VaalerCesaroFTPieces.tailFT_eq_jTail` (`TailFTeqJtail`).  So the
Fourier conjunct is unconditional, leaving only the spatial input `GCesSharpSpatialL2`. -/
theorem gcCesaroPlancherelData_tailDischarged
    (hMemGC : MemLp GC 2 (volume : Measure ℝ))
    (hSharp : GCesSharpSpatialL2) :
    GCCesaroPlancherelData :=
  gcCesaroPlancherelData_corrected hMemGC hSharp tailFT_eq_jTail

/-- **PROVEN — the minor `H′ = 2J` wall `GCFTeqJhat` from `{GIntegrable, GCBounded,
GCesSharpSpatialL2}`** (both Fourier sub-residuals discharged).

The core sub-residual is proven here (`coreFT_eq_principal_plus_Ravg_pos`, the
analytically-correct `M ≥ 1` form), the tail sub-residual is proven in `VaalerCesaroFTPieces`
(`tailFT_eq_jTail`), and the `M = 0` falsity of the committed `∀ M` residuals is bypassed via the
`atTop` limit.  The ONLY remaining input is the spatial `GCesSharpSpatialL2` (separate track). -/
theorem gcFTeqJhat_tailDischarged
    (hGint : GIntegrable) (hBdd : GCBounded)
    (hSharp : GCesSharpSpatialL2) :
    GCFTeqJhat :=
  gcFTeqJhat_corrected hGint hBdd hSharp tailFT_eq_jTail

#print axioms gcesFT_eq_vaalerJC_plus_Ravg_pos
#print axioms tendsto_fourierSide_pos
#print axioms gcCesaroPlancherelData_corrected
#print axioms gcFTeqJhat_corrected
#print axioms gcCesaroPlancherelData_tailDischarged
#print axioms gcFTeqJhat_tailDischarged

end MathExtras.NumberTheory.Analysis.VaalerCesaroFTMinorAssembly
