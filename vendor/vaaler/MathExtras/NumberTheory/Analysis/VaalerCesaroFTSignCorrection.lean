/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCesaroMinorWall

/-!
# Vaaler minor: SIGN CORRECTION of the Fourier-side pointwise identity

## The defect caught here

The committed residual
`MathExtras.NumberTheory.Analysis.VaalerCesaroFourierSide.GCesFTeqJhatMinusRavg`
asserts the pointwise Fourier identity

    `𝓕(gCes M)  =ᵐ  vaalerJCcont  −  Ravg M`     (committed: MINUS).

A direct numerical computation of the **genuine** integral Fourier transform of
`gReal M = ½·(cesaroCore M)′ + ½·tailFn′` (the real function underlying `gCes M`) against
`vaalerJCcont ± Ravg M`, at `M = 20, 80` and several `t ∈ (0,1)`, shows the committed sign is
WRONG: the integral transform matches `vaalerJCcont + Ravg M` (residual ≈ `10⁻⁴`, the
finite-difference error), while `vaalerJCcont − Ravg M` is off by `10⁻²`–`10⁻¹`.

The algebra confirms the `+` sign.  Per `HNcore_deriv_FT_eq`, the `N`-level derivative
transform has oscillatory part

    `π i t · 𝓕(HNcore N)(t)|_osc  =  fejerTriangle t · (π i t)·(i·cos(π(2N+1)t)/sin(π t))
                                  =  − fejerTriangle t · π t · cos(π(2N+1)t)/sin(π t).`

Averaging over `N < M`, dividing by `M`, and using
`(1/M)∑_{N<M} cos((2N+1)πt) = sin(2πMt)/(2M·sin(πt))`
(`VaalerCesaroDirichletSum.sum_cos_odd_eq`) gives the averaged oscillatory FT term

    `− fejerTriangle t · π t · sin(2πMt)/(2M·sin(πt)²)  =  Ravg M t`     (SAME sign as `Ravg`).

Hence `𝓕(½·(cesaroCore M)′)|_osc = + Ravg M`, and the total derivative-level transform is the
principal `Ĵ`-part PLUS `Ravg M`, i.e. `𝓕(gCes M) = vaalerJCcont + Ravg M`.

## Why the wall still closes (the sign is IMMATERIAL downstream)

The committed reduction `VaalerCesaroFourierSide.tendsto_fourierSide_of_identity` only ever uses
the pointwise identity to rewrite `𝓕(gCes M) − vaalerJCcont` as `±(Ravg M)` and then takes
`eLpNorm`, which is invariant under negation (`eLpNorm_neg`).  So both the committed (wrong) `−`
and the correct `+` sign produce the **same** `eLpNorm → 0` conclusion via the PROVEN
`tendsto_eLpNorm_Ravg`.

This leaf therefore (i) states the **correctly-signed** residual `GCesFTeqJhatPlusRavg`, and
(ii) re-proves the full wall-closing reduction from it — `gcFTeqJhat_of_two_residuals_corrected`
— so the minor `H′ = 2J` wall rests on the analytically correct identity, not the mis-signed one.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `GCesFTeqJhatPlusRavg` — the corrected-sign pointwise Fourier identity (named `Prop`).
* `tendsto_fourierSide_of_identity_plus` — **PROVEN**: the corrected `+`-identity plus the
  per-`M` `L²` membership family gives the Fourier-side conjunct convergence (the sign-immaterial
  reduction, via `eLpNorm_neg` + the PROVEN `tendsto_eLpNorm_ofReal_Ravg`).
* `gcCesaroPlancherelData_of_two_residuals_corrected`,
  `gcFTeqJhat_of_two_residuals_corrected` — **PROVEN**: the corrected identity (plus
  `GCesSharpSpatialL2` and `{GIntegrable, GCBounded}`) assembles `GCCesaroPlancherelData` and the
  minor wall `GCFTeqJhat`, exactly mirroring the committed (mis-signed) chain.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.31)–(2.32).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerCesaroFTSignCorrection

open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
open MathExtras.NumberTheory.Analysis.VaalerCesaroRemainderL2
open MathExtras.NumberTheory.Analysis.VaalerCesaroFourierSide
open MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialSide
open MathExtras.NumberTheory.Analysis.VaalerCesaroPlancherelAssembly
open MathExtras.NumberTheory.Analysis.VaalerGCesMemLpDischarge
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT

/-! ## §1 — The corrected-sign pointwise transform identity -/

/-- **Named `Prop` (NEVER an `axiom`): the CORRECTED-sign `𝓕(gCes M) = Ĵ + Ravg M` identity.**

For every `M` and every `L²` membership `h : MemLp (gCes M) 2`, the representative of the
Plancherel `L²`-transform of `gCes M` agrees `a.e.` with `vaalerJCcont + (Ravg M : ℂ)`:

    `⇑(Lp.fourierTransformₗᵢ ℝ ℂ (h.toLp (gCes M)))  =ᵐ[volume]
        fun t => vaalerJCcont t + (Ravg M t : ℂ)`.

This is the **sign-corrected** replacement for the committed (mis-signed)
`VaalerCesaroFourierSide.GCesFTeqJhatMinusRavg`.  The `+` sign is forced by the algebra of
`HNcore_deriv_FT_eq` + `VaalerCesaroDirichletSum.sum_cos_odd_eq` and confirmed numerically (see
the file header). -/
def GCesFTeqJhatPlusRavg : Prop :=
  ∀ (M : ℕ) (h : MemLp (gCes M) 2 (volume : Measure ℝ)),
    (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
        (h.toLp (gCes M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] fun t : ℝ => vaalerJCcont t + (Ravg M t : ℂ)

/-! ## §2 — The sign-immaterial Fourier-side reduction -/

/-- **PROVEN — the Fourier-side conjunct of `GCCesaroPlancherelData`, from the CORRECTED
`+`-identity.**

Identical structure to the committed `VaalerCesaroFourierSide.tendsto_fourierSide_of_identity`,
but driven by the correctly-signed `GCesFTeqJhatPlusRavg`.  For each `M`, the integrand
`⇑(𝓕 (gCes M)) − vaalerJCcont` is `a.e.` equal to `+(Ravg M · : ℂ)` (subtract `vaalerJCcont`
from the `+`-identity), so its `eLpNorm` equals `eLpNorm (fun t => (Ravg M t : ℂ))`
(= `eLpNorm (Ravg M)` by the `ofReal` isometry), which `→ 0` by the PROVEN
`tendsto_eLpNorm_ofReal_Ravg`.  The sign of `Ravg` is immaterial because `eLpNorm` is invariant
under negation, so this matches the committed reduction verbatim. -/
theorem tendsto_fourierSide_of_identity_plus
    (hMemCes : ∀ M, MemLp (gCes M) 2 (volume : Measure ℝ))
    (hId : GCesFTeqJhatPlusRavg) :
    Filter.Tendsto
      (fun M => eLpNorm
        ((fun t : ℝ =>
            (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
              ((hMemCes M).toLp (gCes M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) t
              - vaalerJCcont t))
        2 (volume : Measure ℝ))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hcongr : ∀ M : ℕ,
      eLpNorm
        ((fun t : ℝ =>
            (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
              ((hMemCes M).toLp (gCes M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) t
              - vaalerJCcont t))
        2 (volume : Measure ℝ)
        = eLpNorm (fun t : ℝ => (Ravg M t : ℂ)) 2 (volume : Measure ℝ) := by
    intro M
    have hae := hId M (hMemCes M)
    -- rewrite the integrand a.e. to `+(Ravg M ·)`
    have hstep :
        (fun t : ℝ =>
            (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
              ((hMemCes M).toLp (gCes M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) t
              - vaalerJCcont t)
          =ᵐ[volume] fun t : ℝ => (Ravg M t : ℂ) := by
      filter_upwards [hae] with t ht
      rw [ht]
      ring
    rw [eLpNorm_congr_ae hstep]
  simp_rw [hcongr]
  exact tendsto_eLpNorm_ofReal_Ravg

#print axioms tendsto_fourierSide_of_identity_plus

/-! ## §3 — The wall, re-derived from the corrected identity -/

/-- **PROVEN — `GCCesaroPlancherelData` from the CORRECTED identity + the sharp spatial limit.**

Mirrors `VaalerCesaroPlancherelAssembly.gcCesaroPlancherelData_of_residuals`, but the Fourier
conjunct is supplied by the sign-corrected `tendsto_fourierSide_of_identity_plus`.  The per-`M`
`L²` membership is the discharged `memLp_gCes_two_all`. -/
theorem gcCesaroPlancherelData_of_residuals_corrected
    (hMemGC : MemLp GC 2 (volume : Measure ℝ))
    (hMemCes : ∀ M, MemLp (gCes M) 2 (volume : Measure ℝ))
    (hId : GCesFTeqJhatPlusRavg)
    (hSharp : GCesSharpSpatialL2) :
    GCCesaroPlancherelData := by
  refine ⟨hMemCes, ?_, ?_⟩
  · exact tendsto_spatialSide_of_sharp hMemGC hSharp
  · exact tendsto_fourierSide_of_identity_plus hMemCes hId

#print axioms gcCesaroPlancherelData_of_residuals_corrected

/-- **PROVEN — `GCCesaroPlancherelData` from the CORRECTED identity, per-`M` membership
discharged.**  As above, with `hMemCes` supplied by the discharged `memLp_gCes_two_all`. -/
theorem gcCesaroPlancherelData_of_two_residuals_corrected
    (hMemGC : MemLp GC 2 (volume : Measure ℝ))
    (hId : GCesFTeqJhatPlusRavg)
    (hSharp : GCesSharpSpatialL2) :
    GCCesaroPlancherelData :=
  gcCesaroPlancherelData_of_residuals_corrected hMemGC memLp_gCes_two_all hId hSharp

#print axioms gcCesaroPlancherelData_of_two_residuals_corrected

/-- **PROVEN — `GCFTeqJhat` (the minor `H′ = 2J` wall) from the CORRECTED identity.**

`{GIntegrable, GCBounded}` plus the sign-corrected Fourier identity `GCesFTeqJhatPlusRavg` and
the sharp spatial `L²`-limit `GCesSharpSpatialL2` give the deep minor residual `GCFTeqJhat`
(`𝓕(½H′) = Ĵ`, Vaaler eq. (2.31)→(2.32)).  Chains
`gcCesaroPlancherelData_of_two_residuals_corrected` with the committed `gcFTeqJhat_of_cesaro`. -/
theorem gcFTeqJhat_of_two_residuals_corrected
    (hGint : GIntegrable) (hBdd : GCBounded)
    (hId : GCesFTeqJhatPlusRavg)
    (hSharp : GCesSharpSpatialL2) :
    GCFTeqJhat :=
  gcFTeqJhat_of_cesaro hGint hBdd
    (gcCesaroPlancherelData_of_two_residuals_corrected
      (memLp_GC_two_of hGint hBdd) hId hSharp)

#print axioms gcFTeqJhat_of_two_residuals_corrected

end MathExtras.NumberTheory.Analysis.VaalerCesaroFTSignCorrection
