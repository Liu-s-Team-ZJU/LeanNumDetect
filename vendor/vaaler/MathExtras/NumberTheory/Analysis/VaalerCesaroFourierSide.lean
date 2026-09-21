/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCesaroRemainderL2
import MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
import AnalyticNT.Diophantine.FourierL1L2Agreement

/-!
# Vaaler minor: the Fourier-side `L²`-convergence conjunct of `GCCesaroPlancherelData`

This NEW leaf reduces the **Fourier-side** conjunct of the single remaining minor-arc residual
`GCCesaroPlancherelData`
(`MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel.GCCesaroPlancherelData`)

    `eLpNorm (⇑(Lp.fourierTransformₗᵢ ℝ ℂ ((hMemCes M).toLp (gCes M))) − vaalerJCcont) 2 → 0`

to the single **pointwise Fourier-transform identity** (named `Prop`, never an `axiom`)

    `GCesFTeqJhatMinusRavg`:
        `⇑(Lp.fourierTransformₗᵢ ℝ ℂ ((h).toLp (gCes M)))  =ᵐ[volume]
            fun t => vaalerJCcont t − (Ravg M t : ℂ)`,

where `Ravg` is the Cesàro-averaged oscillatory remainder of
`MathExtras.NumberTheory.Analysis.VaalerCesaroRemainderL2`, whose `L²`-decay to `0`
(`tendsto_eLpNorm_Ravg`) is **already PROVEN, axiom-clean**.

## The reduction (PROVEN here)

Granting `GCesFTeqJhatMinusRavg`, the integrand of the Fourier conjunct is `a.e.` equal to
`−(Ravg M · : ℂ)`, so its `eLpNorm` equals `eLpNorm (fun t => (Ravg M t : ℂ))` (the
`Complex.ofReal` isometry), which equals `eLpNorm (Ravg M)` (real), which `→ 0` by the proven
`VaalerCesaroRemainderL2.tendsto_eLpNorm_Ravg`.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `GCesFTeqJhatMinusRavg` (named `Prop`) — the pointwise `𝓕(gCes M) = Ĵ − Ravg M` identity, the
  genuine remaining analytic content (it follows from `cesaroCore_eq_average`,
  `halfDeriv_FT_eq_mul`, `HNcore_deriv_FT_eq`, `derivLevelTotal_eq_vaalerJhat`,
  `VaalerCesaroDirichletSum.sum_cos_odd_eq`, and `fourierIntegral_ae_eq_fourierTransformₗᵢ`,
  modulo the finite integrability/differentiability bookkeeping of the `cesaroCore`/`tailFn`
  derivatives — see the route notes).
* `eLpNorm_ofReal_Ravg_eq` — **PROVEN**: `eLpNorm (fun t => (Ravg M t : ℂ)) 2 = eLpNorm (Ravg M) 2`.
* `tendsto_eLpNorm_ofReal_Ravg` — **PROVEN**: the complexified remainder also `→ 0` in `L²`.
* `tendsto_fourierSide_of_identity` — **PROVEN reduction**: `GCesFTeqJhatMinusRavg` plus a
  per-`M` `L²` membership family gives the Fourier-side conjunct convergence.

## Honest status — did / did-not

DID: the genuine `L²`-vanishing of the averaged remainder (in `VaalerCesaroRemainderL2`) and the
reduction of the Fourier conjunct to the single pointwise `𝓕(gCes M) = Ĵ − Ravg M` identity.
DID-NOT (isolated as the named `Prop` `GCesFTeqJhatMinusRavg`): the pointwise transform identity
itself, whose only remaining gap is the finite integrability/differentiability bookkeeping of the
explicit `cesaroCore`/`tailFn` derivative family needed to invoke the already-PROVEN
`halfDeriv_FT_eq_mul` term-by-term.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.31)–(2.32).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerCesaroFourierSide

open MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
open MathExtras.NumberTheory.Analysis.VaalerCesaroRemainderL2
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT

/-! ## §1 — The complexified remainder also vanishes in `L²` -/

/-- **PROVEN — `eLpNorm (fun t => (Ravg M t : ℂ)) 2 = eLpNorm (Ravg M) 2`.**

The `Complex.ofReal` embedding is a norm isometry (`Complex.norm_real`), so the `eLpNorm`s of a
real function and its complexification coincide. -/
theorem eLpNorm_ofReal_Ravg_eq (M : ℕ) :
    eLpNorm (fun t : ℝ => (Ravg M t : ℂ)) 2 (volume : Measure ℝ)
      = eLpNorm (Ravg M) 2 (volume : Measure ℝ) := by
  apply eLpNorm_congr_norm_ae
  filter_upwards with t
  exact Complex.norm_real (Ravg M t)

/-- **PROVEN — the complexified averaged remainder `→ 0` in `L²`.**

Immediate from `eLpNorm_ofReal_Ravg_eq` and the proven real
`VaalerCesaroRemainderL2.tendsto_eLpNorm_Ravg`. -/
theorem tendsto_eLpNorm_ofReal_Ravg :
    Filter.Tendsto (fun M : ℕ => eLpNorm (fun t : ℝ => (Ravg M t : ℂ)) 2 (volume : Measure ℝ))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  simp_rw [eLpNorm_ofReal_Ravg_eq]
  exact tendsto_eLpNorm_Ravg

#print axioms eLpNorm_ofReal_Ravg_eq
#print axioms tendsto_eLpNorm_ofReal_Ravg

/-! ## §2 — The named pointwise transform identity (the genuine remaining content) -/

/-- **Named `Prop` (NEVER an `axiom`): the pointwise `𝓕(gCes M) = Ĵ − Ravg M` identity.**

For every `M` and every `L²` membership `h : MemLp (gCes M) 2`, the representative of the
Plancherel `L²`-transform of `gCes M` agrees `a.e.` with `vaalerJCcont − (Ravg M : ℂ)`:

    `⇑(Lp.fourierTransformₗᵢ ℝ ℂ (h.toLp (gCes M)))  =ᵐ[volume]
        fun t => vaalerJCcont t − (Ravg M t : ℂ)`.

This is the genuine remaining analytic content of the Fourier-side of `GCCesaroPlancherelData`.
It is the assembled output of the PROVEN chain
`cesaroCore_eq_average` → (FT linearity) → `halfDeriv_FT_eq_mul` → `HNcore_deriv_FT_eq` →
`derivLevelTotal_eq_vaalerJhat` (the principal `Ĵ` term) plus the Cesàro-Dirichlet sum
`VaalerCesaroDirichletSum.sum_cos_odd_eq` (the averaged remainder `Ravg M`), bridged to the
`Lp` transform by `FourierL1L2Agreement.fourierIntegral_ae_eq_fourierTransformₗᵢ` — modulo the
finite integrability/differentiability bookkeeping of the `cesaroCore`/`tailFn` derivatives. -/
def GCesFTeqJhatMinusRavg : Prop :=
  ∀ (M : ℕ) (h : MemLp (gCes M) 2 (volume : Measure ℝ)),
    (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
        (h.toLp (gCes M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] fun t : ℝ => vaalerJCcont t - (Ravg M t : ℂ)

/-! ## §3 — The reduction: the Fourier conjunct from the pointwise identity -/

/-- **PROVEN — the Fourier-side conjunct of `GCCesaroPlancherelData`**, granting the pointwise
transform identity `GCesFTeqJhatMinusRavg` and a per-`M` `L²` membership family `hMemCes`.

For each `M`, the integrand `⇑(𝓕 (gCes M)) − vaalerJCcont` is `a.e.` equal to `−(Ravg M · : ℂ)`
(subtract `vaalerJCcont` from the `GCesFTeqJhatMinusRavg` identity), so its `eLpNorm` equals
`eLpNorm (fun t => (Ravg M t : ℂ))` (= `eLpNorm (Ravg M)` by the `ofReal` isometry, and `eLpNorm`
is invariant under negation), which `→ 0` by the proven `tendsto_eLpNorm_ofReal_Ravg`. -/
theorem tendsto_fourierSide_of_identity
    (hMemCes : ∀ M, MemLp (gCes M) 2 (volume : Measure ℝ))
    (hId : GCesFTeqJhatMinusRavg) :
    Filter.Tendsto
      (fun M => eLpNorm
        ((fun t : ℝ =>
            (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
              ((hMemCes M).toLp (gCes M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) t
              - vaalerJCcont t))
        2 (volume : Measure ℝ))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  -- each integrand `=ᵐ -(Ravg M ·)`, so its eLpNorm = eLpNorm (Ravg M ·)
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
    -- rewrite the integrand a.e. to `-(Ravg M ·)`
    have hstep :
        (fun t : ℝ =>
            (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
              ((hMemCes M).toLp (gCes M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) t
              - vaalerJCcont t)
          =ᵐ[volume] fun t : ℝ => -(Ravg M t : ℂ) := by
      filter_upwards [hae] with t ht
      rw [ht]
      ring
    rw [eLpNorm_congr_ae hstep]
    -- eLpNorm of `-(Ravg M ·)` equals eLpNorm of `(Ravg M ·)`
    exact eLpNorm_neg _ _ _
  simp_rw [hcongr]
  exact tendsto_eLpNorm_ofReal_Ravg

#print axioms tendsto_fourierSide_of_identity

end MathExtras.NumberTheory.Analysis.VaalerCesaroFourierSide
