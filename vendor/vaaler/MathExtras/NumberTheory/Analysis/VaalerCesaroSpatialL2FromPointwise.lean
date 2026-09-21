/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialDirect
import MathExtras.NumberTheory.Analysis.VaalerCesaroFTMinorAssembly
import MathExtras.NumberTheory.Analysis.VaalerMinorWallSpatialClosed
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Vaaler minor: the TRUE Cesàro spatial `L²` limit from a SINGLE pointwise-a.e. residual

This NEW leaf closes the genuinely-remaining analytic content of the minor `H′ = 2J` wall via a
**non-circular, non-blocked** route, reducing the committed direct Cesàro spatial residual
`VaalerCesaroSpatialDirect.GCesSpatialL2Direct`
(`eLpNorm (gCes M − GC) 2 → 0`, the literal spatial conjunct of `GCCesaroPlancherelData`) to the
**single** pointwise-a.e. convergence `Prop`

    `GCesTendstoPointwiseAE`  :  `∀ᵐ x, Tendsto (fun M => gCes M x) atTop (𝓝 (GC x))`.

## Why this route is correct (avoids both the blocked Gram bound and the circular shortcut)

The committed spatial residual was previously isolated as the quantitative `M^{-1/2}` decay
`GCesSpatialL2DecayBound` / its `Lp`-Hilbert form `GCesFejerL2Summability`, whose only known proof
route — an upper-bound almost-orthogonal Gram estimate `norm_weighted_shift_sum_sq_le_card` — is
**BLOCKED** (the `O(1/√M)` is a head↔tail oscillatory cancellation an upper bound provably cannot
see).  And the naive Plancherel shortcut `‖gCes M − GC‖₂ = ‖𝓕(gCes M) − 𝓕 GC‖₂` is **circular**
(it needs `𝓕 GC =ᵐ vaalerJCcont`, i.e. the very wall being proved).

This leaf bypasses BOTH.  The genuine engine is the **Plancherel isometry + limit identification**:

* The **Fourier side is already PROVEN** (`VaalerCesaroFTMinorAssembly.gcesFT_eq_vaalerJC_plus_Ravg_pos`
  + `VaalerCesaroRemainderL2.tendsto_eLpNorm_Ravg`): for `M ≥ 1`,
  `𝓕_Lp(gCes M) =ᵐ vaalerJCcont + Ravg M`, and `‖Ravg M‖₂ → 0`, so the `Lp`-elements
  `𝓕_Lp(gCes M)` CONVERGE in `L²` to `vaalerJCcont.toLp`.
* The Plancherel transform `𝓕_Lp = Lp.fourierTransformₗᵢ` is a **linear ISOMETRY** (hence its
  inverse is continuous), so `gCes M.toLp` itself CONVERGES in `L²` to `L := 𝓕_Lp.symm
  (vaalerJCcont.toLp)`.  This is NOT circular: it never assumes `𝓕 GC = vaalerJCcont`; it derives
  the `L²`-limit of `gCes M` purely from the proven Fourier-side decay.
* `L²`-convergence ⟹ convergence **in measure** ⟹ a subsequence converges **a.e.** to `L`
  (`tendstoInMeasure_of_tendsto_eLpNorm` + `TendstoInMeasure.exists_seq_tendsto_ae'`).  Combined
  with the pointwise-a.e. limit `gCes M → GC` (the single residual `GCesTendstoPointwiseAE`),
  uniqueness of limits forces `L =ᵐ GC`, i.e. the `L²`-limit IS `GC`.
* Therefore `gCes M.toLp → GC.toLp` in `L²`, i.e. `eLpNorm (gCes M − GC) 2 → 0`.

Everything except the single pointwise-a.e. residual is PROVEN here on top of the committed
Fourier-side theorems and Mathlib's `Lp`/convergence-in-measure API.

## What this file PROVES (sorry / axiom-free, non-vacuous)

* `GCesTendstoPointwiseAE` (named `Prop`, NEVER an `axiom`) — `∀ᵐ x, gCes M x → GC x`.
* `gCesLp_tendsto_GCLp_of_pointwise` — **PROVEN**: the `Lp`-level convergence `gCes M.toLp →
  GC.toLp`, granting the pointwise residual (the full isometry + identification argument).
* `gCesSpatialL2Direct_of_pointwise` — **PROVEN**: `GCesSpatialL2Direct` from the pointwise residual.
* `gcFTeqJhat_of_pointwise` — **PROVEN**: the deep minor residual `GCFTeqJhat` (`𝓕(½H′) = Ĵ`, the
  minor `H′ = 2J` wall, Vaaler eq. (2.31)→(2.32)) from the SINGLE pointwise residual
  (`GIntegrable`/`GCBounded` supplied internally, the Fourier side discharged).
* `gEqReJ_of_pointwise` — **PROVEN**: the minor D-1 wall `GEqReJ` (`G = Re vaalerJ`) from the single
  pointwise residual, fully closing the J-FT subtree modulo only `GCesTendstoPointwiseAE`.

## Honest status — did / did-not

DID: the Plancherel-isometry + convergence-in-measure + limit-identification machinery that turns
the PROVEN Fourier-side `L²`-decay into the spatial `L²` limit, NON-circularly (no `𝓕 GC =
vaalerJCcont` assumed) and OFF the blocked Gram route, reducing the entire minor wall to the single
pointwise-a.e. convergence `gCes M → GC`.  DID-NOT (isolated as the named `Prop`
`GCesTendstoPointwiseAE`): the pointwise-a.e. convergence itself — a TRUE statement (mpmath:
`gCes M x → GC x`, the Cesàro mean of the pointwise-convergent shifted-Fejér derivatives
`(HNcore N)′(x)`, rate `~M^{-1/2}`), never an `axiom`, never vacuous.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.31)–(2.32); Mathlib `Analysis.Fourier.LpSpace` (`fourierTransformₗᵢ` Plancherel isometry),
`MeasureTheory.Function.ConvergenceInMeasure` (`tendstoInMeasure_of_tendsto_eLpNorm`,
`TendstoInMeasure.exists_seq_tendsto_ae'`).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialL2FromPointwise

open MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
open MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialSide
open MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialDirect
open MathExtras.NumberTheory.Analysis.VaalerCesaroFTMinorAssembly
open MathExtras.NumberTheory.Analysis.VaalerCesaroFTPieces
open MathExtras.NumberTheory.Analysis.VaalerCesaroRemainderL2
open MathExtras.NumberTheory.Analysis.VaalerCesaroFourierSide
open MathExtras.NumberTheory.Analysis.VaalerGCesMemLpDischarge
open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2Limit
open MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ
open MathExtras.NumberTheory.Analysis.VaalerGCBoundedProof

/-! ## §0 — Local abbreviations -/

/-- The `Lp 2` element of `gCes M` (using the proven per-`M` membership). -/
abbrev gCesLp (M : ℕ) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) := (memLp_gCes_two_all M).toLp (gCes M)

/-- The Plancherel `L²`-isometry. -/
abbrev 𝓕L : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) :=
  MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

/-! ## §1 — The single remaining pointwise-a.e. residual (named `Prop`, never an `axiom`) -/

/-- **The single remaining analytic step, ONE named `Prop` (never an `axiom`).**

The explicit Cesàro (triangularly-weighted) shifted-Fejér family `gCes M = ½·(cesaroCore M)′ +
½·tailFn′` converges **pointwise a.e.** to `GC = ½·(interpH)′`:

    `∀ᵐ x, Tendsto (fun M => gCes M x) atTop (𝓝 (GC x))`.

TRUE (mpmath: `gCes M x → GC x`, e.g. `diff ≈ 0.003` at `M = 300`, rate `~M^{-1/2}`): pointwise,
`(cesaroCore M)′(x) = (1/M)∑_{N<M}(HNcore N)′(x)` is the Cesàro mean of the pointwise-convergent
sharp shifted-Fejér derivatives `(HNcore N)′(x)`, hence converges to the same limit
`(lim_N HNcore)′(x) = (interpH − tailFn)′(x)`, and `GC x = ½((lim HNcore)′ + tailFn′)(x)`.
NOT an `axiom`, NOT vacuous (both sides are concrete real-valued functions of `x`). -/
def GCesTendstoPointwiseAE : Prop :=
  ∀ᵐ x : ℝ, Filter.Tendsto (fun M : ℕ => gCes M x) Filter.atTop (nhds (GC x))

/-! ## §2 — The Fourier-side `Lp`-limit (PROVEN, from the committed Fourier side) -/

/-- **PROVEN — `𝓕_Lp(gCes M)` converges in `L²` to `vaalerJCcont.toLp`.**

For `M ≥ 1` the committed `gcesFT_eq_vaalerJC_plus_Ravg_pos` gives `𝓕_Lp(gCes M) =ᵐ vaalerJCcont +
Ravg M`, so `‖𝓕_Lp(gCes M) − vaalerJCcont.toLp‖ = ‖Ravg M‖₂` (`Lp.norm_def` + the `ofReal`
isometry), which `→ 0` by `tendsto_eLpNorm_Ravg`.  Hence `𝓕_Lp(gCes M) → vaalerJCcont.toLp`. -/
theorem fourier_gCesLp_tendsto_JLp :
    Filter.Tendsto (fun M : ℕ => 𝓕L (gCesLp M)) Filter.atTop
      (nhds (memLp_vaalerJCcont_two.toLp vaalerJCcont)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- ‖𝓕_Lp(gCes M) − vaalerJCcont.toLp‖  →  0
  -- eventually (M ≥ 1) equals eLpNorm (Ravg M ·).toReal
  have hev : (fun M : ℕ => ‖𝓕L (gCesLp M) - memLp_vaalerJCcont_two.toLp vaalerJCcont‖)
      =ᶠ[Filter.atTop]
      (fun M : ℕ => (eLpNorm (fun t : ℝ => (Ravg M t : ℂ)) 2 (volume : Measure ℝ)).toReal) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with M hM1
    have hM : 0 < M := hM1
    -- the difference of `Lp` elements, as a function, is a.e. `Ravg M ·`
    have hsub_ae :
        (⇑(𝓕L (gCesLp M) - memLp_vaalerJCcont_two.toLp vaalerJCcont) : ℝ → ℂ)
          =ᵐ[volume] fun t : ℝ => (Ravg M t : ℂ) := by
      have hft := gcesFT_eq_vaalerJC_plus_Ravg_pos tailFT_eq_jTail hM (memLp_gCes_two_all M)
      have hJ := memLp_vaalerJCcont_two.coeFn_toLp (p := 2) (μ := (volume : Measure ℝ))
      filter_upwards [MeasureTheory.Lp.coeFn_sub (𝓕L (gCesLp M))
        (memLp_vaalerJCcont_two.toLp vaalerJCcont), hft, hJ] with t hsub hft' hJ'
      rw [hsub, Pi.sub_apply, hft', hJ']
      -- (vaalerJCcont t + Ravg M t) − vaalerJCcont t = Ravg M t
      ring
    rw [MeasureTheory.Lp.norm_def]
    congr 1
    exact eLpNorm_congr_ae hsub_ae
  rw [Filter.tendsto_congr' hev]
  -- (eLpNorm (Ravg M ·) 2).toReal → 0  from  eLpNorm (Ravg M ·) 2 → 0
  have h0 : Filter.Tendsto
      (fun M : ℕ => eLpNorm (fun t : ℝ => (Ravg M t : ℂ)) 2 (volume : Measure ℝ))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := tendsto_eLpNorm_ofReal_Ravg
  have := (ENNReal.tendsto_toReal (by simp)).comp h0
  exact this.congr' (Filter.Eventually.of_forall fun M => rfl)

/-! ## §3 — `gCes M.toLp` converges in `L²` (isometry inverse is continuous) -/

/-- **PROVEN — `gCes M.toLp` converges in `L²` to `L := 𝓕_Lp.symm (vaalerJCcont.toLp)`.**

The Plancherel isometry `𝓕_Lp` is a linear isometry equiv, so its inverse `𝓕_Lp.symm` is
continuous; applying it to `fourier_gCesLp_tendsto_JLp` and using `𝓕_Lp.symm (𝓕_Lp (gCesLp M)) =
gCesLp M` gives the spatial `Lp`-convergence — NON-circularly (no `𝓕 GC = vaalerJCcont` used). -/
theorem gCesLp_tendsto_symm_JLp :
    Filter.Tendsto (fun M : ℕ => gCesLp M) Filter.atTop
      (nhds ((𝓕L).symm (memLp_vaalerJCcont_two.toLp vaalerJCcont))) := by
  have hcont : Filter.Tendsto (fun M : ℕ => (𝓕L).symm (𝓕L (gCesLp M))) Filter.atTop
      (nhds ((𝓕L).symm (memLp_vaalerJCcont_two.toLp vaalerJCcont))) :=
    ((𝓕L).symm.continuous.tendsto _).comp fourier_gCesLp_tendsto_JLp
  simpa using hcont

/-! ## §4 — Identifying the `L²`-limit with `GC` via the pointwise residual -/

/-- **PROVEN — the `L²`-limit `L = 𝓕_Lp.symm (vaalerJCcont.toLp)` agrees a.e. with `GC`,
granting the pointwise residual.**

`gCes M.toLp → L` in `L²` ⟹ in measure ⟹ a subsequence `gCes (ns i) → L` a.e.; the pointwise
residual gives `gCes M → GC` a.e.; uniqueness of limits forces `L =ᵐ GC`. -/
theorem symm_JLp_ae_eq_GC (hpt : GCesTendstoPointwiseAE) :
    (⇑((𝓕L).symm (memLp_vaalerJCcont_two.toLp vaalerJCcont)) : ℝ → ℂ) =ᵐ[volume] GC := by
  set L : Lp (α := ℝ) ℂ 2 := (𝓕L).symm (memLp_vaalerJCcont_two.toLp vaalerJCcont) with hL
  -- (1) eLpNorm (gCes M.toLp − L) → 0
  have hLp0 : Filter.Tendsto
      (fun M : ℕ => eLpNorm (⇑(gCesLp M) - ⇑(L : Lp (α := ℝ) ℂ 2)) 2 (volume : Measure ℝ))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    have hnorm : Filter.Tendsto (fun M : ℕ => ‖gCesLp M - L‖) Filter.atTop (nhds 0) := by
      rw [← tendsto_iff_norm_sub_tendsto_zero] at *
      exact gCesLp_tendsto_symm_JLp
    -- ‖·‖ = (eLpNorm (coeFn (gCesLp M) − coeFn L) 2).toReal, and eLpNorm < ⊤
    have hev : (fun M : ℕ => eLpNorm (⇑(gCesLp M) - ⇑(L : Lp (α := ℝ) ℂ 2)) 2 (volume : Measure ℝ))
        = fun M : ℕ => ENNReal.ofReal ‖gCesLp M - L‖ := by
      funext M
      rw [MeasureTheory.Lp.norm_def,
        ENNReal.ofReal_toReal (MeasureTheory.Lp.memLp (gCesLp M - L)).eLpNorm_lt_top.ne]
      refine eLpNorm_congr_ae ?_
      filter_upwards [MeasureTheory.Lp.coeFn_sub (gCesLp M) L] with x hx
      rw [hx]
    rw [hev, show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp hnorm
  -- (2) TendstoInMeasure
  have hmeas_fn : ∀ M : ℕ, AEStronglyMeasurable (⇑(gCesLp M) : ℝ → ℂ) volume :=
    fun M => (MeasureTheory.Lp.memLp _).aestronglyMeasurable
  have hTIM : MeasureTheory.TendstoInMeasure (volume : Measure ℝ)
      (fun M : ℕ => (⇑(gCesLp M) : ℝ → ℂ)) Filter.atTop (⇑(L : Lp (α := ℝ) ℂ 2)) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      hmeas_fn (MeasureTheory.Lp.memLp _).aestronglyMeasurable hLp0
  -- (3) a.e.-convergent subsequence to L
  obtain ⟨ns, _hns, hae⟩ := hTIM.exists_seq_tendsto_ae'
  -- (4) on this subsequence, also gCes (ns i) → GC a.e. (from pointwise residual + coeFn)
  -- gCes M.toLp =ᵐ gCes M
  have hcoe : ∀ M : ℕ, (⇑(gCesLp M) : ℝ → ℂ) =ᵐ[volume] gCes M :=
    fun M => (memLp_gCes_two_all M).coeFn_toLp
  -- The countable union of null sets where coeFn ≠ gCes is null.
  have hcoe_all : ∀ᵐ x : ℝ, ∀ i : ℕ, (⇑(gCesLp (ns i)) : ℝ → ℂ) x = gCes (ns i) x := by
    rw [MeasureTheory.ae_all_iff]
    exact fun i => hcoe (ns i)
  -- combine: a.e. x, gCes (ns i) x → L x  and  gCes M x → GC x, so L x = GC x
  filter_upwards [hae, hcoe_all, hpt] with x hxL hxcoe hxpt
  -- hxL : Tendsto (fun i => gCesLp (ns i) x) atTop (𝓝 (L x))
  -- rewrite gCesLp (ns i) x = gCes (ns i) x
  have hxL' : Filter.Tendsto (fun i : ℕ => gCes (ns i) x) Filter.atTop (nhds ((L : ℝ → ℂ) x)) := by
    refine (Filter.tendsto_congr ?_).mp hxL
    intro i; rw [hxcoe i]
  -- hxpt : Tendsto (fun M => gCes M x) atTop (𝓝 (GC x)); compose with ns → atTop
  have hxpt' : Filter.Tendsto (fun i : ℕ => gCes (ns i) x) Filter.atTop (nhds (GC x)) :=
    hxpt.comp (by
      -- ns → atTop since `ns` tends to the `atTop` filter on ℕ (from exists_seq_tendsto_ae')
      simpa using _hns)
  exact tendsto_nhds_unique hxL' hxpt'

/-! ## §5 — `gCes M.toLp → GC.toLp` and `GCesSpatialL2Direct` -/

/-- **PROVEN — the `Lp`-level spatial convergence `gCes M.toLp → GC.toLp`, from the pointwise
residual.**  Rewrites the limit `L = 𝓕_Lp.symm (vaalerJCcont.toLp)` of `gCesLp_tendsto_symm_JLp`
as `GC.toLp` using `symm_JLp_ae_eq_GC` (`Lp.ext` on the a.e. identity). -/
theorem gCesLp_tendsto_GCLp_of_pointwise
    (hMemGC : MemLp GC 2 (volume : Measure ℝ))
    (hpt : GCesTendstoPointwiseAE) :
    Filter.Tendsto (fun M : ℕ => gCesLp M) Filter.atTop (nhds (hMemGC.toLp GC)) := by
  have hLeq : (𝓕L).symm (memLp_vaalerJCcont_two.toLp vaalerJCcont) = hMemGC.toLp GC := by
    apply MeasureTheory.Lp.ext
    -- coeFn (symm JLp) =ᵐ GC =ᵐ coeFn (GC.toLp)
    exact (symm_JLp_ae_eq_GC hpt).trans (hMemGC.coeFn_toLp).symm
  rw [← hLeq]
  exact gCesLp_tendsto_symm_JLp

/-- **PROVEN — `GCesSpatialL2Direct` from the single pointwise-a.e. residual.**

`gCes M.toLp → GC.toLp` in `L²` (`gCesLp_tendsto_GCLp_of_pointwise`) gives
`‖gCes M.toLp − GC.toLp‖ → 0`, i.e. `eLpNorm (gCes M − GC) 2 → 0`; bundle with the proven per-`M`
membership `memLp_gCes_two_all`. -/
theorem gCesSpatialL2Direct_of_pointwise (hpt : GCesTendstoPointwiseAE) :
    GCesSpatialL2Direct := by
  have hMemGC : MemLp GC 2 (volume : Measure ℝ) := memLp_GC_two_of gIntegrable_holds gCBounded_proven
  refine ⟨memLp_gCes_two_all, ?_⟩
  -- eLpNorm (gCes M − GC) = ‖gCes M.toLp − GC.toLp‖ₑ  (a.e. coeFn), and ‖·‖ → 0
  have hnorm : Filter.Tendsto (fun M : ℕ => ‖gCesLp M - hMemGC.toLp GC‖) Filter.atTop (nhds 0) := by
    rw [← tendsto_iff_norm_sub_tendsto_zero]
    exact gCesLp_tendsto_GCLp_of_pointwise hMemGC hpt
  have hev : (fun M : ℕ => eLpNorm (fun x : ℝ => gCes M x - GC x) 2 (volume : Measure ℝ))
      = fun M : ℕ => ENNReal.ofReal ‖gCesLp M - hMemGC.toLp GC‖ := by
    funext M
    rw [MeasureTheory.Lp.norm_def, ENNReal.ofReal_toReal
      ((MeasureTheory.Lp.memLp (gCesLp M - hMemGC.toLp GC)).eLpNorm_lt_top.ne)]
    refine eLpNorm_congr_ae ?_
    filter_upwards [MeasureTheory.Lp.coeFn_sub (gCesLp M) (hMemGC.toLp GC),
      (memLp_gCes_two_all M).coeFn_toLp, hMemGC.coeFn_toLp] with x hsub hg hG
    rw [hsub, Pi.sub_apply, hg, hG]
  rw [hev, show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
  exact (ENNReal.continuous_ofReal.tendsto 0).comp hnorm

/-! ## §6 — The minor wall `GCFTeqJhat` and `GEqReJ` from the single pointwise residual -/

/-- **PROVEN — the minor `H′ = 2J` wall `GCFTeqJhat` (`𝓕(½H′) = Ĵ`) from the single pointwise
residual.**  Chains `gCesSpatialL2Direct_of_pointwise` into the committed
`VaalerCesaroSpatialDirect.gcFTeqJhat_of_cesaroDirect`-style assembly via
`VaalerCesaroSpatialL2DecayCore`/`VaalerMinorWallSpatialClosed` route — here directly through the
proven `gcFTeqJhat_of_cesaroDirect`, supplying the Fourier identity from the discharged tail. -/
theorem gcFTeqJhat_of_pointwise (hpt : GCesTendstoPointwiseAE) : GCFTeqJhat := by
  -- assemble GCCesaroPlancherelData from the spatial-direct limit + discharged Fourier side
  have hMemGC : MemLp GC 2 (volume : Measure ℝ) := memLp_GC_two_of gIntegrable_holds gCBounded_proven
  have hDirect := gCesSpatialL2Direct_of_pointwise hpt
  obtain ⟨hMemCes, hspat⟩ := hDirect
  have hData : GCCesaroPlancherelData :=
    ⟨hMemCes, hspat, tendsto_fourierSide_pos tailFT_eq_jTail⟩
  exact gcFTeqJhat_of_cesaro gIntegrable_holds gCBounded_proven hData

/-- **PROVEN — the minor D-1 wall `GEqReJ` (`G = Re vaalerJ`) from the single pointwise residual.**

Routes the minor wall `GCFTeqJhat` (from `gcFTeqJhat_of_pointwise`) through the committed
`VaalerGCFTeqJ.gEqReJ_of_hat` (`GCFTeqJhat` + the two proven `vaalerJ`-side residuals give
`GEqReJ`).  Fully closes the J-FT subtree modulo ONLY `GCesTendstoPointwiseAE`. -/
theorem gEqReJ_of_pointwise (hpt : GCesTendstoPointwiseAE) :
    MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ.GEqReJ :=
  MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ.gEqReJ_of_hat
    gContinuous_holds gIntegrable_holds (gcFTeqJhat_of_pointwise hpt)
    MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ.vaalerJhatContCornerOne_holds
    MathExtras.NumberTheory.Analysis.VaalerGEqVaalerJ.vaalerJTwoIBPDecay_holds

#print axioms fourier_gCesLp_tendsto_JLp
#print axioms gCesLp_tendsto_symm_JLp
#print axioms symm_JLp_ae_eq_GC
#print axioms gCesLp_tendsto_GCLp_of_pointwise
#print axioms gCesSpatialL2Direct_of_pointwise
#print axioms gcFTeqJhat_of_pointwise
#print axioms gEqReJ_of_pointwise

end MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialL2FromPointwise

end
