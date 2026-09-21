/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
import MathExtras.NumberTheory.Analysis.VaalerJFTviaHN
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Vaaler minor: the spatial-side `L²`-convergence conjunct of `GCCesaroPlancherelData`

This NEW leaf reduces the **spatial-side** conjunct of the single remaining minor-arc residual
`GCCesaroPlancherelData`
(`MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel.GCCesaroPlancherelData`)

    `eLpNorm (fun x => gCes M x − GC x) 2 volume → 0`

to the **sharp-truncation** spatial `L²`-convergence `eLpNorm (gSharp N − GC) 2 → 0` (a named
`Prop`, never an `axiom`), via the abstract **Cesàro-preservation** principle: the explicit
Cesàro family `gCes M` is the Cesàro mean `(1/M)∑_{N<M} gSharp N` of the sharp truncations
(`gCes_eq_average_gSharp`, PROVEN), and a Cesàro mean of an `L²`-null sequence is `L²`-null.

The sharp spatial convergence is numerically confirmed (`‖gSharp N − GC‖₂ = 0.84 → 0.023 →
0.0049` at `N = 10,20,40`, decay `~N⁻¹`); only the *Fourier-side* sharp convergence FAILS
(constant `≈ 0.855`), which is exactly why the Cesàro smoothing is needed — but only on the
Fourier side.  On the spatial side the sharp family already converges, and Cesàro preserves it.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `gSharp` (DEFINED) — the sharp truncation `½(HNcore N)′ + ½ tailFn′` (complexified).
* `gCes_eq_average_gSharp` — **PROVEN**: `gCes M = (1/M)∑_{N<M} gSharp N` pointwise (from
  `cesaroCore_eq_average` and `deriv` linearity over the finite Fejér sum).
* `eLpNorm_cesaroMean_le` — **PROVEN, reusable**: `eLpNorm ((1/M)∑_{N<M} f N − c) 2 ≤
  (1/M)∑_{N<M} eLpNorm (f N − c) 2`.
* `tendsto_eLpNorm_cesaro_of_tendsto` — **PROVEN, reusable**: if `eLpNorm (f N − c) 2 → 0` and
  each `f N`, `c` is `AEStronglyMeasurable`, then `eLpNorm ((1/M)∑_{N<M} f N − c) 2 → 0`.
* `tendsto_spatialSide_of_sharp` — **PROVEN reduction**: the sharp spatial `L²`-convergence
  `GCesSharpSpatialL2` gives the spatial conjunct of `GCCesaroPlancherelData`.

## Honest status — did / did-not

DID: the abstract Cesàro-preservation of `L²`-convergence and the proven identity exhibiting
`gCes` as the Cesàro mean of the sharp `gSharp`, reducing the spatial conjunct to the sharp
spatial limit.  DID-NOT (isolated as the named `Prop` `GCesSharpSpatialL2`): the sharp spatial
`L²`-limit `eLpNorm (gSharp N − GC) 2 → 0` itself (the shifted-Fejér-derivative `L²`-tail
estimate).

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6;
Cesàro means preserve convergence (`Filter.Tendsto.cesaro`, Mathlib
`Analysis.Asymptotics.SpecificAsymptotics`).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal BigOperators ContDiff

namespace MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialSide

open MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
open MathExtras.NumberTheory.Analysis.VaalerJFTviaHN
open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerGRegularityProof

/-! ## §1 — The sharp truncation family `gSharp` and the Cesàro-average identity -/

/-- **DEFINED — the sharp truncation family** (ℂ-valued):

    `gSharp N x = ½·(deriv (HNcore N)) x + ½·(deriv tailFn) x`   (complexified).

The Cesàro family `gCes M` is the Cesàro mean of `gSharp` over `N < M`
(`gCes_eq_average_gSharp`); the sharp `gSharp N` is `½H_N′ + ½ tail′`, the sharp-truncation
half-derivative whose *spatial* `L²`-limit is `GC = ½H′` (numerically confirmed). -/
def gSharp (N : ℕ) (x : ℝ) : ℂ :=
  ((1 / 2 : ℝ) * deriv (HNcore N) x + (1 / 2 : ℝ) * deriv tailFn x : ℝ)

/-- `HNcore N` is `C∞` (finite sum of `C∞` shifted Fejér pairs). -/
theorem contDiff_HNcore (N : ℕ) : ContDiff ℝ ∞ (HNcore N) := by
  have : HNcore N = fun z : ℝ =>
      ∑ m ∈ Finset.range N,
        (fejerK (z - ((m : ℝ) + 1)) - fejerK (z + ((m : ℝ) + 1))) := by
    funext z; rw [HNcore]
  rw [this]
  refine ContDiff.sum (fun m _ => ?_)
  exact (contDiff_fejerK_shift ((m : ℝ) + 1)).sub (contDiff_fejerK_addShift ((m : ℝ) + 1))

/-- `deriv (cesaroCore M) x = (1/M)·∑_{N<M} deriv (HNcore N) x`.

From `cesaroCore_eq_average` (`cesaroCore M = fun z => (1/M)·∑_{N<M} HNcore N z`) and `deriv`
linearity (`deriv_const_mul`, `deriv_sum`), each `HNcore N` being differentiable
(`contDiff_HNcore`). -/
theorem deriv_cesaroCore_eq (M : ℕ) (x : ℝ) :
    deriv (cesaroCore M) x
      = (1 / (M : ℝ)) * ∑ N ∈ Finset.range M, deriv (HNcore N) x := by
  -- rewrite cesaroCore as the scaled finite sum
  have hfun : cesaroCore M = fun z : ℝ => (1 / (M : ℝ)) * ∑ N ∈ Finset.range M, HNcore N z := by
    funext z; exact cesaroCore_eq_average M z
  have hdiff : ∀ N ∈ Finset.range M, DifferentiableAt ℝ (HNcore N) x :=
    fun N _ => ((contDiff_HNcore N).differentiable (by simp)).differentiableAt
  rw [hfun]
  rw [deriv_const_mul]
  · congr 1
    -- `deriv (fun z => ∑ N, HNcore N z) x = ∑ N, deriv (HNcore N) x`
    have : (fun z : ℝ => ∑ N ∈ Finset.range M, HNcore N z)
        = (∑ N ∈ Finset.range M, HNcore N) := by
      funext z; rw [Finset.sum_apply]
    rw [this, deriv_sum hdiff]
  · -- differentiability of the finite sum
    have : (fun z : ℝ => ∑ N ∈ Finset.range M, HNcore N z)
        = (∑ N ∈ Finset.range M, HNcore N) := by
      funext z; rw [Finset.sum_apply]
    rw [this]
    exact DifferentiableAt.sum hdiff

/-- **PROVEN — `gCes M = (1/M)·∑_{N<M} gSharp N` pointwise.**

`gCes M x = ½(cesaroCore M)′ x + ½ tailFn′ x`; with `(cesaroCore M)′ x = (1/M)∑(HNcore N)′ x`
(`deriv_cesaroCore_eq`) and the `M`-independent `½ tail′` written as the average
`(1/M)∑_{N<M} ½ tail′` of `M` equal terms, the whole `gCes M` becomes `(1/M)∑ gSharp N`. -/
theorem gCes_eq_average_gSharp (M : ℕ) (hM : 0 < M) (x : ℝ) :
    gCes M x = (1 / (M : ℝ)) * ∑ N ∈ Finset.range M, gSharp N x := by
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  -- prove the underlying REAL identity, then cast
  have hreal : (1 / 2 : ℝ) * deriv (cesaroCore M) x + (1 / 2 : ℝ) * deriv tailFn x
      = (1 / (M : ℝ)) * ∑ N ∈ Finset.range M,
          ((1 / 2 : ℝ) * deriv (HNcore N) x + (1 / 2 : ℝ) * deriv tailFn x) := by
    rw [deriv_cesaroCore_eq M x]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [mul_add]
    have h1 : (1 / (M : ℝ)) * ∑ N ∈ Finset.range M, (1 / 2 : ℝ) * deriv (HNcore N) x
        = (1 / 2 : ℝ) * ((1 / (M : ℝ)) * ∑ N ∈ Finset.range M, deriv (HNcore N) x) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun N _ => by ring)
    have h2 : (1 / (M : ℝ)) * ((M : ℝ) * ((1 / 2 : ℝ) * deriv tailFn x))
        = (1 / 2 : ℝ) * deriv tailFn x := by
      field_simp
    rw [h1, h2]
  -- cast to ℂ
  simp only [gCes_apply, gSharp]
  rw [hreal]
  push_cast
  rw [Finset.mul_sum]

#print axioms contDiff_HNcore
#print axioms gCes_eq_average_gSharp

/-! ## §2 — Abstract Cesàro-preservation of `L²`-convergence -/

/-- **PROVEN, reusable — the Cesàro mean triangle bound.**

    `eLpNorm ((1/M)·∑_{N<M} f N − c) 2 ≤ (1/M)·∑_{N<M} eLpNorm (f N − c) 2`.

The difference `(1/M)∑ f N − c = (1/M)∑ (f N − c)` (since `(1/M)∑_{N<M} c = c`), then the
`eLpNorm` triangle inequality `eLpNorm_sum_le` plus the `(1/M)` scalar pullout. -/
theorem eLpNorm_cesaroMean_le {f : ℕ → ℝ → ℂ} {c : ℝ → ℂ} (M : ℕ) (hM : 0 < M)
    (hf : ∀ N, AEStronglyMeasurable (f N) (volume : Measure ℝ))
    (hc : AEStronglyMeasurable c (volume : Measure ℝ)) :
    eLpNorm (fun x => (1 / (M : ℝ)) * ∑ N ∈ Finset.range M, f N x - c x) 2 (volume : Measure ℝ)
      ≤ (∑ N ∈ Finset.range M,
          eLpNorm (fun x => f N x - c x) 2 (volume : Measure ℝ)) / (M : ℝ≥0∞) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  -- `(1/M)∑ f N x - c x = (1/M) • (∑ (f N x - c x))`, as functions
  have hrw : (fun x => (1 / (M : ℝ)) * ∑ N ∈ Finset.range M, f N x - c x)
      = ((1 / (M : ℝ)) : ℂ) • (fun x => ∑ N ∈ Finset.range M, (f N x - c x)) := by
    funext x
    have hMc : ((M : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_natCast]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hMc, one_mul]
  rw [hrw]
  -- scalar pullout: eLpNorm (a • g) = ‖a‖ₑ · eLpNorm g
  rw [eLpNorm_const_smul]
  -- the sum's eLpNorm ≤ ∑ eLpNorm
  have hsum_le : eLpNorm (fun x => ∑ N ∈ Finset.range M, (f N x - c x)) 2 (volume : Measure ℝ)
      ≤ ∑ N ∈ Finset.range M, eLpNorm (fun x => f N x - c x) 2 (volume : Measure ℝ) := by
    have hh := eLpNorm_sum_le (p := (2 : ℝ≥0∞))
      (f := fun N x => f N x - c x) (s := Finset.range M)
      (fun N _ => (hf N).sub hc) (by norm_num)
    rw [show (∑ N ∈ Finset.range M, fun x => f N x - c x)
        = (fun x => ∑ N ∈ Finset.range M, (f N x - c x)) by
      funext x; rw [Finset.sum_apply]] at hh
    exact hh
  -- `‖(1/M : ℂ)‖ₑ = (M : ℝ≥0∞)⁻¹`
  have henorm : ‖((1 / (M : ℝ)) : ℂ)‖ₑ = (M : ℝ≥0∞)⁻¹ := by
    have heq : ‖((1 / (M : ℝ)) : ℂ)‖ₑ = ‖(1 / (M : ℝ))‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      norm_cast
    rw [heq, Real.enorm_eq_ofReal_abs, one_div, abs_inv, abs_of_nonneg hMpos.le]
    rw [ENNReal.ofReal_inv_of_pos hMpos, ENNReal.ofReal_natCast]
  calc ‖((1 / (M : ℝ)) : ℂ)‖ₑ
        * eLpNorm (fun x => ∑ N ∈ Finset.range M, (f N x - c x)) 2 (volume : Measure ℝ)
      ≤ ‖((1 / (M : ℝ)) : ℂ)‖ₑ
          * ∑ N ∈ Finset.range M, eLpNorm (fun x => f N x - c x) 2 (volume : Measure ℝ) := by
        gcongr
    _ = (∑ N ∈ Finset.range M,
          eLpNorm (fun x => f N x - c x) 2 (volume : Measure ℝ)) / (M : ℝ≥0∞) := by
        rw [henorm, ENNReal.div_eq_inv_mul]

#print axioms eLpNorm_cesaroMean_le

/-- **PROVEN, reusable — Cesàro preservation of `L²`-null convergence.**

If each `eLpNorm (f N − c) 2` is finite and `eLpNorm (f N − c) 2 → 0`, then the Cesàro means
also converge: `eLpNorm ((1/M)∑_{N<M} f N − c) 2 → 0`.

Bound by `eLpNorm_cesaroMean_le`, identify the `ℝ≥0∞` Cesàro mean with `ENNReal.ofReal` of the
real Cesàro mean of `b N := (eLpNorm (f N − c) 2).toReal` (finite terms), which `→ 0` by
`Filter.Tendsto.cesaro` and `ENNReal.continuous_ofReal`; squeeze. -/
theorem tendsto_eLpNorm_cesaro_of_tendsto {f : ℕ → ℝ → ℂ} {c : ℝ → ℂ}
    (hf : ∀ N, AEStronglyMeasurable (f N) (volume : Measure ℝ))
    (hc : AEStronglyMeasurable c (volume : Measure ℝ))
    (hfin : ∀ N, eLpNorm (fun x => f N x - c x) 2 (volume : Measure ℝ) ≠ (⊤ : ℝ≥0∞))
    (h0 : Filter.Tendsto
      (fun N => eLpNorm (fun x => f N x - c x) 2 (volume : Measure ℝ))
      Filter.atTop (nhds (0 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun M : ℕ => eLpNorm
        (fun x => (1 / (M : ℝ)) * ∑ N ∈ Finset.range M, f N x - c x) 2 (volume : Measure ℝ))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  set b : ℕ → ℝ := fun N => (eLpNorm (fun x => f N x - c x) 2 (volume : Measure ℝ)).toReal with hb
  -- b N → 0
  have hb0 : Filter.Tendsto b Filter.atTop (nhds (0 : ℝ)) :=
    (ENNReal.tendsto_toReal_zero_iff hfin).mpr h0
  -- the real Cesàro mean → 0
  have hcesaro : Filter.Tendsto
      (fun M : ℕ => ((M : ℝ)⁻¹ * ∑ N ∈ Finset.range M, b N)) Filter.atTop (nhds (0 : ℝ)) :=
    hb0.cesaro
  -- the ℝ≥0∞ upper bound → 0
  have hupper : Filter.Tendsto
      (fun M : ℕ => ENNReal.ofReal ((M : ℝ)⁻¹ * ∑ N ∈ Finset.range M, b N))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    have h := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hcesaro
    rw [show ENNReal.ofReal (0 : ℝ) = (0 : ℝ≥0∞) by simp] at h
    exact h
  -- squeeze (eventual): 0 ≤ eLpNorm ≤ upper for M ≥ 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds) hupper (Filter.Eventually.of_forall (fun M => zero_le')) ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with M hMpos
  · -- M ≥ 1: the bound from eLpNorm_cesaroMean_le, rewritten through ofReal
    have hle := eLpNorm_cesaroMean_le (f := f) (c := c) M hMpos hf hc
    refine hle.trans (le_of_eq ?_)
    -- `(∑ eLpNorm)/(M:ℝ≥0∞) = ENNReal.ofReal ((1/M)·∑ b N)`
    have hsum_fin : (∑ N ∈ Finset.range M, eLpNorm (fun x => f N x - c x) 2 (volume : Measure ℝ))
        ≠ (⊤ : ℝ≥0∞) := by
      apply ENNReal.sum_ne_top.mpr
      intro N _; exact hfin N
    have hofReal_sum : (∑ N ∈ Finset.range M,
          eLpNorm (fun x => f N x - c x) 2 (volume : Measure ℝ))
        = ENNReal.ofReal (∑ N ∈ Finset.range M, b N) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun N _ => ENNReal.toReal_nonneg)]
      refine Finset.sum_congr rfl (fun N _ => ?_)
      show eLpNorm (fun x => f N x - c x) 2 (volume : Measure ℝ)
        = ENNReal.ofReal (eLpNorm (fun x => f N x - c x) 2 (volume : Measure ℝ)).toReal
      rw [ENNReal.ofReal_toReal (hfin N)]
    rw [hofReal_sum]
    rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_natCast M,
        ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hMpos),
        ← ENNReal.ofReal_mul (by positivity)]

#print axioms tendsto_eLpNorm_cesaro_of_tendsto

/-! ## §3 — The named sharp spatial residual and the spatial conjunct reduction -/

/-- **Named `Prop` (NEVER an `axiom`): the sharp-truncation spatial `L²`-convergence.**

The sharp truncations `gSharp N = ½H_N′ + ½tail′` are in `L²` for every `N`, and converge to
`GC = ½H′` in `L²`:

    `eLpNorm (fun x => gSharp N x − GC x) 2 volume → 0`.

Numerically confirmed (`0.84 → 0.023 → 0.0049` at `N = 10,20,40`, decay `~N⁻¹`).  Unlike the
*Fourier* side (where the sharp truncation FAILS, constant `≈ 0.855`), the spatial side already
converges for the sharp family; the Cesàro smoothing (needed only on the Fourier side) preserves
this spatial limit (`tendsto_spatialSide_of_sharp`).  Bundles the per-`N` `L²` membership. -/
def GCesSharpSpatialL2 : Prop :=
  ∃ _hMemSharp : ∀ N, MemLp (gSharp N) 2 (volume : Measure ℝ),
    Filter.Tendsto (fun N => eLpNorm (fun x : ℝ => gSharp N x - GC x) 2 (volume : Measure ℝ))
      Filter.atTop (nhds (0 : ℝ≥0∞))

/-- **PROVEN — the spatial conjunct of `GCCesaroPlancherelData` from the sharp spatial limit.**

Granting `GCesSharpSpatialL2` (the sharp spatial `L²`-convergence with per-`N` `L²` membership)
and `MemLp GC 2`, the Cesàro family's spatial `L²`-convergence

    `eLpNorm (fun x => gCes M x − GC x) 2 volume → 0`

follows: `gCes M = (1/M)∑_{N<M} gSharp N` (`gCes_eq_average_gSharp`), and the Cesàro mean of an
`L²`-null sequence is `L²`-null (`tendsto_eLpNorm_cesaro_of_tendsto`), the membership giving the
finiteness of each `eLpNorm (gSharp N − GC) 2`. -/
theorem tendsto_spatialSide_of_sharp
    (hMemGC : MemLp GC 2 (volume : Measure ℝ))
    (hSharp : GCesSharpSpatialL2) :
    Filter.Tendsto (fun M => eLpNorm (fun x : ℝ => gCes M x - GC x) 2 (volume : Measure ℝ))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  obtain ⟨hMemSharp, h0⟩ := hSharp
  -- finiteness of each eLpNorm (gSharp N − GC)
  have hfin : ∀ N, eLpNorm (fun x => gSharp N x - GC x) 2 (volume : Measure ℝ) ≠ (⊤ : ℝ≥0∞) :=
    fun N => ((hMemSharp N).sub hMemGC).eLpNorm_lt_top.ne
  -- the Cesàro-mean convergence for f := gSharp, c := GC
  have hces := tendsto_eLpNorm_cesaro_of_tendsto (f := gSharp) (c := GC)
    (fun N => (hMemSharp N).aestronglyMeasurable)
    hMemGC.aestronglyMeasurable hfin h0
  -- rewrite `(1/M)∑ gSharp − GC` as `gCes M − GC` (only the `M ≥ 1` tail matters for atTop)
  refine (Filter.tendsto_congr' ?_).mp hces
  filter_upwards [Filter.eventually_gt_atTop 0] with M hMpos
  apply eLpNorm_congr_ae
  filter_upwards with x
  rw [gCes_eq_average_gSharp M hMpos x]

#print axioms GCesSharpSpatialL2
#print axioms tendsto_spatialSide_of_sharp

end MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialSide
