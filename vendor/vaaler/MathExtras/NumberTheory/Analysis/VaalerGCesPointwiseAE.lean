/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialL2FromPointwise
import MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialSide
import MathExtras.NumberTheory.Analysis.VaalerGCesMemLpDischarge
import MathExtras.NumberTheory.Analysis.VaalerGPoUReprDecay
import MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail

/-!
# Closing the minor wall: `GCesTendstoPointwiseAE` is PROVEN

This NEW leaf proves the single remaining pointwise-a.e. residual of the minor wall

    `GCesTendstoPointwiseAE : ∀ᵐ x, Tendsto (fun M => gCes M x) atTop (𝓝 (GC x))`

(`VaalerCesaroSpatialL2FromPointwise.GCesTendstoPointwiseAE`), and then composes it with the
PROVEN reduction `gcFTeqJhat_of_pointwise` to obtain `GCFTeqJhat` **with no residual**.

## Mathematical content (all about EXPLICIT real functions; off ℤ, where `sin πx ≠ 0`)

Write `S = sin πx/π`, `C = cos πx·π/π`.  Off ℤ each shifted-Fejér derivative has the proven
closed form (`hasDerivAt_fejerK_shift_offInt`, `hasDerivAt_fejerK_posShift`)

    `deriv fejerK (x − (m+1)) = 2·S·C·(x−(m+1))⁻² − 2·S²·(x−(m+1))⁻³`,
    `deriv fejerK (x + (m+1)) = 2·S·C·(x+(m+1))⁻² − 2·S²·(x+(m+1))⁻³`.

* **Piece 1 (`hasSum_dShift`, `tendsto_deriv_HNcore`).**  The shifted-difference series
  `dShift m x = deriv fejerK(x−(m+1)) − deriv fejerK(x+(m+1))` is summable (the four
  inverse-square / inverse-cube tails are all summable), and `deriv (HNcore N) x` is its `N`-th
  partial sum (`deriv` of a finite sum), so `deriv (HNcore N) x → S x := ∑' m, dShift m x`.

* **Piece 3 (`half_S_add_half_dtail_eq_G`).**  By splitting the summable series into the four
  tails `M₂ = ∑(x−(k+1))⁻²`, `P₂ = ∑(x+(k+1))⁻²`, `M₃ = ∑(x−(k+1))⁻³`, `P₃ = ∑(x+(k+1))⁻³`,

      `S x = 2·S·C·(M₂ − P₂) − 2·S²·(M₃ − P₃)`,

  which is exactly `2·G x − deriv tailFn x` after matching `G`'s proven closed form
  (`G_eq_of_ne_zero`) and `deriv tailFn x = 2 fejerK x + 2x·deriv fejerK x` (`deriv_tailFn`).
  Hence `½·S x + ½·deriv tailFn x = G x`.

* **Piece 2 (`gCes_tendsto_GC_off_int`).**  `gSharp N x = ½ deriv(HNcore N) x + ½ deriv tailFn x
  → ½ S x + ½ deriv tailFn x = G x`, and `gCes M = (1/M)∑_{N<M} gSharp N` (`gCes_eq_average_gSharp`)
  is the Cesàro mean of `gSharp N → G x`, so it converges to the same limit (`Filter.Tendsto.cesaro`).
  Casting to `ℂ` and using `GC x = (G x : ℂ)` gives `gCes M x → GC x`.

Since `ℤ` (`Set.range ((↑) : ℤ → ℝ)`) is null, the off-ℤ convergence is a.e.

## Hard constraints honoured

NEW leaf only; nothing committed is edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Thm 6,
eqs (2.27)–(2.32).
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerGCesPointwiseAE

open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
open MathExtras.NumberTheory.Analysis.VaalerJFTviaHN
open MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ
open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGRegularityProof
open MathExtras.NumberTheory.Analysis.VaalerGCesMemLpDischarge
open MathExtras.NumberTheory.Analysis.VaalerGPoUReprDecay
open MathExtras.NumberTheory.Analysis.VaalerPoUCancellation
open MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialSide
open MathExtras.NumberTheory.Analysis.VaalerCesaroSpatialL2FromPointwise

/-! ## §1 — Closed forms for the shifted-Fejér derivatives off ℤ -/

/-- `x − (m+1) ≠ 0` off ℤ (else `x = m+1 ∈ ℤ`, contradicting `sin πx ≠ 0`). -/
theorem sub_posShift_ne_zero {x : ℝ} (hs : Real.sin (π * x) ≠ 0) (m : ℕ) :
    x - ((m : ℝ) + 1) ≠ 0 := by
  intro h
  apply hs
  have hxm : x = ((m : ℝ) + 1) := by linarith
  rw [hxm, show π * ((m : ℝ) + 1) = ((↑m + 1 : ℤ) : ℝ) * π by push_cast; ring, Real.sin_int_mul_pi]

/-- The neg-shift derivative `deriv fejerK (x − (m+1))`, in the closed form carrying `sin πx`. -/
theorem deriv_fejerK_negShift (m : ℕ) {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    deriv fejerK (x - ((m : ℝ) + 1))
      = 2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (x - ((m : ℝ) + 1))⁻¹ ^ 2
        + (Real.sin (π * x) / π) ^ 2 * (-2 * (x - ((m : ℝ) + 1))⁻¹ ^ 3) := by
  -- `deriv (fun y => fejerK (y - (m+1))) x = deriv fejerK (x - (m+1))` (shift by constant)
  have hshiftdiff : deriv (fun y : ℝ => fejerK (y - ((m : ℝ) + 1))) x
      = deriv fejerK (x - ((m : ℝ) + 1)) :=
    ((hasDerivAt_fejerK (x - ((m : ℝ) + 1))).comp_sub_const x ((m : ℝ) + 1)).deriv
  -- closed form for `deriv (fun y => fejerK (y - n)) x` at the integer `n = m+1`
  have hxn : x - (((↑m + 1 : ℤ)) : ℝ) ≠ 0 := by
    have : x - ((m : ℝ) + 1) ≠ 0 := sub_posShift_ne_zero hs m
    push_cast; push_cast at this; exact this
  have h := hasDerivAt_fejerK_shift_offInt (n := (↑m + 1 : ℤ)) (x := x) hxn
  have hcast : (((↑m + 1 : ℤ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h
  rw [← hshiftdiff, h.deriv]

/-- The pos-shift derivative `deriv fejerK (x + (m+1))`, in the closed form carrying `sin πx`.
The point-derivative equals `deriv (fun y => fejerK (y + (m+1))) x` (shift by constant), whose
closed form is `hasDerivAt_fejerK_posShift`. -/
theorem deriv_fejerK_posShift_pt (m : ℕ) {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    deriv fejerK (x + ((m : ℝ) + 1))
      = 2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (x + ((m : ℝ) + 1))⁻¹ ^ 2
        + (Real.sin (π * x) / π) ^ 2 * (-2 * (x + ((m : ℝ) + 1))⁻¹ ^ 3) := by
  have hshiftdiff : deriv (fun y : ℝ => fejerK (y + ((m : ℝ) + 1))) x
      = deriv fejerK (x + ((m : ℝ) + 1)) :=
    ((hasDerivAt_fejerK (x + ((m : ℝ) + 1))).comp_add_const x ((m : ℝ) + 1)).deriv
  rw [← hshiftdiff, (hasDerivAt_fejerK_posShift m hs).deriv]

/-! ## §2 — The shifted-difference summand and its summability/limit -/

/-- The shifted-Fejér derivative-difference summand. -/
def dShift (x : ℝ) (m : ℕ) : ℝ :=
  deriv fejerK (x - ((m : ℝ) + 1)) - deriv fejerK (x + ((m : ℝ) + 1))

/-- `dShift x m` in closed form off ℤ: `2SC((x−(m+1))⁻² − (x+(m+1))⁻²) − 2S²((x−(m+1))⁻³ − (x+(m+1))⁻³)`. -/
theorem dShift_closed (m : ℕ) {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    dShift x m
      = 2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π)
          * ((x - ((m : ℝ) + 1))⁻¹ ^ 2 - (x + ((m : ℝ) + 1))⁻¹ ^ 2)
        - 2 * (Real.sin (π * x) / π) ^ 2
          * ((x - ((m : ℝ) + 1))⁻¹ ^ 3 - (x + ((m : ℝ) + 1))⁻¹ ^ 3) := by
  simp only [dShift]
  rw [deriv_fejerK_negShift m hs, deriv_fejerK_posShift_pt m hs]
  ring

/-- Summability of the inverse-square neg tail. -/
theorem summable_negSq (x : ℝ) : Summable (fun m : ℕ => (x - ((m : ℝ) + 1))⁻¹ ^ 2) := by
  have h := MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail.summable_invSq_shift_neg x
  refine h.congr (fun m => ?_); push_cast; ring_nf

/-- Summability of the inverse-square pos tail. -/
theorem summable_posSq (x : ℝ) : Summable (fun m : ℕ => (x + ((m : ℝ) + 1))⁻¹ ^ 2) := by
  have h := MathExtras.NumberTheory.Analysis.VaalerGPoUReprDecay.summable_posTail_sq x
  refine h.congr (fun m => ?_); push_cast; ring_nf

/-- Summability of the inverse-cube neg tail (from the absolute cube tail). -/
theorem summable_negCube (x : ℝ) : Summable (fun m : ℕ => (x - ((m : ℝ) + 1))⁻¹ ^ 3) := by
  have h := MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail.summable_invCube_shift_neg x
  -- |·|⁻³ summable ⟹ ·⁻³ summable (abs)
  refine Summable.of_abs ?_
  refine h.congr (fun m => ?_)
  have hcast : (x - ((m : ℕ) + 1 : ℕ) : ℝ) = x - ((m : ℝ) + 1) := by push_cast; ring
  rw [hcast, abs_pow, abs_inv]

/-- Summability of the inverse-cube pos tail. -/
theorem summable_posCube (x : ℝ) : Summable (fun m : ℕ => (x + ((m : ℝ) + 1))⁻¹ ^ 3) := by
  have h := MathExtras.NumberTheory.Analysis.VaalerGPoUReprDecay.summable_posTail_cube' x
  refine h.congr (fun m => ?_); push_cast; ring_nf

/-- The shifted-difference series is summable off ℤ (sum of the four summable tails). -/
theorem summable_dShift {x : ℝ} (hs : Real.sin (π * x) ≠ 0) : Summable (dShift x) := by
  have hsumcl : Summable (fun m : ℕ =>
      2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π)
          * ((x - ((m : ℝ) + 1))⁻¹ ^ 2 - (x + ((m : ℝ) + 1))⁻¹ ^ 2)
        - 2 * (Real.sin (π * x) / π) ^ 2
          * ((x - ((m : ℝ) + 1))⁻¹ ^ 3 - (x + ((m : ℝ) + 1))⁻¹ ^ 3)) := by
    apply Summable.sub
    · exact (((summable_negSq x).sub (summable_posSq x)).mul_left _)
    · exact (((summable_negCube x).sub (summable_posCube x)).mul_left _)
  refine hsumcl.congr (fun m => (dShift_closed m hs).symm)

/-- The tsum of the shifted-difference series, off ℤ:
`∑' m, dShift x m = 2SC(M₂−P₂) − 2S²(M₃−P₃)`. -/
theorem tsum_dShift {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    ∑' m : ℕ, dShift x m
      = 2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π)
          * ((∑' m : ℕ, (x - ((m : ℝ) + 1))⁻¹ ^ 2) - ∑' m : ℕ, (x + ((m : ℝ) + 1))⁻¹ ^ 2)
        - 2 * (Real.sin (π * x) / π) ^ 2
          * ((∑' m : ℕ, (x - ((m : ℝ) + 1))⁻¹ ^ 3) - ∑' m : ℕ, (x + ((m : ℝ) + 1))⁻¹ ^ 3) := by
  rw [tsum_congr (fun m => dShift_closed m hs)]
  rw [Summable.tsum_sub
      (((summable_negSq x).sub (summable_posSq x)).mul_left _)
      (((summable_negCube x).sub (summable_posCube x)).mul_left _)]
  rw [(((summable_negSq x).sub (summable_posSq x))).tsum_mul_left,
      (((summable_negCube x).sub (summable_posCube x))).tsum_mul_left]
  rw [(summable_negSq x).tsum_sub (summable_posSq x),
      (summable_negCube x).tsum_sub (summable_posCube x)]

/-! ## §3 — `deriv (HNcore N) x` is the `N`-th partial sum of `dShift x`, hence `→ ∑' dShift` -/

/-- `deriv (HNcore N) x = ∑_{m<N} dShift x m` (deriv of the finite shifted-Fejér core). -/
theorem deriv_HNcore_eq (N : ℕ) (x : ℝ) :
    deriv (HNcore N) x = ∑ m ∈ Finset.range N, dShift x m := by
  have hsum : HasDerivAt (HNcore N) (∑ m ∈ Finset.range N, dShift x m) x := by
    have heach : ∀ m ∈ Finset.range N,
        HasDerivAt (fun z : ℝ => fejerK (z - ((m : ℝ) + 1)) - fejerK (z + ((m : ℝ) + 1)))
          (dShift x m) x := by
      intro m _
      have hsub : HasDerivAt (fun z : ℝ => fejerK (z - ((m : ℝ) + 1)))
          (deriv fejerK (x - ((m : ℝ) + 1))) x :=
        (hasDerivAt_fejerK (x - ((m : ℝ) + 1))).comp_sub_const x ((m : ℝ) + 1)
      have hadd : HasDerivAt (fun z : ℝ => fejerK (z + ((m : ℝ) + 1)))
          (deriv fejerK (x + ((m : ℝ) + 1))) x :=
        (hasDerivAt_fejerK (x + ((m : ℝ) + 1))).comp_add_const x ((m : ℝ) + 1)
      exact hsub.sub hadd
    have hHN : HasDerivAt (HNcore N) (∑ m ∈ Finset.range N, dShift x m) x := by
      have hfun : HNcore N = (fun z : ℝ => ∑ m ∈ Finset.range N,
          (fejerK (z - ((m : ℝ) + 1)) - fejerK (z + ((m : ℝ) + 1)))) := by
        funext z; rw [HNcore]
      rw [hfun]
      have hs := HasDerivAt.sum (u := Finset.range N)
        (A := fun m z => fejerK (z - ((m : ℝ) + 1)) - fejerK (z + ((m : ℝ) + 1)))
        (A' := fun m => dShift x m) heach
      have hfn : (∑ i ∈ Finset.range N, fun z : ℝ =>
          fejerK (z - ((i : ℝ) + 1)) - fejerK (z + ((i : ℝ) + 1)))
          = (fun z : ℝ => ∑ m ∈ Finset.range N,
            (fejerK (z - ((m : ℝ) + 1)) - fejerK (z + ((m : ℝ) + 1)))) := by
        funext z; rw [Finset.sum_apply]
      rwa [hfn] at hs
    exact hHN
  exact hsum.deriv

/-- **Piece 1 — `deriv (HNcore N) x → ∑' m, dShift x m`** (off ℤ). -/
theorem tendsto_deriv_HNcore {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    Filter.Tendsto (fun N : ℕ => deriv (HNcore N) x) Filter.atTop (nhds (∑' m : ℕ, dShift x m)) := by
  have htend := (summable_dShift hs).hasSum.tendsto_sum_nat
  refine htend.congr (fun N => ?_)
  rw [deriv_HNcore_eq N x]

/-! ## §4 — Piece 3: `½·(∑' dShift) + ½·deriv tailFn = G` off ℤ -/

/-- **Piece 3 — `½·(∑' m, dShift x m) + ½·deriv tailFn x = G x`** (off ℤ).

By `tsum_dShift`, `∑' dShift = 2SC(M₂−P₂) − 2S²(M₃−P₃)`.  By `G_eq_of_ne_zero`,
`G x = SC·(M₂ − P₂ + 2x⁻¹) + ½S²·(−2M₃ + 2P₃ − 2x⁻²)`, and `deriv tailFn x = 4SCx⁻¹ − 2S²x⁻²`
(`deriv_tailFn` + `deriv_fejerK_offZero`); pure algebra yields `½·(∑' dShift) + ½ tailFn′ = G`. -/
theorem half_S_add_half_dtail_eq_G {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    (1 / 2 : ℝ) * (∑' m : ℕ, dShift x m) + (1 / 2 : ℝ) * deriv tailFn x = G x := by
  have hx0 : x ≠ 0 := by
    intro h; apply hs; rw [h]; simp
  -- closed form for the tail derivative, with `deriv fejerK x` expanded off zero
  have hdtail : deriv tailFn x
      = 4 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * x⁻¹
        - 2 * (Real.sin (π * x) / π) ^ 2 * x⁻¹ ^ 2 := by
    rw [deriv_tailFn, deriv_fejerK_offZero hx0, fejerK, if_neg hx0]
    field_simp
    ring
  rw [tsum_dShift hs, hdtail, G_eq_of_ne_zero hx0, interpBracket, tailSum]
  -- Align all four tsums (G uses the `(k+1:ℕ)` cast and the `^2*·` cube shape;
  -- tsum_dShift uses `(↑m+1)` and `^3`).  Rewrite G's tsums into the matching forms.
  have hM2 : (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2) = ∑' m : ℕ, (x - ((m : ℝ) + 1))⁻¹ ^ 2 :=
    tsum_congr (fun m => by push_cast; ring_nf)
  have hP2 : (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2) = ∑' m : ℕ, (x + ((m : ℝ) + 1))⁻¹ ^ 2 :=
    tsum_congr (fun m => by push_cast; ring_nf)
  have hM3neg : (∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹)
      = -2 * ∑' m : ℕ, (x - ((m : ℝ) + 1))⁻¹ ^ 3 := by
    rw [show (-2 : ℝ) * ∑' m : ℕ, (x - ((m : ℝ) + 1))⁻¹ ^ 3
          = ∑' m : ℕ, -2 * (x - ((m : ℝ) + 1))⁻¹ ^ 3 from (tsum_mul_left).symm]
    refine tsum_congr (fun m => by push_cast; ring_nf)
  have hP3neg : (∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹)
      = -2 * ∑' m : ℕ, (x + ((m : ℝ) + 1))⁻¹ ^ 3 := by
    rw [show (-2 : ℝ) * ∑' m : ℕ, (x + ((m : ℝ) + 1))⁻¹ ^ 3
          = ∑' m : ℕ, -2 * (x + ((m : ℝ) + 1))⁻¹ ^ 3 from (tsum_mul_left).symm]
    refine tsum_congr (fun m => by push_cast; ring_nf)
  rw [hM2, hP2, hM3neg, hP3neg]
  ring

/-! ## §5 — Piece 2: `gSharp N x → GC x` off ℤ, the Cesàro mean, and the a.e. statement -/

/-- **Pieces 1 + 3 combined — `gSharp N x → GC x`** (off ℤ).

`gSharp N x = ½·deriv(HNcore N) x + ½·deriv tailFn x` (cast to `ℂ`); the `N`-dependent part
converges to `½·(∑' dShift) x` (`tendsto_deriv_HNcore`), so `gSharp N x → (½·(∑' dShift) x +
½·deriv tailFn x : ℝ) = (G x : ℝ) = GC x` (`half_S_add_half_dtail_eq_G`, `GC`). -/
theorem tendsto_gSharp_GC {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    Filter.Tendsto (fun N : ℕ => gSharp N x) Filter.atTop (nhds (GC x)) := by
  -- the real limit
  have hreal : Filter.Tendsto
      (fun N : ℕ => (1 / 2 : ℝ) * deriv (HNcore N) x + (1 / 2 : ℝ) * deriv tailFn x)
      Filter.atTop (nhds ((1 / 2 : ℝ) * (∑' m : ℕ, dShift x m) + (1 / 2 : ℝ) * deriv tailFn x)) := by
    have h1 : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) * deriv (HNcore N) x) Filter.atTop
        (nhds ((1 / 2 : ℝ) * (∑' m : ℕ, dShift x m))) :=
      (tendsto_deriv_HNcore hs).const_mul (1 / 2 : ℝ)
    exact h1.add_const _
  -- identify the real limit with `G x`
  rw [half_S_add_half_dtail_eq_G hs] at hreal
  -- cast to ℂ; `gSharp N x = (real ·)`, `GC x = (G x : ℂ)`
  have hcast : Filter.Tendsto (fun N : ℕ => gSharp N x) Filter.atTop (nhds ((G x : ℝ) : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto (G x)).comp hreal
    refine this.congr (fun N => ?_)
    simp only [gSharp, Function.comp]
  rw [GC]
  exact hcast

/-- **Piece 2 — the Cesàro mean `gCes M x → GC x`** (off ℤ).

`gCes M = (1/M)·∑_{N<M} gSharp N` (`gCes_eq_average_gSharp`) is the Cesàro mean of the convergent
sequence `gSharp N x → GC x` (`tendsto_gSharp_GC`), so it converges to the same limit
(`Filter.Tendsto.cesaro_smul`). -/
theorem tendsto_gCes_GC {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    Filter.Tendsto (fun M : ℕ => gCes M x) Filter.atTop (nhds (GC x)) := by
  -- Cesàro mean of the convergent ℂ-sequence
  have hces : Filter.Tendsto
      (fun M : ℕ => ((M : ℝ)⁻¹ : ℝ) • ∑ N ∈ Finset.range M, gSharp N x)
      Filter.atTop (nhds (GC x)) :=
    (tendsto_gSharp_GC hs).cesaro_smul
  -- rewrite `(M⁻¹) • ∑ = gCes M` eventually (M ≥ 1)
  refine hces.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with M hM1
  have hMpos : 0 < M := hM1
  rw [gCes_eq_average_gSharp M hMpos x, Complex.real_smul]
  push_cast
  ring

/-- The set of `x` with `sin (π x) = 0` is exactly `Set.range ((↑) : ℤ → ℝ)`, which is null. -/
theorem sin_pi_ne_zero_ae : ∀ᵐ x : ℝ, Real.sin (π * x) ≠ 0 := by
  -- the complement is contained in the countable set `range ((↑):ℤ→ℝ)`
  have hsub : {x : ℝ | ¬ Real.sin (π * x) ≠ 0} ⊆ Set.range ((↑) : ℤ → ℝ) := by
    intro x hx
    simp only [Set.mem_setOf_eq, not_not] at hx
    rw [Real.sin_eq_zero_iff] at hx
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    -- hn : (n : ℝ) * π = π * x  ⇒  x = n
    have : (x : ℝ) * π = (n : ℝ) * π := by rw [mul_comm x π, ← hn]
    exact (mul_right_cancel₀ hπ this).symm
  refine MeasureTheory.measure_mono_null hsub ?_
  exact (Set.countable_range _).measure_zero _

/-! ## §6 — `GCesTendstoPointwiseAE` is PROVEN, and the minor wall closes -/

/-- **PROVEN — the single remaining residual `GCesTendstoPointwiseAE`.**
Off ℤ (a.e., `sin_pi_ne_zero_ae`) the Cesàro family converges pointwise to `GC`
(`tendsto_gCes_GC`). -/
theorem gCesTendstoPointwiseAE_holds : GCesTendstoPointwiseAE := by
  rw [GCesTendstoPointwiseAE]
  filter_upwards [sin_pi_ne_zero_ae] with x hx
  exact tendsto_gCes_GC hx

/-- **PROVEN — the minor wall `GCFTeqJhat` is FULLY closed**, with no residual:
compose the now-proven pointwise residual with the committed reduction
`gcFTeqJhat_of_pointwise`. -/
theorem minorWall_closed : MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ.GCFTeqJhat :=
  gcFTeqJhat_of_pointwise gCesTendstoPointwiseAE_holds

#print axioms gCesTendstoPointwiseAE_holds
#print axioms minorWall_closed

end MathExtras.NumberTheory.Analysis.VaalerGCesPointwiseAE
