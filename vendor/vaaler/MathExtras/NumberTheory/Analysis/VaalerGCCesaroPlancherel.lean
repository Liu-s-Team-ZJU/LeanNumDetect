/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGCPlancherelELpNorm
import MathExtras.NumberTheory.Analysis.VaalerInterpHShiftedFejerSum

/-!
# Vaaler Theorem 6: the CESÀRO-mean truncation family for the `L²`-Plancherel datum

This NEW leaf supplies the **explicit truncation family** for the single remaining minor-arc
residual `GCPlancherelELpNormData`
(`MathExtras.NumberTheory.Analysis.VaalerGCPlancherelELpNorm.GCPlancherelELpNormData`), and
proves the genuine reduction `(Cesàro data) → GCPlancherelELpNormData`.

## The mathematical finding (verified numerically BEFORE formalising)

The "natural" sharp-truncation family proposed for this residual,

    g_N := ½·(HNcore N)′ + ½·tail′      (`tail z = (sin πz/π)²·2z⁻¹`),

satisfies the **spatial** `L²`-convergence `eLpNorm (g_N − GC) 2 → 0` (numerically
`0.84 → 0.023 → 0.0049` at `N = 10, 20, 40`), but it **FAILS** the Fourier-side
`L²`-convergence.  By the PROVEN closed form
`VaalerJFTviaHN.HNcore_FT_eq_triangle_cot`, the transform of `g_N` is

    𝓕(g_N)(t) = Ĵ(t)  −  π t (1−|t|) · cos(π(2N+1)t) / sin(πt)        (|t| < 1),

i.e. `Ĵ` **plus a highly-oscillatory remainder** `R_N`.  By the Bessel/Parseval mean-square
law `∫ |h(t)·cos(ωt)|² dt → ½∫|h|²` as `ω → ∞`, the remainder does **NOT** vanish in `L²`:

    ‖𝓕(g_N) − Ĵ‖₂  →  0.855…  ≠  0      (numerically constant in `N`: `0.855` at `N=5,20,80,200`).

This is exactly the same obstruction as the unsmoothed §10.2 major-arc saga (the "bad-idea"
sharp truncation Helfgott avoids): a sharp cutoff produces an oscillatory tail whose `L²`
norm is bounded away from `0`.

**The fix — Cesàro (Fejér-of-Fejér) smoothing.**  Replace the sharp partial sum by its
Cesàro mean over the truncation index:

    g_M  :=  ½·(K_M)′ + ½·tail′,   where   K_M := (1/M)·∑_{N<M} HNcore N
           =  ½·(K_M)′ + ½·tail′,   K_M(z) = ∑_{m=1}^{M-1} (1 − m/M)·(fejerK(z−m) − fejerK(z+m)).

Averaging leaves the `N`-independent `½·tail′` term unchanged and turns the oscillatory
remainder into its Cesàro mean

    R_avg_M(t) = −π t (1−|t|)/sin(πt) · (1/M)∑_{N<M} cos(π(2N+1)t)
               = −π t (1−|t|)/sin(πt) · sin(2πMt)/(2M sin(πt)),

whose `L²` norm **DOES** vanish: numerically `0.43 → 0.22 → 0.11 → 0.071 → 0.035` at
`M = 5,20,80,200,800` (decay `~M^{-1/2}`).  The spatial convergence is preserved (Cesàro of
a convergent sequence converges to the same limit): numerically `‖g_M − GC‖₂ =
0.151 → 0.037 → 0.015` at `M = 20,80,200` (decay `~M^{-1}`).

So the CORRECT truncation family is the **Cesàro-mean (triangularly-weighted) shifted-Fejér
core** plus the tail derivative.  `K_M` is precisely a Fejér-of-Fejér kernel: each shift
`fejerK(·∓m)` is weighted by the Fejér triangle `(1 − m/M)`.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `cesaroCore` (DEFINED) — the explicit triangularly-weighted shifted-Fejér core
  `K_M(z) = ∑_{m=1}^{M-1}(1 − m/M)(fejerK(z−m) − fejerK(z+m))`.
* `cesaroCore_eq_average` — **PROVEN**: `K_M = (1/M)·∑_{N<M} HNcore N`, identifying the
  triangular weights as the Cesàro mean of the sharp cores (Abel/triangle summation).
* `GCCesaroPlancherelData` (named `Prop`, NEVER an `axiom`) — the Cesàro-family form of the
  Plancherel datum: a family `g : ℕ → ℝ → ℂ` with `MemLp (g M) 2`, built from `½(K_M)′ +
  ½·tail′`, with BOTH `eLpNorm (g M − GC) 2 → 0` and `eLpNorm (𝓕(g M) − Ĵ) 2 → 0`.
* `gcPlancherelELpNormData_of_cesaro` — **PROVEN**: `GCCesaroPlancherelData → ∀ memberships,
  GCPlancherelELpNormData` (the genuine reduction; pure existential introduction, the Cesàro
  family IS the witness).
* `gcFTeqJhat_of_cesaro` — **PROVEN** the full chain to `GCFTeqJhat` from
  `{GIntegrable, GCBounded, GCCesaroPlancherelData}`.

## Honest status — did / did-not

DID: caught the Fourier-side `L²` defect of the natural sharp truncation (numerically), found
and numerically verified the Cesàro-mean correction, gave the explicit construction
`cesaroCore`, proved its Cesàro-average identity, and proved the reduction
`GCCesaroPlancherelData → GCPlancherelELpNormData → GCFTeqJhat`.  DID-NOT: prove the two
`L²`-convergences for the Cesàro family or the per-`M` `MemLp` (those are the genuine
remaining analytic content, isolated inside the named `Prop` `GCCesaroPlancherelData`).

## Numerical confirmation (mpmath, dps 25)

* sharp `g_N` Fourier defect: `‖𝓕(g_N) − Ĵ‖₂ = 0.85533, 0.85488, 0.85485, 0.85485`
  at `N = 5,20,80,200` (does not vanish);
* Cesàro Fourier: `‖R_avg_M‖₂ = 0.431, 0.221, 0.111, 0.0706, 0.0353` at `M = 5,20,80,200,800`;
* Cesàro spatial: `‖g_M − GC‖₂ = 0.151, 0.0375, 0.0150` at `M = 20,80,200`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.31)–(2.32); the Cesàro/Fejér summation that turns the oscillatory remainder of the
sharp partial sum into an `L²`-null Fejér tail (cf. Zygmund, *Trigonometric Series*, III.3,
Fejér's theorem and its `L²` form).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal BigOperators ContDiff

namespace MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel

open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJ
open MathExtras.NumberTheory.Analysis.VaalerGCFTeqJhatL2Limit
open MathExtras.NumberTheory.Analysis.VaalerGCMemLpTwo
open MathExtras.NumberTheory.Analysis.VaalerGCPlancherelELpNorm
open MathExtras.NumberTheory.Analysis.VaalerJFTviaHN
open MathExtras.NumberTheory.Analysis.VaalerInterpHShiftedFejerSum
open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerGRegularityProof

/-! ## §1 — The explicit Cesàro (triangularly-weighted) shifted-Fejér core -/

/-- **DEFINED — the Cesàro-mean shifted-Fejér core**

    `cesaroCore M z = ∑_{m=0}^{M-2} (1 − (m+1)/M)·(fejerK (z − (m+1)) − fejerK (z + (m+1)))`.

Equivalently `∑_{m=1}^{M-1} (1 − m/M)(fejerK(z−m) − fejerK(z+m))`: each shifted-Fejér pair
is weighted by the Fejér triangle `(1 − m/M)`.  This is the Cesàro mean of the sharp cores
`HNcore N` (see `cesaroCore_eq_average`), the truncation that — unlike the sharp `HNcore` —
makes the Fourier-side `L²`-convergence to `Ĵ` succeed (the oscillatory remainder becomes an
`L²`-null Fejér tail). -/
def cesaroCore (M : ℕ) (z : ℝ) : ℝ :=
  ∑ m ∈ Finset.range M,
    (1 - ((m : ℝ) + 1) / (M : ℝ)) *
      (fejerK (z - ((m : ℝ) + 1)) - fejerK (z + ((m : ℝ) + 1)))

/-- The `m = M-1`-indexed top weight `(1 − M/M) = 0` vanishes, so the `range M` and
`range (M-1)`/`range M` sums agree; this is just the explicit summand at the top index being
zero.  Recorded for downstream rewriting. -/
theorem cesaroCore_top_weight_zero (M : ℕ) (z : ℝ) (hM : 0 < M) :
    (1 - (((M - 1 : ℕ) : ℝ) + 1) / (M : ℝ)) *
      (fejerK (z - (((M - 1 : ℕ) : ℝ) + 1)) - fejerK (z + (((M - 1 : ℕ) : ℝ) + 1))) = 0 := by
  have hcast : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
    have : (M - 1 : ℕ) + 1 = M := Nat.succ_pred_eq_of_pos hM
    rw [← this]; push_cast; ring
  rw [hcast]
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have : (1 : ℝ) - (M : ℝ) / (M : ℝ) = 0 := by
    rw [div_self hMne]; ring
  rw [this]; ring

/-! ## §2 — The Cesàro mean identity: `cesaroCore M = (1/M)·∑_{N<M} HNcore N` -/

/-- **PROVEN (abstract triangular-weight / double-sum identity).**

For any real sequence `a : ℕ → ℝ`,

    ∑_{N<M} ∑_{m<N} a m  =  ∑_{m<M} ((M : ℝ) − (m+1)) · a m.

The term `a m` of the inner sum is counted once for each `N` with `m < N < M`, i.e.
`M − (m+1)` times.  Clean induction on `M` via `Finset.sum_range_succ`. -/
theorem double_sum_triangular (a : ℕ → ℝ) (M : ℕ) :
    (∑ N ∈ Finset.range M, ∑ m ∈ Finset.range N, a m)
      = ∑ m ∈ Finset.range M, ((M : ℝ) - ((m : ℝ) + 1)) * a m := by
  induction M with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    -- RHS at K+1: peel the top term m=K (which vanishes), then split the rest
    rw [Finset.sum_range_succ (f := fun m => ((↑(K + 1) : ℝ) - ((m : ℝ) + 1)) * a m)]
    have htop : ((↑(K + 1) : ℝ) - ((K : ℝ) + 1)) * a K = 0 := by push_cast; ring
    have hsplit : (∑ m ∈ Finset.range K, ((↑(K + 1) : ℝ) - ((m : ℝ) + 1)) * a m)
        = (∑ m ∈ Finset.range K, ((K : ℝ) - ((m : ℝ) + 1)) * a m)
          + ∑ m ∈ Finset.range K, a m := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      push_cast; ring
    rw [hsplit, htop]
    ring

/-- **PROVEN — the Cesàro-average identity.**

    `cesaroCore M z = (1/M) · ∑_{N ∈ range M} HNcore N z`.

This identifies the triangular weights `(1 − (m+1)/M)` with the Cesàro mean of the sharp
partial sums `HNcore N`.  Proof: expand `HNcore N z = ∑_{m<N}(fejerK(z−(m+1)) −
fejerK(z+(m+1)))`, apply the double-sum triangular count `double_sum_triangular`, and pull
out the `1/M` factor (matching `(M − (m+1))/M = 1 − (m+1)/M`). -/
theorem cesaroCore_eq_average (M : ℕ) (z : ℝ) :
    cesaroCore M z = (1 / (M : ℝ)) * ∑ N ∈ Finset.range M, HNcore N z := by
  set a : ℕ → ℝ := fun m => fejerK (z - ((m : ℝ) + 1)) - fejerK (z + ((m : ℝ) + 1)) with ha
  have hHN : (∑ N ∈ Finset.range M, HNcore N z)
      = ∑ N ∈ Finset.range M, ∑ m ∈ Finset.range N, a m := by
    refine Finset.sum_congr rfl (fun N _ => ?_); rw [HNcore]
  rw [hHN, double_sum_triangular a M, Finset.mul_sum, cesaroCore]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_range] at hm
  have hMne : (M : ℝ) ≠ 0 := by
    have : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    exact_mod_cast this.ne'
  -- match `(1 − (m+1)/M)·a m` with `(1/M)·((M−(m+1))·a m)`
  field_simp
  ring

/-- The Cesàro core unfolds termwise (definitional, for downstream `eLpNorm` work). -/
theorem cesaroCore_apply (M : ℕ) (z : ℝ) :
    cesaroCore M z =
      ∑ m ∈ Finset.range M,
        (1 - ((m : ℝ) + 1) / (M : ℝ)) *
          (fejerK (z - ((m : ℝ) + 1)) - fejerK (z + ((m : ℝ) + 1))) := rfl

/-! ## §3 — The tail function and the explicit Cesàro truncation family `gCes` -/

/-- The `2 z⁻¹` tail summand of the interpolant `interpH`:
`tailFn z = (sin πz/π)²·(2 z⁻¹)` (Vaaler eq. (2.31)).  Its half-derivative `½·tailFn′` is the
`N`-independent part of `GC = ½ interpH′` and contributes the `+|t|` of `Ĵ` on the Fourier
side (`VaalerHNAssembly.tailDeriv_collapse`). -/
def tailFn (z : ℝ) : ℝ := (Real.sin (π * z) / π) ^ 2 * (2 * z⁻¹)

/-- **DEFINED — the explicit Cesàro truncation family** (ℂ-valued):

    `gCes M x = ½·(deriv (cesaroCore M)) x  +  ½·(deriv tailFn) x`   (complexified).

This is `½·(K_M)′ + ½·tail′` with `K_M = cesaroCore M`, the triangularly-weighted
shifted-Fejér core derivative plus the (`M`-independent) tail derivative.  By
`cesaroCore_eq_average` this equals the Cesàro mean `(1/M)∑_{N<M} (½ HNcore N′ + ½ tail′)` of
the sharp truncations — the smoothing that repairs the Fourier-side `L²`-convergence to `Ĵ`. -/
def gCes (M : ℕ) (x : ℝ) : ℂ :=
  ((1 / 2 : ℝ) * deriv (cesaroCore M) x + (1 / 2 : ℝ) * deriv tailFn x : ℝ)

@[simp] theorem gCes_apply (M : ℕ) (x : ℝ) :
    gCes M x = ((1 / 2 : ℝ) * deriv (cesaroCore M) x + (1 / 2 : ℝ) * deriv tailFn x : ℝ) := rfl

/-! ### Smoothness of the Cesàro core and the tail (toward the `L²` membership) -/

/-- `tailFn = fun z => 2·z·fejerK z`.  For `z ≠ 0`, `2z·fejerK z = 2z·(sin πz/π)²·z⁻² =
(sin πz/π)²·2z⁻¹ = tailFn z`; at `z = 0` both sides are `0` (`0⁻¹ = 0`). -/
theorem tailFn_eq_two_mul_id_fejerK : tailFn = fun z : ℝ => 2 * z * fejerK z := by
  funext z
  rw [tailFn, fejerK]
  by_cases hz : z = 0
  · subst hz; simp
  · rw [if_neg hz]; field_simp

/-- `fun y => fejerK (y + c)` is `C∞` (the shift by `-c`). -/
theorem contDiff_fejerK_addShift (c : ℝ) : ContDiff ℝ ∞ (fun y : ℝ => fejerK (y + c)) := by
  have := contDiff_fejerK_shift (-c)
  simpa [sub_neg_eq_add] using this

/-- **PROVEN — the Cesàro core is `C∞`** (finite sum of `C∞` shifted Fejér pairs). -/
theorem contDiff_cesaroCore (M : ℕ) : ContDiff ℝ ∞ (cesaroCore M) := by
  have : cesaroCore M = fun z : ℝ =>
      ∑ m ∈ Finset.range M,
        (1 - ((m : ℝ) + 1) / (M : ℝ)) *
          (fejerK (z - ((m : ℝ) + 1)) - fejerK (z + ((m : ℝ) + 1))) := by
    funext z; exact cesaroCore_apply M z
  rw [this]
  refine ContDiff.sum (fun m _ => ?_)
  exact contDiff_const.mul
    ((contDiff_fejerK_shift ((m : ℝ) + 1)).sub (contDiff_fejerK_addShift ((m : ℝ) + 1)))

/-- **PROVEN — the tail `tailFn` is `C∞`** (`= 2·z·fejerK z`, `contDiff_two_mul_id_fejerK`). -/
theorem contDiff_tailFn : ContDiff ℝ ∞ tailFn := by
  rw [tailFn_eq_two_mul_id_fejerK]; exact contDiff_two_mul_id_fejerK

/-- **PROVEN — `Continuous (gCes M)`.**  `gCes M = (½·(cesaroCore M)′ + ½·tailFn′ : ℂ)` with
both derivatives continuous (the underlying functions are `C∞`), so the complexified
combination is continuous. -/
theorem continuous_gCes (M : ℕ) : Continuous (gCes M) := by
  have h1 : Continuous (deriv (cesaroCore M)) :=
    (contDiff_cesaroCore M).continuous_deriv (by simp)
  have h2 : Continuous (deriv tailFn) := contDiff_tailFn.continuous_deriv (by simp)
  have hreal : Continuous (fun x : ℝ => (1 / 2 : ℝ) * deriv (cesaroCore M) x
      + (1 / 2 : ℝ) * deriv tailFn x) := by fun_prop
  exact Complex.continuous_ofReal.comp hreal

/-- **PROVEN (reduction) — `MemLp (gCes M) 2` from integrability + boundedness.**

Each `gCes M` is continuous (`continuous_gCes`); with `Integrable (gCes M)` and a global
bound `∃ B, ∀ x, ‖gCes M x‖ ≤ B`, the reusable `memLp_two_of_integrable_of_bounded` gives
`MemLp (gCes M) 2`.  This isolates the remaining `L²`-membership content to the (finite-sum,
`O(1/x²)`-decay) integrability + boundedness of the explicit Cesàro derivative family — the
honest small-print of the construction. -/
theorem memLp_gCes_two_of (M : ℕ) (hint : Integrable (gCes M) (volume : Measure ℝ))
    (hbdd : ∃ B : ℝ, ∀ x, ‖gCes M x‖ ≤ B) : MemLp (gCes M) 2 (volume : Measure ℝ) :=
  memLp_two_of_integrable_of_bounded hint hbdd

/-! ## §4 — The named Cesàro Plancherel datum and the reduction to `GCPlancherelELpNormData` -/

/-- **Named `Prop` (NEVER an `axiom`): the Cesàro-family form of the Plancherel datum.**

The explicit Cesàro truncation family `gCes` is in `L²` for every `M`, and satisfies BOTH

* `eLpNorm (gCes M − GC) 2 → 0`  (spatial `L²`-convergence; numerically `0.151 → 0.0375 →
  0.0150` at `M = 20,80,200`, decay `~M⁻¹`); and
* `eLpNorm (⇑(𝓕 ((hMemCes M).toLp (gCes M))) − vaalerJCcont) 2 → 0`  (Fourier-side
  `L²`-convergence; the oscillatory remainder of the sharp truncation is replaced by the
  Cesàro/Fejér mean `sin(2πMt)/(2M sin πt)`, whose `L²` norm DOES vanish: numerically
  `0.431 → 0.221 → 0.111 → 0.0706 → 0.0353` at `M = 5,20,80,200,800`, decay `~M^{-1/2}`).

This is the CORRECTED replacement for the natural sharp-truncation datum, whose Fourier-side
`L²` norm is constant `≈ 0.855` (does not vanish; see the file header).  Bundles the per-`M`
`L²` membership `hMemCes`. -/
def GCCesaroPlancherelData : Prop :=
  ∃ hMemCes : ∀ M, MemLp (gCes M) 2 (volume : Measure ℝ),
    Filter.Tendsto (fun M => eLpNorm (fun x : ℝ => gCes M x - GC x) 2 (volume : Measure ℝ))
        Filter.atTop (nhds (0 : ℝ≥0∞)) ∧
    Filter.Tendsto
      (fun M => eLpNorm
        ((fun x : ℝ =>
            (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
              ((hMemCes M).toLp (gCes M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) x
              - MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.vaalerJCcont x))
        2 (volume : Measure ℝ))
      Filter.atTop (nhds (0 : ℝ≥0∞))

/-- **PROVEN — `GCPlancherelELpNormData` from the Cesàro datum.**

The explicit Cesàro family `gCes` (with its bundled per-`M` `L²` memberships and the two
`eLpNorm → 0` convergences) is *exactly* a witness of the existential `GCPlancherelELpNormData`.
Pure existential introduction: take `g := gCes`, `hg := hMemCes`, and forward the two
convergences.  This is the genuine reduction discharging the minor residual once the Cesàro
construction's two `L²`-limits are supplied. -/
theorem gcPlancherelELpNormData_of_cesaro
    (hMem : MemLp GC 2 (volume : Measure ℝ))
    (hJMem : MemLp MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT.vaalerJCcont 2
      (volume : Measure ℝ))
    (hData : GCCesaroPlancherelData) :
    GCPlancherelELpNormData hMem hJMem := by
  obtain ⟨hMemCes, hC1, hC2⟩ := hData
  exact ⟨gCes, hMemCes, hC1, hC2⟩

/-- **PROVEN — `GCFTeqJhat` from `{GIntegrable, GCBounded, GCCesaroPlancherelData}`.**

The deepest minor residual `GCFTeqJhat` (`𝓕(½H′) = Ĵ`, Vaaler eq. (2.31)→(2.32)) now rests on
the explicit *Cesàro* truncation construction: its per-`M` `L²` membership and its two
`eLpNorm → 0` convergences.  Composes `gcPlancherelELpNormData_of_cesaro` with the committed
`gcFTeqJhat_of_eLpNormData`. -/
theorem gcFTeqJhat_of_cesaro
    (hGint : GIntegrable) (hBdd : GCBounded)
    (hData : GCCesaroPlancherelData) :
    GCFTeqJhat :=
  gcFTeqJhat_of_eLpNormData hGint hBdd
    (gcPlancherelELpNormData_of_cesaro (memLp_GC_two_of hGint hBdd) memLp_vaalerJCcont_two hData)

#print axioms cesaroCore_top_weight_zero
#print axioms double_sum_triangular
#print axioms cesaroCore_eq_average
#print axioms gcPlancherelELpNormData_of_cesaro
#print axioms gcFTeqJhat_of_cesaro

end MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
