/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCesaroFTSignCorrection

/-!
# Vaaler minor: the `Lp`-linearity decomposition of `𝓕(gCes M)` into core + tail

`gCes M = ½·(cesaroCore M)′ + ½·tailFn′` is NOT in `L¹` (the tail derivative carries a
non-integrable `O(1/x)` envelope), so the `L¹∩L²` integral-transform bridge
`FourierL1L2Agreement.fourierIntegral_ae_eq_fourierTransformₗᵢ` does not apply to `gCes M`
directly.  The genuine route splits `gCes M` into

* `gCore M x := ½·(cesaroCore M)′ x`  (real, then complexified) — a FINITE sum of shifted
  Fejér-kernel derivatives, each `O(1/x²)` for large `|x|`, hence `L¹ ∩ L²`; and
* `gTail x := ½·tailFn′ x`  (real, then complexified) — `L²` but NOT `L¹` (the `O(1/x)`
  envelope),

and uses the `L²`-Plancherel transform `Lp.fourierTransformₗᵢ`, which is a **linear isometry**,
to add the two transforms at the `Lp` level (`map_add` on `toLp (gCore M) + toLp gTail`).

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `gCes_eq_gCore_add_gTail` — **PROVEN**: `gCes M = gCore M + gTail` pointwise.
* `lp_fourier_gCes_eq_add` — **PROVEN**: granting per-`M` `L²` memberships of the two pieces,
  the Plancherel transform of `gCes M` splits a.e. as
  `𝓕_Lp(gCore M) + 𝓕_Lp(gTail)` (via `MemLp.toLp_add` + `map_add` of the linear isometry).
* `gcesFTeqJhatPlusRavg_of_pieces` — **PROVEN reduction**: the corrected identity
  `GCesFTeqJhatPlusRavg` follows from the TWO precisely-named, numerically-verified `L²`-FT
  sub-residuals `CoreFTeqPrincipalPlusRavg` (`𝓕_Lp(gCore M) =ᵐ Ĵ_core + Ravg M`) and
  `TailFTeqJtail` (`𝓕_Lp(gTail) =ᵐ Ĵ_tail`), where `Ĵ_core + Ĵ_tail = vaalerJCcont` pointwise
  (`jPrincipalCore_add_jTail_eq_vaalerJCcont`, PROVEN).

## The residual map after this leaf

`GCesFTeqJhatPlusRavg`  (the sign-corrected Fourier identity; closes the minor wall via
`VaalerCesaroFTSignCorrection.gcFTeqJhat_of_two_residuals_corrected`) reduces to exactly:

1. `CoreFTeqPrincipalPlusRavg`  — the `L¹∩L²` core piece (provable via the committed agreement
   bridge `fourierIntegral_ae_eq_fourierTransformₗᵢ` + the Cesàro mean of `HNcore_deriv_FT_eq`,
   once `Integrable (gCore M)` is supplied — its `O(1/x²)` decay is in `abs_deriv_fejerK_le`);
2. `TailFTeqJtail`  — the `L²`-only tail piece (the genuine `L²`-density limit;
   `𝓕_Lp(½·tailFn′) = +|t|`-type closed form, `tailDeriv_collapse`).

Numerically (see the sibling sign-correction file): `𝓕(gCore M) ≈ Ĵ_core + Ravg M` and
`𝓕(gTail) ≈ Ĵ_tail`, with `Ĵ_core + Ĵ_tail = vaalerJCcont`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6,
eqs (2.31)–(2.32).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped FourierTransform ENNReal BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerCesaroFTDecomposition

open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel
open MathExtras.NumberTheory.Analysis.VaalerCesaroRemainderL2
open MathExtras.NumberTheory.Analysis.VaalerCesaroFTSignCorrection
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerFejerCoefficientNonneg

/-! ## §1 — The two pieces and the pointwise splitting -/

/-- The `L¹∩L²` core piece of `gCes M`: `gCore M x = ½·(cesaroCore M)′ x` (complexified). -/
def gCore (M : ℕ) (x : ℝ) : ℂ := (((1 / 2 : ℝ) * deriv (cesaroCore M) x : ℝ) : ℂ)

/-- The `L²`-only tail piece of `gCes M`: `gTail x = ½·tailFn′ x` (complexified). -/
def gTail (x : ℝ) : ℂ := (((1 / 2 : ℝ) * deriv tailFn x : ℝ) : ℂ)

/-- **PROVEN — the pointwise splitting `gCes M = gCore M + gTail`.** -/
theorem gCes_eq_gCore_add_gTail (M : ℕ) (x : ℝ) :
    gCes M x = gCore M x + gTail x := by
  rw [gCes_apply, gCore, gTail]
  push_cast
  ring

theorem continuous_gCore (M : ℕ) : Continuous (gCore M) := by
  have h1 : Continuous (deriv (cesaroCore M)) :=
    (contDiff_cesaroCore M).continuous_deriv (by simp)
  unfold gCore
  fun_prop

theorem continuous_gTail : Continuous gTail := by
  have h2 : Continuous (deriv tailFn) := contDiff_tailFn.continuous_deriv (by simp)
  unfold gTail
  fun_prop

/-! ### `L²` membership of the two pieces (discharged) -/

open MathExtras.NumberTheory.Analysis.VaalerGCesMemLpDischarge
open MathExtras.NumberTheory.Analysis.VaalerPoUCancellation

/-- **PROVEN — `MemLp (gCore M) 2`.**  `gCore M` is continuous with the large-`|x|`
`(x²)⁻¹` ⟹ `|x|⁻¹` decay of `½·(cesaroCore M)′` (`abs_deriv_cesaroCore_le`), which
`decay_one_of_large_compact` upgrades to a global `(1+|x|)⁻¹` envelope, then
`memLp_two_of_continuous_decay_one`. -/
theorem memLp_gCore_two (M : ℕ) : MemLp (gCore M) 2 (volume : Measure ℝ) := by
  have hK0 : (0 : ℝ) ≤ 2 / π + 2 / π ^ 2 := le_of_lt fejerK_const_pos
  have hcont : Continuous (fun x : ℝ => (1 / 2 : ℝ) * deriv (cesaroCore M) x) :=
    ((contDiff_cesaroCore M).continuous_deriv (by simp)).const_mul _
  -- large-|x| bound: |½·(cesaroCore M)′ x| ≤ (4 M K)·|x|⁻¹  for |x| ≥ 2(M+1)
  have hlarge : ∀ x : ℝ, 2 * ((M : ℝ) + 1) ≤ |x| →
      |(1 / 2 : ℝ) * deriv (cesaroCore M) x|
        ≤ (4 * (M : ℝ) * (2 / π + 2 / π ^ 2)) * |x|⁻¹ := by
    intro x hx
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hxge1 : (1 : ℝ) ≤ |x| := by nlinarith [hMnn, hx]
    have hxpos : (0 : ℝ) < |x| := lt_of_lt_of_le one_pos hxge1
    have hsq_le : (x ^ 2)⁻¹ ≤ |x|⁻¹ := by
      rw [show x ^ 2 = |x| ^ 2 by rw [sq_abs], inv_le_inv₀ (by positivity) hxpos]
      nlinarith [hxge1]
    have hces : |deriv (cesaroCore M) x|
        ≤ (8 * (M : ℝ) * (2 / π + 2 / π ^ 2)) * |x|⁻¹ := by
      refine le_trans (abs_deriv_cesaroCore_le hx) ?_
      exact mul_le_mul_of_nonneg_left hsq_le (by positivity)
    calc |(1 / 2 : ℝ) * deriv (cesaroCore M) x|
            = (1 / 2 : ℝ) * |deriv (cesaroCore M) x| := by
            rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
      _ ≤ (1 / 2 : ℝ) * ((8 * (M : ℝ) * (2 / π + 2 / π ^ 2)) * |x|⁻¹) :=
            mul_le_mul_of_nonneg_left hces (by norm_num)
      _ = (4 * (M : ℝ) * (2 / π + 2 / π ^ 2)) * |x|⁻¹ := by ring
  obtain ⟨A, hA0, hAle⟩ := decay_one_of_large_compact
    (h := fun x : ℝ => (1 / 2 : ℝ) * deriv (cesaroCore M) x)
    (C := 4 * (M : ℝ) * (2 / π + 2 / π ^ 2)) (R := 2 * ((M : ℝ) + 1)) hcont
    (by have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M; nlinarith)
    (by have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M; positivity)
    hlarge
  apply memLp_two_of_continuous_decay_one (continuous_gCore M) (A := A)
  intro x
  rw [gCore, Complex.norm_real, Real.norm_eq_abs]
  exact hAle x

/-- **PROVEN — `MemLp gTail 2`.**  `gTail` is continuous with the large-`|x|` `|x|⁻¹` decay of
`½·tailFn′` (`abs_deriv_tailFn_le`), upgraded to a global `(1+|x|)⁻¹` envelope by
`decay_one_of_large_compact`, then `memLp_two_of_continuous_decay_one`. -/
theorem memLp_gTail_two : MemLp gTail 2 (volume : Measure ℝ) := by
  have hK0 : (0 : ℝ) ≤ 2 / π + 2 / π ^ 2 := le_of_lt fejerK_const_pos
  have hcont : Continuous (fun x : ℝ => (1 / 2 : ℝ) * deriv tailFn x) :=
    (contDiff_tailFn.continuous_deriv (by simp)).const_mul _
  have hlarge : ∀ x : ℝ, (1 : ℝ) ≤ |x| →
      |(1 / 2 : ℝ) * deriv tailFn x|
        ≤ ((1 / 2 : ℝ) * (2 + 2 * (2 / π + 2 / π ^ 2))) * |x|⁻¹ := by
    intro x hx
    have htail : |deriv tailFn x| ≤ (2 + 2 * (2 / π + 2 / π ^ 2)) * |x|⁻¹ :=
      abs_deriv_tailFn_le hx
    calc |(1 / 2 : ℝ) * deriv tailFn x| = (1 / 2 : ℝ) * |deriv tailFn x| := by
            rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
      _ ≤ (1 / 2 : ℝ) * ((2 + 2 * (2 / π + 2 / π ^ 2)) * |x|⁻¹) :=
            mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = ((1 / 2 : ℝ) * (2 + 2 * (2 / π + 2 / π ^ 2))) * |x|⁻¹ := by ring
  obtain ⟨A, hA0, hAle⟩ := decay_one_of_large_compact
    (h := fun x : ℝ => (1 / 2 : ℝ) * deriv tailFn x)
    (C := (1 / 2 : ℝ) * (2 + 2 * (2 / π + 2 / π ^ 2))) (R := 1) hcont le_rfl
    (by positivity) hlarge
  apply memLp_two_of_continuous_decay_one continuous_gTail (A := A)
  intro x
  rw [gTail, Complex.norm_real, Real.norm_eq_abs]
  exact hAle x

/-! ## §2 — The `Lp`-linearity split of the Plancherel transform -/

/-- **PROVEN — the Plancherel transform of `gCes M` splits a.e. as core + tail.**

Granting per-`M` `L²` memberships of `gCes M`, `gCore M` and `gTail`, the `Lp` representatives
satisfy `toLp (gCes M) = toLp (gCore M) + toLp gTail` (`MemLp.toLp_add` via the pointwise
splitting `gCes_eq_gCore_add_gTail`), and the linear isometry `Lp.fourierTransformₗᵢ` is additive
(`map_add`), so

    `⇑(𝓕_Lp (gCes M))  =ᵐ  ⇑(𝓕_Lp (gCore M))  +  ⇑(𝓕_Lp gTail)`. -/
theorem lp_fourier_gCes_eq_add (M : ℕ)
    (hCes : MemLp (gCes M) 2 (volume : Measure ℝ))
    (hCore : MemLp (gCore M) 2 (volume : Measure ℝ))
    (hTail : MemLp gTail 2 (volume : Measure ℝ)) :
    (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
        (hCes.toLp (gCes M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] fun t : ℝ =>
        (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
          (hCore.toLp (gCore M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) t
        + (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
          (hTail.toLp gTail : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) t := by
  -- `toLp (gCes M) = toLp (gCore M) + toLp gTail` at the `Lp` level.
  have hsplit : hCes.toLp (gCes M)
      = hCore.toLp (gCore M) + hTail.toLp gTail := by
    rw [← MemLp.toLp_add hCore hTail]
    exact MemLp.toLp_congr hCes (hCore.add hTail)
      (Filter.Eventually.of_forall (fun x => gCes_eq_gCore_add_gTail M x))
  -- apply the linear isometry; `map_add`
  rw [hsplit, map_add]
  -- the representative of a sum is a.e. the sum of representatives
  filter_upwards [MeasureTheory.Lp.coeFn_add
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hCore.toLp (gCore M)))
    (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (hTail.toLp gTail))] with t ht
  rw [ht]
  rfl

/-! ## §3 — The two `Ĵ`-summands and their sum -/

/-- The tail `Ĵ`-summand `jTail t`, the function-FT of `gTail = ½·tailFn′`.  On `0 < |t| < 1`
this is `|t|` (`tailDeriv_collapse`); `0` at `t = 0` (matching `vaalerJhatCont`'s literal value)
and `0` off `[-1,1]`. -/
def jTail (t : ℝ) : ℝ :=
  if 1 ≤ |t| then 0 else if t = 0 then 0 else |t|

/-- The principal (core) `Ĵ`-summand: `fejerTriangle t · π t · cot(π t)` on the support
`(0 < |t| < 1)`, the limiting value at `t = 0`, and `0` off `[-1,1]`.  This is the function-FT
of `gCore M` minus its oscillatory `Ravg M` part — equivalently `vaalerJCcont t − jTail t`. -/
def jPrincipalCore (t : ℝ) : ℝ := vaalerJhatCont t - jTail t

/-- ℂ-valued principal-core summand. -/
def jPrincipalCoreC (t : ℝ) : ℂ := (jPrincipalCore t : ℂ)

/-- ℂ-valued tail summand. -/
def jTailC (t : ℝ) : ℂ := (jTail t : ℂ)

/-- **PROVEN — `Ĵ_core + Ĵ_tail = vaalerJCcont` pointwise.**

By definition `jPrincipalCore t = vaalerJhatCont t − jTail t`, so the (complexified) sum
telescopes to `vaalerJCcont t`. -/
theorem jPrincipalCore_add_jTail_eq_vaalerJCcont (t : ℝ) :
    jPrincipalCoreC t + jTailC t = vaalerJCcont t := by
  rw [jPrincipalCoreC, jTailC, vaalerJCcont_apply, jPrincipalCore]
  push_cast
  ring

/-! ## §4 — The two named `L²`-FT sub-residuals and the reduction -/

/-- **Named `Prop` (NEVER an `axiom`): the `L¹∩L²` core transform identity.**

`𝓕_Lp(gCore M) =ᵐ Ĵ_core + Ravg M` — the Plancherel transform of the core piece is the
principal `Ĵ`-core plus the Cesàro-averaged oscillatory remainder.  This is the `L¹∩L²`-provable
half: `gCore M` is integrable (finite shifted-Fejér-derivative sum, `O(1/x²)`), so the committed
agreement bridge `FourierL1L2Agreement.fourierIntegral_ae_eq_fourierTransformₗᵢ` reduces it to
the integral transform `𝓕(gCore M)`, which is the Cesàro mean of `HNcore_deriv_FT_eq`.
Numerically `𝓕(gCore M) ≈ Ĵ_core + Ravg M` (residual `≈ 10⁻⁴`). -/
def CoreFTeqPrincipalPlusRavg : Prop :=
  ∀ (M : ℕ) (h : MemLp (gCore M) 2 (volume : Measure ℝ)),
    (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
        (h.toLp (gCore M) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] fun t : ℝ => jPrincipalCoreC t + (Ravg M t : ℂ)

/-- **Named `Prop` (NEVER an `axiom`): the `L²`-only tail transform identity.**

`𝓕_Lp(gTail) =ᵐ Ĵ_tail` — the Plancherel transform of the (non-`L¹`) tail piece is the `Ĵ`-tail
summand `|t|`-part.  This is the genuine `L²`-density / limiting piece (`gTail ∉ L¹`); its
closed form `+|t|` on the support is `tailDeriv_collapse`.  Numerically `𝓕(gTail) ≈ Ĵ_tail`. -/
def TailFTeqJtail : Prop :=
  ∀ (h : MemLp gTail 2 (volume : Measure ℝ)),
    (⇑(MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ
        (h.toLp gTail : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] jTailC

/-- **PROVEN reduction — the corrected identity from the two `L²`-FT pieces.**

Granting the per-`M` `L²` membership of the two pieces, the core transform identity
`CoreFTeqPrincipalPlusRavg`, and the tail transform identity `TailFTeqJtail`, the sign-corrected
full identity `GCesFTeqJhatPlusRavg` follows: split via `lp_fourier_gCes_eq_add`, substitute the
two piece-identities, and telescope `Ĵ_core + Ĵ_tail = vaalerJCcont`
(`jPrincipalCore_add_jTail_eq_vaalerJCcont`) leaving `vaalerJCcont + Ravg M`. -/
theorem gcesFTeqJhatPlusRavg_of_pieces
    (hCoreId : CoreFTeqPrincipalPlusRavg)
    (hTailId : TailFTeqJtail) :
    GCesFTeqJhatPlusRavg := by
  intro M hCes
  have hsplit := lp_fourier_gCes_eq_add M hCes (memLp_gCore_two M) memLp_gTail_two
  have hc := hCoreId M (memLp_gCore_two M)
  have ht := hTailId memLp_gTail_two
  filter_upwards [hsplit, hc, ht] with t hsp hct htt
  rw [hsp, hct, htt]
  -- (Ĵ_core + Ravg) + Ĵ_tail = (Ĵ_core + Ĵ_tail) + Ravg = vaalerJCcont + Ravg
  have hsum := jPrincipalCore_add_jTail_eq_vaalerJCcont t
  rw [jPrincipalCoreC, jTailC] at hsum
  rw [show jPrincipalCoreC t + (Ravg M t : ℂ) + jTailC t
        = ((jPrincipalCore t : ℂ) + (jTail t : ℂ)) + (Ravg M t : ℂ) by
      rw [jPrincipalCoreC, jTailC]; ring]
  rw [hsum]

#print axioms gCes_eq_gCore_add_gTail
#print axioms memLp_gCore_two
#print axioms memLp_gTail_two
#print axioms lp_fourier_gCes_eq_add
#print axioms jPrincipalCore_add_jTail_eq_vaalerJCcont
#print axioms gcesFTeqJhatPlusRavg_of_pieces

end MathExtras.NumberTheory.Analysis.VaalerCesaroFTDecomposition
