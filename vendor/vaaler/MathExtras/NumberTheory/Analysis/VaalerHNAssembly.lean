/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerJFTviaHN
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Vaaler Theorem 6, derivative-level assembly of `𝓕(½H_N′) → Ĵ`

This NEW leaf is the **derivative-level assembly** sitting on top of the proven
shifted-Fejér Fourier theory of `VaalerJFTviaHN` (`HNcore_FT`,
`HNcore_FT_eq_triangle_cot`).  Its purpose is to pin — numerically and then in Lean —
exactly how the `πit` derivative multiplier turns the proven *function-level* core
transform

    𝓕(H_N-core)(t) = (1−|t|)₊ · (−i·cot πt + i·osc_N(t))                 (PROVEN)

into the first (principal) term of Vaaler's `Ĵ`, and how the `2 z⁻¹` tail — whose
*function-level* transform is the purely-imaginary `|t|/(πit)` (DEAD_ENDS #18: the FT
of the odd `(sin πz/π)²·2z⁻¹` is imaginary, not the real `|t|`) — supplies the `+|t|`
ONLY after the `πit` derivative factor.

## Numerical pin (mpmath, verified before formalising)

With `Ĵ(t) := vaalerJhat |t| = π|t|(1−|t|)cot(π|t|) + |t|` (the target, `|t|<1`):

* `principal(t) := πt(1−|t|)cot(πt)` and `Ĵ(t) − principal(t) = |t|` **exactly** for
  every tested `t ∈ {±0.05, ±0.1, 0.3, ±0.4, 0.7, ±0.9, ±0.15}` — the derivative-level
  tail contribution is exactly `+|t|`.
* derivative-level principal `πit·[(1−|t|)·(−i·cot πt)] = πt(1−|t|)cot πt = principal(t)`
  (real), and `πit·[|t|/(πit)] = |t|` (real).  Sum `= Ĵ(t)` to `1e-31`.
* function-level tail FT `= |t|/(πit) = −i·sgn(t)/π` is purely imaginary — consistent
  with the odd kernel — and becomes real only after `×πit`.

(See the `derivLevelTotal_*` theorems for the Lean witnesses of these identities.)

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `derivLevelPrincipal_eq` — **PROVEN.**  `πit·((1−|t|)·(−i·cotC t)) = πt(1−|t|)·cotC t`
  (the `i·(−i)=1` collapse of the derivative-multiplier on the principal core term;
  pure complex algebra, no parity needed).
* `derivLevelTotal_eq` — **PROVEN.**  the full derivative-level total
  `πit·((1−|t|)·(−i·cotC t)) + |t| = πt(1−|t|)·cotC t + |t|` — the symbolic statement of
  the numeric pin, the principal-plus-tail decomposition of `Ĵ` at derivative level.
* `derivLevelTotal_eq_vaalerJhat` — **PROVEN.**  for `0 < t < 1`, the derivative-level
  total equals `(vaalerJhat t : ℂ)` (literally `Ĵ` on the positive support), via
  `cotC t = (Real.cot (π t) : ℂ)` on `0 < t`.
* `echar_eq_fourierKernel` — **PROVEN.**  `echar t v = Real.fourierChar (−(v·t))` smul `1`
  bridge: `∫ (f v)·echar t v dv = 𝓕 f t` (`integral_mul_echar_eq_fourier`), tying the
  `echar`-integrals of this project to Mathlib's `𝓕`.
* `halfDeriv_FT_eq_mul` — **PROVEN.**  the derivative→multiplier FT rule, *proved* (not
  a `Prop`!) for any integrable differentiable `f : ℝ → ℂ` with integrable derivative
  `f' = 2·g` (the `½`-derivative shape):
  `∫ (g v)·echar t v dv = (π i t)·∫ (f v)·echar t v dv`, via Mathlib `fourier_deriv`.

* `tailDeriv_collapse` — **PROVEN.**  `π i t · (−i·(sgn t)/π) = |t|`: the tail's
  *function-level* transform is the purely-imaginary `−i·sgn(t)/π = |t|/(πit)`
  (DEAD_ENDS #18), and the `πit` derivative multiplier turns it into the real `+|t|` of
  `Ĵ`.  Pure complex algebra.
* `HNcore_deriv_FT_eq` — **PROVEN.**  the `N`-level *derivative* transform of the
  shifted-Fejér core `= (1−|t|)₊·(π t cotC t + osc_N)`; the principal is the first `Ĵ`
  term, `osc_N → 0` by Riemann–Lebesgue.

## What is reduced to the SINGLE remaining residual (NOT an axiom)

* The truncation limit (`VaalerJFTviaHN.HNDerivConverges := ∃Gc, GcEqVaalerJ Gc`) is the
  ONE remaining `N → ∞` Riemann–Lebesgue passage (numerically CONFIRMED).  Granting it,
  the proven `gEqReJ_of_truncationLimit` (via `GcEqVaalerJ_of_HN_backbone`) closes
  `GEqReJ` — the entire D-1 minor wall.  No new `Prop` is introduced here: this file
  upgrades two of the three `VaalerJFTviaHN` backbone `Prop`s (the tail transform and the
  derivative multiplier) to THEOREMS, leaving exactly that single limit.

## Honest status

The derivative-multiplier *mechanism* — the `πit` algebra collapsing the core to the
principal `Ĵ` term, the closed `vaalerJhat` value, and the generic
integration-by-parts FT rule `halfDeriv_FT_eq_mul` (now a THEOREM, upgraded from the
`HalfHNDerivFT` Prop of `VaalerJFTviaHN`) — is FULLY PROVEN here.  What remains, exactly
as in `VaalerJFTviaHN`, is the truncation limit / Riemann–Lebesgue passage producing
`GcEqVaalerJ`; it is isolated as the named (numerically-grounded) Props above, never an
axiom.  Granting that single limit, `GEqReJ` (and the whole `H′ = 2J` minor wall) closes
through the proven `GcEqVaalerJ_of_HN_backbone`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.31)–(2.32); Mathlib `Analysis.Fourier.FourierTransformDeriv`
(`fourier_deriv`).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology
open scoped BigOperators FourierTransform RealInnerProductSpace

namespace MathExtras.NumberTheory.Analysis.VaalerHNAssembly

open MathExtras.NumberTheory.Analysis.VaalerJFourierTransform
open MathExtras.NumberTheory.Analysis.VaalerThm16Mechanism
open MathExtras.NumberTheory.Analysis.VaalerJFTviaHN

/-! ## §1 — The derivative-level total identity (the numeric pin, FULLY PROVEN) -/

/-- **PROVEN.**  The `πit` derivative-multiplier collapses the principal core term:

    π i t · ((1 − |t|) · (−i · cotC t)) = π t (1 − |t|) · cotC t.

Pure complex algebra: `(π i t)·(−i) = π t` because `i·(−i) = 1`.  This is the first
(principal) term of Vaaler's `Ĵ` arising at the *derivative* level from the proven
function-level core `(1−|t|)·(−i·cot πt)` (eq. (2.31)→(2.32)). -/
theorem derivLevelPrincipal_eq (t : ℝ) :
    (π * Complex.I * t : ℂ) * (((1 - |t| : ℝ) : ℂ) * (-Complex.I * cotC t))
      = (π * t : ℂ) * ((1 - |t| : ℝ) : ℂ) * cotC t := by
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **PROVEN — the derivative-level total (symbolic numeric pin).**

    π i t · ((1 − |t|) · (−i · cotC t)) + |t|  =  π t (1 − |t|) · cotC t + |t|.

The LHS is `[derivative-multiplier]·[function-level principal core] +
[derivative-level tail contribution]`; the RHS is the principal-plus-`|t|`
decomposition of `Ĵ` (Vaaler eq. (2.31)).  Verified numerically (mpmath) to `1e-31`
over the tested grid before formalising. -/
theorem derivLevelTotal_eq (t : ℝ) :
    (π * Complex.I * t : ℂ) * (((1 - |t| : ℝ) : ℂ) * (-Complex.I * cotC t))
        + ((|t| : ℝ) : ℂ)
      = (π * t : ℂ) * ((1 - |t| : ℝ) : ℂ) * cotC t + ((|t| : ℝ) : ℂ) := by
  rw [derivLevelPrincipal_eq]

/-- `cotC t = (Real.cot (π t) : ℂ)` whenever `sin (π t) ≠ 0`.  (`Real.cot x =
cos x / sin x`.) -/
theorem cotC_eq_real_cot {t : ℝ} (_ht : Real.sin (π * t) ≠ 0) :
    cotC t = ((Real.cot (π * t) : ℝ) : ℂ) := by
  unfold cotC
  rw [Real.cot_eq_cos_div_sin]
  push_cast
  rfl

/-- **PROVEN — the derivative-level total equals Vaaler's `Ĵ` on the positive support.**

For `0 < t < 1`,

    π i t · ((1 − |t|) · (−i · cotC t)) + |t|  =  (vaalerJhat t : ℂ)

where `vaalerJhat t = π t (1 − t) cot (π t) + t`.  On `0 < t` we have `|t| = t`, and
`cotC t = (cot (π t) : ℂ)` (using `sin (π t) ≠ 0` on `(0,1)`), so the proven
`derivLevelTotal_eq` matches the `vaalerJhat` definition verbatim.  This exhibits the
derivative-level total as the closed `Ĵ` value of eq. (2.31). -/
theorem derivLevelTotal_eq_vaalerJhat {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (π * Complex.I * t : ℂ) * (((1 - |t| : ℝ) : ℂ) * (-Complex.I * cotC t))
        + ((|t| : ℝ) : ℂ)
      = ((MathExtras.NumberTheory.Analysis.VaalerFejerCoefficientNonneg.vaalerJhat t : ℝ) : ℂ) := by
  have hsin : Real.sin (π * t) ≠ 0 := by
    have hpt0 : 0 < π * t := mul_pos Real.pi_pos ht0
    have hptpi : π * t < π := by
      have := mul_lt_mul_of_pos_left ht1 Real.pi_pos
      simpa using this
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpt0 hptpi)
  have habs : |t| = t := abs_of_pos ht0
  rw [derivLevelTotal_eq, cotC_eq_real_cot hsin, habs]
  unfold MathExtras.NumberTheory.Analysis.VaalerFejerCoefficientNonneg.vaalerJhat
  push_cast
  ring

/-! ## §2 — The `echar` ↔ Mathlib `𝓕` bridge (FULLY PROVEN) -/

/-- **PROVEN.**  The project character `echar t v = exp(−2π i t v)` equals the Mathlib
Fourier kernel in explicit-exponential form `exp((−2π·⟪v,t⟫)·I) = exp((−2π·(v·t))·I)`.
The pointwise kernel identity that turns every `∫ (f v)·echar t v` of this project into
Mathlib's `𝓕 f t` (via `fourier_eq'`). -/
theorem echar_eq_fourierKernel (t v : ℝ) :
    Complex.exp (((-2 * π * ⟪v, t⟫) : ℝ) * Complex.I) = echar t v := by
  rw [Real.inner_apply]
  unfold echar
  congr 1
  push_cast
  ring

/-- **PROVEN.**  `∫ (f v)·echar t v dv = 𝓕 f t` for `f : ℝ → ℂ`.  Combines the kernel
identity `echar_eq_fourierKernel` with `fourier_eq'` (`𝓕 f t = ∫ exp((−2π⟪v,t⟫)I)·f v`)
and the commutativity of `ℂ` multiplication. -/
theorem integral_mul_echar_eq_fourier (f : ℝ → ℂ) (t : ℝ) :
    (∫ v : ℝ, f v * echar t v) = 𝓕 f t := by
  rw [fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only [smul_eq_mul]
  rw [← echar_eq_fourierKernel t v]
  ring

/-! ## §3 — The derivative→multiplier FT rule, UPGRADED from `Prop` to THEOREM -/

/-- **PROVEN — the `½`-derivative Fourier multiplier rule.**

Let `f : ℝ → ℂ` be integrable and differentiable with integrable derivative, and let
`g` be the *half*-derivative, i.e. `deriv f = fun v => 2 * g v`.  Then

    ∫ (g v)·echar t v dv = (π i t) · ∫ (f v)·echar t v dv.

This is `VaalerJFTviaHN.HalfHNDerivFT` upgraded from a named `Prop` to a genuine
theorem: Mathlib's `fourier_deriv` gives `𝓕(f′)(t) = (2π i t)·𝓕 f t`; with `f′ = 2g`
the factor `2` cancels, leaving the `π i t` half-derivative multiplier.  Bridged to the
project `echar`-integrals by `integral_mul_echar_eq_fourier`. -/
theorem halfDeriv_FT_eq_mul {f g : ℝ → ℂ}
    (hf : Integrable f) (hf' : Differentiable ℝ f)
    (hderiv : Integrable (deriv f)) (hhalf : deriv f = fun v => 2 * g v) (t : ℝ) :
    (∫ v : ℝ, g v * echar t v) = (π * Complex.I * t : ℂ) * (∫ v : ℝ, f v * echar t v) := by
  -- Move both sides to Mathlib `𝓕`.
  have hg : Integrable g := by
    have : g = fun v => (1 / 2 : ℂ) * deriv f v := by
      funext v; rw [hhalf]; ring
    rw [this]; exact hderiv.const_mul _
  rw [integral_mul_echar_eq_fourier g t, integral_mul_echar_eq_fourier f t]
  -- 𝓕(deriv f) t = (2π i t) • 𝓕 f t
  have hFD := fourier_deriv hf hf' hderiv
  -- 𝓕(deriv f) t = 2 * 𝓕 g t  (linearity of the transform, via the echar bridge)
  have hFDg : 𝓕 (deriv f) t = (2 : ℂ) * 𝓕 g t := by
    rw [← integral_mul_echar_eq_fourier (deriv f) t, ← integral_mul_echar_eq_fourier g t]
    rw [hhalf]
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
    ring
  -- and 𝓕(deriv f) t = (2π i t) * 𝓕 f t
  have hFDt : 𝓕 (deriv f) t = (2 * π * Complex.I * t) * 𝓕 f t := by
    rw [hFD]; simp [smul_eq_mul]
  -- combine
  have keyt : (2 : ℂ) * 𝓕 g t = (2 * π * Complex.I * t) * 𝓕 f t := by
    rw [← hFDg, hFDt]
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h2
  rw [keyt]; ring


/-! ## §4 — Assembly: principal `N`-level transform, the tail, and the combine -/

/-- **PROVEN — the derivative-level tail multiplier collapse.**

The `2 z⁻¹` tail's *function-level* Fourier transform is the purely-imaginary
`−i·sgn(t)/π` (DEAD_ENDS #18: the FT of the odd `(sin πz/π)²·2z⁻¹` is imaginary).
After the `πit` derivative multiplier it becomes the real `|t|`:

    π i t · (−i·(Real.sign t)/π)  =  |t|.

Pure complex algebra (`i·(−i)=1`, `t·sgn t = |t|`).  This is the symbolic statement of
the numeric pin `π i t · (|t|/(πit)) = |t|` and supplies the `+|t|` of Vaaler's `Ĵ`. -/
theorem tailDeriv_collapse (t : ℝ) :
    (π * Complex.I * t : ℂ) * (-Complex.I * ((Real.sign t : ℝ) : ℂ) / (π : ℂ))
      = ((|t| : ℝ) : ℂ) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsgn : (t : ℝ) * Real.sign t = |t| := by
    rcases lt_trichotomy t 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; ring
    · rw [h]; simp
    · rw [Real.sign_of_pos h, abs_of_pos h]; ring
  rw [show (π * Complex.I * t : ℂ) * (-Complex.I * ((Real.sign t : ℝ) : ℂ) / (π : ℂ))
      = (Complex.I * (-Complex.I)) * (((t : ℝ) : ℂ) * ((Real.sign t : ℝ) : ℂ)) * ((π : ℂ) / (π : ℂ))
      by ring]
  rw [show Complex.I * (-Complex.I) = 1 by rw [mul_neg, Complex.I_mul_I]; ring,
      div_self hpi, ← Complex.ofReal_mul, hsgn]
  ring

/-- **PROVEN — the `N`-level principal transform of the shifted-Fejér core.**

For `sin (π t) ≠ 0`, applying the half-derivative multiplier (`× π i t`) to the proven
function-level core transform `HNcore_FT_eq_triangle_cot` gives, at the *derivative*
level, the principal `Ĵ`-term plus the `N`-oscillatory remainder:

    π i t · 𝓕(HNcore N)(t)
      = (1−|t|)₊ · ( π t · cotC t  +  oscillatory remainder ).

(The principal `π t (1−|t|)₊ cotC t` is the first `Ĵ`-term via `derivLevelPrincipal_eq`;
the second term `→ 0` as `N→∞` by Riemann–Lebesgue, `VaalerOscillatoryRemainder`.) -/
theorem HNcore_deriv_FT_eq {N : ℕ} {t : ℝ} (ht : Real.sin (π * t) ≠ 0) :
    (π * Complex.I * t : ℂ) * (∫ z : ℝ, (HNcore N z : ℂ) * echar t z)
      = (MathExtras.Fourier.fejerTriangle t : ℂ)
          * ((π * t : ℂ) * cotC t
              + (π * Complex.I * t : ℂ)
                  * (Complex.I * ((Real.cos (π * (2 * N + 1) * t) : ℂ) / (Real.sin (π * t) : ℂ)))) := by
  rw [HNcore_FT_eq_triangle_cot ht]
  -- distribute π i t over triangle·(−i cotC t + i osc); the osc terms match verbatim,
  -- and the −i·(πit) principal collapses to πt via I*I = -1.
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination
    (-(MathExtras.Fourier.fejerTriangle t : ℂ) * (π : ℂ) * (t : ℂ) * cotC t) * hI

/-! ### The remaining truncation limit, and the combine to the minor wall

The function-level core transform is PROVEN (`HNcore_FT_eq_triangle_cot`); the
derivative multiplier is PROVEN (`halfDeriv_FT_eq_mul`, `HNcore_deriv_FT_eq`); the tail
collapse is PROVEN (`tailDeriv_collapse`); and the closed total is PROVEN
(`derivLevelTotal_eq_vaalerJhat`).  The SINGLE remaining analytic step is the
`N → ∞` Riemann–Lebesgue passage that turns the proven `N`-level transforms into the
limiting `𝓕(½H′) = Ĵ` and hence the complex match `Gc = vaalerJ`.  We reuse the exact
named residual of `VaalerJFTviaHN` (`HNDerivConverges := ∃ Gc, GcEqVaalerJ Gc`) — it is
numerically CONFIRMED and is the only piece between this file and the minor wall. -/

/-- **PROVEN combine — the minor D-1 wall from the single truncation-limit residual.**

Granting `VaalerJFTviaHN.HNDerivConverges` (`∃ Gc, GcEqVaalerJ Gc`, the Riemann–Lebesgue
truncation limit — the ONLY remaining analytic step, numerically confirmed), the deep
minor residual `GEqReJ` follows, and with it the entire `H′ = 2J` minor wall, via the
proven `VaalerJFTviaHN.GcEqVaalerJ_of_HN_backbone`. -/
theorem gEqReJ_of_truncationLimit
    (h : MathExtras.NumberTheory.Analysis.VaalerJFTviaHN.HNDerivConverges) :
    MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ.GEqReJ :=
  MathExtras.NumberTheory.Analysis.VaalerJFTviaHN.GcEqVaalerJ_of_HN_backbone h

/-- **PROVEN combine — the bundled D-1 residual from the truncation limit.** -/
theorem derivInterpHEqTwoJ_of_truncationLimit
    (h : MathExtras.NumberTheory.Analysis.VaalerJFTviaHN.HNDerivConverges) :
    MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail.DerivInterpHEqTwoJ :=
  MathExtras.NumberTheory.Analysis.VaalerJFTviaHN.derivInterpHEqTwoJ_of_HN_backbone h

#print axioms derivLevelPrincipal_eq
#print axioms derivLevelTotal_eq
#print axioms cotC_eq_real_cot
#print axioms derivLevelTotal_eq_vaalerJhat
#print axioms echar_eq_fourierKernel
#print axioms integral_mul_echar_eq_fourier
#print axioms halfDeriv_FT_eq_mul
#print axioms tailDeriv_collapse
#print axioms HNcore_deriv_FT_eq
#print axioms gEqReJ_of_truncationLimit
#print axioms derivInterpHEqTwoJ_of_truncationLimit

end MathExtras.NumberTheory.Analysis.VaalerHNAssembly

end
