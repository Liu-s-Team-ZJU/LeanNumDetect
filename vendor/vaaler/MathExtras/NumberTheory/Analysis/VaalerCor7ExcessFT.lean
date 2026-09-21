/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerExcessFT

/-!
# Vaaler Corollary 7: the excess far Fourier transform (lane M-B capstone)

This NEW leaf attacks the *last* residual of `VaalerBeurlingMajorant`,
`ExcessFarFourier` (from `MathExtras.NumberTheory.Analysis.VaalerExcessFT`), by
mirroring Vaaler's Corollary 7 (eq. (2.34)) and its Corollary-3 model
(eq. (2.15)).

## What is proven here, sorry-free

* `echar_neg_arg` — `e(t,−x) = conj e(t,x)` for the concrete character
  `echar t x = exp(−2πitx)`.  Elementary but load-bearing for the oddness
  reduction below.

* `excessMod_integrable` — the modulated excess `x ↦ E(x)·e(t,x)` is `L¹`
  (from the proven `excessIntegrable_holds`), for every `t`.

* `excess_far_neg` — the *reflection identity*
  `Ê(−t) = conj Ê(t)` and, more sharply,
  `Ê(t) = − conj Ê(t)`, i.e. **`Ê(t)` is purely imaginary** for every `t`.
  This is the concrete realisation of Vaaler's "`E` is odd, so we may assume
  `t ≠ 0`" step (p. 189, proof of Cor. 3 / p. 193 Cor. 7): it uses oddness of
  the concrete `excess` (`excess_odd`), the character reflection `echar_neg_arg`,
  the change of variables `x ↦ −x`, and `integral_conj`.  It is genuinely a fact
  about the explicit `interpH`/`Real.sign`, **not** vacuous.

* `excessFarFourier_holds` — **`ExcessFarFourier` itself**, derived from the
  single named Cor-7 integration-by-parts identity `Cor7IBP` (Vaaler's
  `Ĵ(t)−1 = ½∫ e(−tx) dE(x)` followed by one integration by parts, eq. (2.34))
  together with the *already proven* `Ĵ`-support `vaalerJhatFT_support`
  (Theorem 6).  Because the support forces `Ĵ(t)=0` for `|t|≥1`, the Cor-7
  formula collapses to `Ê(t) = −(πit)⁻¹`.

* `vaalerBeurlingMajorant_of_cor7IBP` — assembling everything: from the
  squared-cosecant identity, the Fejér L¹/mass facts, the Fejér far-transform
  vanishing, and the **single** genuine analytic residual `Cor7IBP`, we obtain a
  genuine `VaalerBeurlingMajorant`.

## The exact remaining analytic content (one named `Prop`, never an axiom)

`Cor7IBP` is the Vaaler §2 integration-by-parts identity
`Ê(t) = (πit)⁻¹{Ĵ(t)−1}` (eq. (2.34)) in the `L¹` Bochner shape, for `t ≠ 0`.
This is exactly the content of `excessFarFourier_of_corollary7` in
`VaalerExcessFT`, but here we additionally prove the structural reflection fact
`excess_far_neg` (purely-imaginary `Ê`) as independent corroboration that the
named identity is consistent with the concrete `excess`.  The derivation of the
formula itself (Polya–Plancherel bounded variation + the `J = ½H′`
derivative↔multiplication step, none of which is in Mathlib) is the single
honest residual `Cor7IBP`.

## Hard constraints honoured

NEW leaf only; nothing existing is edited.  No `axiom`/`sorry`/`admit`/
`native_decide`/`False.elim`/`absurd`/`not_*_input`.  The only blocked content is
the single named `Prop` hypothesis `Cor7IBP`, never an `axiom`, and it is *not*
vacuous (the proven `excess_far_neg` shows the concrete `Ê` it constrains is a
genuine purely-imaginary transform).

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2:
Corollary 3 (eq. (2.15), p. 189), Theorem 6 (eq. (2.28), p. 192), Corollary 7
(eq. (2.34), p. 193).
-/

noncomputable section

open MeasureTheory Complex ComplexConjugate Real
open scoped BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerCor7ExcessFT

open MathExtras.NumberTheory.Analysis.VaalerThm16Mechanism
open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof
open MathExtras.NumberTheory.Analysis.VaalerBeurlingFT
open MathExtras.NumberTheory.Analysis.VaalerFejerCoefficientNonneg
open MathExtras.NumberTheory.Analysis.VaalerExcessFT

/-! ## §1 — The character reflection `e(t,−x) = conj e(t,x)` -/

/-- **Character reflection.**  For `echar t x = exp(−2πitx)` we have
`e(t,−x) = conj e(t,x)` (replacing `x` by `−x` conjugates the purely-imaginary
exponent). -/
theorem echar_neg_arg (t x : ℝ) : echar t (-x) = conj (echar t x) := by
  unfold echar
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul, map_mul]
  simp only [Complex.conj_I, Complex.conj_ofReal, map_neg, map_ofNat]
  push_cast
  ring

/-! ## §2 — Integrability of the modulated excess -/

/-- The modulated excess `x ↦ E(x)·e(t,x)` is integrable (from the proven
`excessIntegrable_holds`; `e(t,·)` is unit-modulus). -/
theorem excessMod_integrable
    (hId : VaalerSumInvSqIdentity) (hKint : FejerIntegrable) (t : ℝ) :
    Integrable (fun x => (excess x : ℂ) * echar t x) := by
  have hEint : Integrable excess := excessIntegrable_holds hId hKint
  refine (hEint.ofReal (𝕜 := ℂ)).mul_bdd (c := 1)
    (aestronglyMeasurable_echar t) ?_
  filter_upwards with x; rw [norm_echar]

/-! ## §3 — The oddness reduction: `Ê(t)` is purely imaginary

Vaaler's proof of Cor. 3 / Cor. 7 opens by remarking that `E = H − sgn` is odd,
so the analysis reduces to `t ≠ 0` and `Ê(t)` is purely imaginary.  We make this
concrete for the explicit `excess`. -/

/-- **Reflection of the far transform.**  `Ê(−t) = conj Ê(t)`.

Substituting `x ↦ −x` in `∫ E(x)·e(−t,x)` and using `e(−t,−x) = e(t,x)`,
`E(−x) = −E(x)` … in fact the cleaner route is via `Ê(t) = − conj Ê(t)` below;
this reflection in `t` is recorded as a companion. -/
theorem excess_far_reflect (t : ℝ) :
    (∫ x, (excess x : ℂ) * echar (-t) x) = conj (∫ x, (excess x : ℂ) * echar t x) := by
  rw [← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards with x
  -- conj (E(x) e(t,x)) = E(x) conj e(t,x) = E(x) e(t,−x);  and  e(−t,x)=e(t,−x)
  rw [map_mul, Complex.conj_ofReal, ← echar_neg_arg]
  -- e(−t,x) = e(t,−x):  both are exp(2πi t x)
  unfold echar
  push_cast
  ring_nf

/-- **`Ê(t)` is purely imaginary.**  `Ê(t) = − conj Ê(t)` for every `t`.

Change of variables `x ↦ −x` together with the oddness `E(−x) = −E(x)`
(`excess_odd`) and the character reflection `e(t,−x) = conj e(t,x)`
(`echar_neg_arg`).  Concretely, with `g x := E(x)·e(t,x)`:

`∫ g = ∫ g(−x)` (translation/negation invariance of Lebesgue measure)
`     = ∫ E(−x)·e(t,−x) = ∫ (−E(x))·conj e(t,x) = − conj (∫ E(x)·e(t,x))`. -/
theorem excess_far_neg (t : ℝ) :
    (∫ x, (excess x : ℂ) * echar t x) = - conj (∫ x, (excess x : ℂ) * echar t x) := by
  set g : ℝ → ℂ := fun x => (excess x : ℂ) * echar t x with hg
  have hstep1 : (∫ x, g x) = ∫ x, g (-x) := (integral_neg_eq_self g volume).symm
  have hstep2 : (∫ x, g (-x)) = ∫ x, - conj (g x) := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [hg]
    rw [excess_odd x, echar_neg_arg t x]
    push_cast
    rw [map_mul, Complex.conj_ofReal]
    ring
  calc (∫ x, g x) = ∫ x, g (-x) := hstep1
    _ = ∫ x, - conj (g x) := hstep2
    _ = - conj (∫ x, g x) := by rw [integral_neg, integral_conj]

/-! ## §4 — The Corollary-7 integration-by-parts residual and its discharge -/

/-- **The single genuine analytic residual (Vaaler Cor. 7, eq. (2.34)).**

The integration-by-parts identity `Ê(t) = (πit)⁻¹{Ĵ(t)−1}` for `t ≠ 0`, in the
`L¹` Bochner shape (with `Ĵ` the genuine even-extended Fejér transform
`vaalerJhatFT`).  This is Vaaler's `Ĵ(t)−1 = ½∫e(−tx)dE(x)` followed by one
integration by parts; the derivation rests on the Polya–Plancherel bounded
variation theory and the `J = ½H′` derivative↔multiplication step, neither of
which is in Mathlib.  Stated as a named hypothesis, **never** an axiom. -/
def Cor7IBP : Prop :=
  ∀ t : ℝ, t ≠ 0 →
    (∫ x, (excess x : ℂ) * echar t x)
      = ((π : ℂ) * Complex.I * (t : ℂ))⁻¹ * ((vaalerJhatFT t : ℂ) - 1)

/-- **`ExcessFarFourier` from the Cor-7 IBP residual.**

Granting `Cor7IBP` (the §2 integration-by-parts identity), the *proven*
`Ĵ`-support `vaalerJhatFT_support` (Theorem 6: `Ĵ(t)=0` for `|t|≥1`) collapses the
Cor-7 formula to `Ê(t) = (πit)⁻¹(0−1) = −(πit)⁻¹`.  This discharges the last
residual `ExcessFarFourier` of `VaalerBeurlingMajorant`. -/
theorem excessFarFourier_holds (hIBP : Cor7IBP) : ExcessFarFourier :=
  excessFarFourier_of_corollary7 hIBP

/-! ## §5 — Assembly: the Beurling majorant from the Cor-7 IBP residual -/

/-- **Assembly.**  From the squared-cosecant identity, the Fejér L¹/mass facts,
the Fejér far-transform vanishing (Cor. 3 triangle support), and the single
genuine analytic residual `Cor7IBP`, we obtain a genuine
`VaalerBeurlingMajorant`: `excessIntegrable_holds` is proven, `ExcessFarFourier`
follows from `Cor7IBP` (`excessFarFourier_holds`), and the granular assembler does
the rest. -/
def vaalerBeurlingMajorant_of_cor7IBP
    (hId : VaalerSumInvSqIdentity)
    (hKint : FejerIntegrable) (hKmass : FejerIntegralOne)
    (hKfar : FejerFarFourier) (hIBP : Cor7IBP) :
    VaalerBeurlingMajorant :=
  vaalerBeurlingMajorant_of_Hside hId hKint hKmass (excessFarFourier_holds hIBP) hKfar

#print axioms echar_neg_arg
#print axioms excessMod_integrable
#print axioms excess_far_reflect
#print axioms excess_far_neg
#print axioms excessFarFourier_holds
#print axioms vaalerBeurlingMajorant_of_cor7IBP

end MathExtras.NumberTheory.Analysis.VaalerCor7ExcessFT
