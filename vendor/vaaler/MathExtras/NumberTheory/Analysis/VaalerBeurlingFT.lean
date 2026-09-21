/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AnalyticNT.Diophantine.VaalerThm16Mechanism
import AnalyticNT.Diophantine.VaalerBeurlingNonneg
import MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof

/-!
# The Fourier-transform fields of `VaalerBeurlingMajorant` (Vaaler Cor. 3 / Cor. 7)

This leaf assembles the full Beurling majorant structure
`VaalerBeurlingMajorant`
(`MathExtras.NumberTheory.Analysis.VaalerThm16Mechanism`) for the **concrete**
Beurling function `φ = H + K − sgn` whose pieces `interpH`, `fejerK`, `phi` are
defined in `VaalerBeurlingNonneg`.

## The math (Vaaler 1985, §2)

* `K(x) = (sin πx / πx)²` (Fejér).  Its Fourier transform is the triangle
  `K̂(t) = (1 − |t|)₊`, supported on `[−1,1]`; in particular `∫ K = K̂(0) = 1` and
  `K̂(t) = 0` for `|t| ≥ 1`.
* `E := H − sgn` (Cor. 7, eq. (2.34)): `Ê(t) = (πit)⁻¹{Ĵ(t) − 1}` for `t ≠ 0`,
  where `Ĵ` (Vaaler's `vaalerJhat`, repo `VaalerFejerCoefficientNonneg`) is
  supported on `[−1,1]` (Theorem 6, `Ĵ(t)=0` for `|t| ≥ 1`).  Hence for `|t| ≥ 1`
  `Ê(t) = (πit)⁻¹(0 − 1) = −(πit)⁻¹`.  Also `E` is odd and integrable, so
  `∫ E = 0`.
* `φ = E + K`, so for `|t| ≥ 1`: `φ̂(t) = Ê(t) + K̂(t) = −(πit)⁻¹ + 0 = −(πit)⁻¹`
  (= `ftFar`), and `∫ φ = ∫ E + ∫ K = 0 + 1 = 1` (= `ft0`).

## What is delivered (NEW leaf; no axiom, no sorry, no vacuous proof)

The nonnegativity field (`nonneg`) is the proven `vaaler_phi_nonneg`, made
**unconditional** here by supplying the discharged
`vaalerSumInvSqIdentity_holds` (the squared cosecant identity is proven
`sorry`-free in `VaalerSumInvSqProof`).  So `nonneg` is genuinely closed.

The three remaining fields rest on Fourier-analytic facts about the concrete
`phi` that are **not available in Mathlib** (Mathlib has no Fejér-kernel /
sinc² Fourier transform, no Paley–Wiener band-limiting theorem, and Vaaler's
Theorem 6 support statement `Ĵ(t)=0` for `|t|≥1` is not in the repo either —
`vaalerJhat` is only defined and shown nonnegative on `[0,1]`).  Each is
therefore isolated as a **precisely named, dischargeable hypothesis (`Prop`)**
about the concrete `phi`, *not* an `axiom`:

* `PhiIntegrable`  — `Integrable phi`  (sinc² ∈ L¹ + `H − sgn` ∈ L¹).
* `PhiIntegralOne` — `∫ phi = 1`       (`∫ K = 1` and `∫ (H − sgn) = 0`).
* `PhiFarFourier`  — `∀ t, 1 ≤ |t| → ∫ (φ x) e(t,x) = −(πit)⁻¹`
                                       (Cor. 3/7 + Theorem 6 support).

Given these three, the structure is assembled and the sixth field
(`integrableMod`, modulation by the unit-modulus character) is **proven
outright** from `PhiIntegrable` (the same `mul_bdd` argument used in the
mechanism file).  Thus `vaalerBeurlingMajorant_of_fourier` reduces the entire
residual to exactly these three named analytic statements.

Moreover the **oddness half** of unit-mass is discharged here outright:
`integral_excess_eq_zero : ∫ (H − sgn) = 0` is proven via
`integral_neg_eq_self` and `excess_odd` (no integrability hypothesis needed).
Consequently `vaalerBeurlingMajorant_of_granular` assembles the structure from
the **finer** residual set — `FejerIntegralOne` (`∫ K = 1`), `FejerIntegrable`,
`ExcessIntegrable`, `PhiFarFourier` — in which the unit-mass field needs only
`∫ K = 1` (the Fejér mass), not the full `∫ φ = 1`.

Discharging the three is the remaining classical Fourier-analysis work (Vaaler
§2 Cor. 3/7 + Thm 6); none is declared as an `axiom` and none is vacuous —
they are concrete, satisfiable statements about the explicit `phi`.

## Book

Vaaler, Bull. AMS 12 (1985), §2: Theorem 6 (eq. 2.28), Cor. 3 (eq. 2.15),
Cor. 7 (eqs. 2.29/2.34).
-/

noncomputable section

open MeasureTheory Complex Real
open scoped BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerBeurlingFT

open MathExtras.NumberTheory.Analysis.VaalerThm16Mechanism
open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof

/-! ## The concrete majorant `φ = H + K − sgn`

We work with the function `phi` defined in `VaalerBeurlingNonneg`:
`phi x = interpH x + fejerK x - Real.sign x`. -/

/-- `phi` is unconditionally nonnegative (Vaaler Lemma 5), the discharged
`nonneg` field.  Uses the proven squared cosecant identity. -/
theorem phi_nonneg (x : ℝ) : 0 ≤ phi x :=
  vaaler_phi_nonneg
    MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds x

/-! ## The three named analytic residuals about the concrete `phi`

These are concrete statements about the explicit `phi = H + K − sgn`; they are
the Fourier-analytic content of Vaaler Cor. 3 / Cor. 7 / Thm 6 that is not in
Mathlib.  They are threaded as hypotheses, never declared as `axiom`s. -/

/-- **Residual (Vaaler Cor. 3, L¹).**  The concrete Beurling majorant
`φ = H + K − sgn` is Lebesgue integrable over `ℝ`.  (`K = (sin πx/πx)²` is in
`L¹`; `H − sgn` is in `L¹` by Vaaler's bound `|sgn − H| ≤ K`.) -/
def PhiIntegrable : Prop := Integrable phi

/-- **Residual (Vaaler Cor. 3, eq. 2.15 at `t = 0`).**  `∫ φ = 1`, i.e.
`φ̂(0) = 1` (`∫ K = 1` and `∫ (H − sgn) = 0` by oddness). -/
def PhiIntegralOne : Prop := ∫ x, phi x = 1

/-- **Residual (Vaaler Cor. 7, eq. 2.34 + Thm 6 support).**  The far Fourier
transform of the concrete `φ` is `−(π i t)⁻¹` for `|t| ≥ 1`. -/
def PhiFarFourier : Prop :=
  ∀ t : ℝ, 1 ≤ |t| →
    (∫ x, (phi x : ℂ) * echar t x) = -((π : ℂ) * Complex.I * (t : ℂ))⁻¹

/-! ## Genuinely proven sub-facts (no extra hypothesis)

The "`∫ (H − sgn) = 0` by oddness" half of `PhiIntegralOne` is proven outright
here, so the unit-mass residual collapses to the single Fejér fact `∫ K = 1`
(given integrability of the two pieces).  Likewise `PhiIntegrable` is split into
the two genuinely separate L¹ inputs. -/

/-- The Beurling excess `E(x) = H(x) − sgn(x)`. -/
def excess (x : ℝ) : ℝ := interpH x - Real.sign x

/-- `φ = E + K` pointwise (regrouping the concrete `phi`). -/
theorem phi_eq_excess_add_fejerK (x : ℝ) : phi x = excess x + fejerK x := by
  unfold phi excess; ring

/-- **The excess is odd.**  `E(−x) = −E(x)`, from `interpH_neg` (proven in
`VaalerBeurlingNonneg`) and oddness of `Real.sign`. -/
theorem excess_odd (x : ℝ) : excess (-x) = - excess x := by
  unfold excess
  rw [interpH_neg, Real.sign_neg]; ring

/-- **The integral of an odd function over `ℝ` vanishes** (unconditional: uses
`integral_neg_eq_self`; no integrability hypothesis needed — both sides are the
Bochner integral, which is `0` for non-integrable functions, and the identity
`∫ g(−x) = ∫ g(x)` together with `g(−x) = −g(x)` forces `∫ g = 0`). -/
theorem integral_eq_zero_of_odd {g : ℝ → ℝ} (hodd : ∀ x, g (-x) = - g x) :
    ∫ x, g x = 0 := by
  have h1 : (∫ x, g (-x)) = ∫ x, g x := integral_neg_eq_self g volume
  have h2 : (∫ x, g (-x)) = ∫ x, - g x := by
    refine integral_congr_ae ?_; filter_upwards with x; rw [hodd]
  rw [h2, integral_neg] at h1
  linarith

/-- **`∫ (H − sgn) = 0`** — the oddness half of unit-mass, proven outright. -/
theorem integral_excess_eq_zero : ∫ x, excess x = 0 :=
  integral_eq_zero_of_odd excess_odd

/-- **Residual (Fejér mass).**  `∫ K = 1` for the concrete Fejér kernel
`K = (sin πx/πx)²`.  (Mathlib has no Fejér / sinc² integral.) -/
def FejerIntegralOne : Prop := ∫ x, fejerK x = 1

/-- **Residual (Fejér L¹).**  `K ∈ L¹(ℝ)`. -/
def FejerIntegrable : Prop := Integrable fejerK

/-- **Residual (excess L¹).**  `E = H − sgn ∈ L¹(ℝ)` (Vaaler `|sgn − H| ≤ K`). -/
def ExcessIntegrable : Prop := Integrable excess

/-- `PhiIntegrable` from the two genuinely separate L¹ pieces. -/
theorem phiIntegrable_of (hE : ExcessIntegrable) (hK : FejerIntegrable) :
    PhiIntegrable := by
  have : phi = fun x => excess x + fejerK x := funext phi_eq_excess_add_fejerK
  rw [PhiIntegrable, this]; exact hE.add hK

/-- **`∫ φ = 1` from the Fejér mass alone** (the oddness half is already proven).
Given `∫ K = 1` and integrability of the two pieces, the split
`∫ φ = ∫ E + ∫ K = 0 + 1 = 1` closes the unit-mass field. -/
theorem phiIntegralOne_of (hE : ExcessIntegrable) (hK : FejerIntegrable)
    (hmass : FejerIntegralOne) : PhiIntegralOne := by
  have hsplit : (∫ x, phi x) = (∫ x, excess x) + ∫ x, fejerK x := by
    have hcongr : (fun x => phi x) = fun x => excess x + fejerK x :=
      funext phi_eq_excess_add_fejerK
    rw [show (∫ x, phi x) = ∫ x, (excess x + fejerK x) from by rw [hcongr]]
    exact integral_add hE hK
  rw [PhiIntegralOne, hsplit, integral_excess_eq_zero, hmass, zero_add]

/-! ## Glue: `integrableMod` from `PhiIntegrable` (proven outright) -/

/-- Given integrability of `phi`, the modulated function `x ↦ (φ x) e(t,x)` is
integrable for every `t` (the character `e(t,·)` is unit modulus).  This is the
same `mul_bdd` argument used for the scaled majorant in the mechanism file. -/
theorem phi_integrableMod (hInt : PhiIntegrable) (t : ℝ) :
    Integrable (fun x => (phi x : ℂ) * echar t x) := by
  refine (hInt.ofReal (𝕜 := ℂ)).mul_bdd (c := 1)
    (aestronglyMeasurable_echar t) ?_
  filter_upwards with x
  rw [norm_echar]

/-! ## The assembly -/

/-- **Assembly of the Beurling majorant from the three Fourier residuals.**

Given the integrability (`PhiIntegrable`), the unit-mass (`PhiIntegralOne`),
and the far Fourier transform (`PhiFarFourier`) of the concrete `φ = H + K − sgn`,
together with the *unconditionally proven* nonnegativity `phi_nonneg`, we obtain
a genuine `VaalerBeurlingMajorant` whose carrier function is exactly the concrete
`phi`.  The `integrableMod` field is derived from `PhiIntegrable`.

This reduces Theorem 16's residual to exactly the three named hypotheses. -/
def vaalerBeurlingMajorant_of_fourier
    (hInt : PhiIntegrable) (hMass : PhiIntegralOne) (hFar : PhiFarFourier) :
    VaalerBeurlingMajorant where
  φ := phi
  nonneg := phi_nonneg
  integrable := hInt
  ft0 := hMass
  ftFar := hFar
  integrableMod := fun t => phi_integrableMod hInt t

/-- The same as a `Nonempty` statement. -/
theorem vaalerBeurlingMajorant_nonempty_of_fourier
    (hInt : PhiIntegrable) (hMass : PhiIntegralOne) (hFar : PhiFarFourier) :
    Nonempty VaalerBeurlingMajorant :=
  ⟨vaalerBeurlingMajorant_of_fourier hInt hMass hFar⟩

/-- **Assembly from the granular residuals** (`∫ K = 1`, `K ∈ L¹`, `E ∈ L¹`,
far transform).  Here the unit-mass field uses only the Fejér mass `∫ K = 1`;
the oddness half `∫ E = 0` is already discharged.  This is the tightest residual
set: four concrete Fourier-analytic facts, two of them shared between the
integrability and mass fields. -/
def vaalerBeurlingMajorant_of_granular
    (hE : ExcessIntegrable) (hK : FejerIntegrable)
    (hmass : FejerIntegralOne) (hFar : PhiFarFourier) :
    VaalerBeurlingMajorant :=
  vaalerBeurlingMajorant_of_fourier
    (phiIntegrable_of hE hK) (phiIntegralOne_of hE hK hmass) hFar

/-! ## Downstream: the full Vaaler 6.8 bound from the three residuals

Composing the assembly with the proven mechanism `vaaler_thm16_of_beurlingMajorant`
gives the real-line Hilbert/cosecant inequality (6.8) conditional only on the
three concrete Fourier residuals. -/

/-- **(VAALER THEOREM 16, eq. 6.8 — from the three concrete Fourier residuals.)**
For `δ`-separated real frequencies and complex coefficients,
`‖∑_{m≠n} a_m conj(a_n) / (i(λ_m − λ_n))‖ ≤ (π/δ)·∑‖a_n‖²`, conditional only on
the integrability, unit-mass and far-transform of the concrete `φ = H + K − sgn`. -/
theorem vaaler_thm16_of_fourierResiduals
    (hInt : PhiIntegrable) (hMass : PhiIntegralOne) (hFar : PhiFarFourier)
    {N : ℕ} (lam : Fin N → ℝ) (a : Fin N → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsp : ∀ m n, m ≠ n → δ ≤ |lam m - lam n|) :
    ‖hilbertForm lam a‖ ≤ (π / δ) * ∑ n, ‖a n‖ ^ 2 :=
  vaaler_thm16_of_beurlingMajorant
    (vaalerBeurlingMajorant_of_fourier hInt hMass hFar) lam a hδ hsp

#print axioms phi_nonneg
#print axioms integral_excess_eq_zero
#print axioms phi_integrableMod
#print axioms vaalerBeurlingMajorant_of_fourier
#print axioms vaalerBeurlingMajorant_of_granular
#print axioms vaaler_thm16_of_fourierResiduals

end MathExtras.NumberTheory.Analysis.VaalerBeurlingFT
