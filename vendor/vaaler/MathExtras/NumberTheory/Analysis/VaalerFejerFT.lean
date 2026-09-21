/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Fejér-kernel Fourier facts (Vaaler 1985, eq. 2.29) — MINOR track, lane M-A

This NEW leaf discharges the Fejér-kernel residuals of `VaalerBeurlingFT.lean`
for the **concrete** Fejér kernel `fejerK` of `VaalerBeurlingNonneg.lean`:

  `fejerK x = if x = 0 then 1 else (sin πx / π)² · x⁻²`,  i.e. `(sin πx / (πx))²`.

The math (Vaaler eq. 2.29): `K(z) = ∫_{-1}^1 (1 − |t|) e(tz) dt`, the Fejér
kernel is the inverse Fourier transform of the triangle `Λ(t) = (1−|t|)₊`.
Consequences:
* `K̂(t) = (1 − |t|)₊` (triangle), supported on `[−1,1]` ⇒ `K̂(t) = 0` for `|t| ≥ 1`;
* `∫_ℝ K = K̂(0) = 1`;
* `K` integrable.

## How it is proven (no axiom, no sorry, no `native_decide`, no vacuous proof)

The repo already contains the FULL sinc-square Fourier theory, proven sorry-free
in `MathExtras/Analysis/Fourier/SincSquare.lean`, for the kernel
`MathExtras.Fourier.sincSqPi x = (Real.sinc (π x))²`:

* `sincSqPi_integrable`                                  — `Integrable sincSqPi`;
* `integral_sincSqPi`                                    — `∫ sincSqPi = 1`;
* `integral_sincSqPi_mul_cos_eq_fejerTriangle`           — cosine moment `= (1−|ξ|)₊`;
* `integral_sincSqPi_mul_sin_eq_zero`                    — sine moment `= 0`;
* `fejerTriangle_eq_zero_of_one_le_abs`                  — `(1−|ξ|)₊ = 0` for `1 ≤ |ξ|`.

The ONLY gap to Vaaler's concrete `fejerK` is the *definitional* bridge
`fejerK x = sincSqPi x` (both equal `(sin πx/(πx))²` with removable value `1` at
`0`), proven sorry-free in `fejerK_eq_sincSqPi`.  Through it:

* `fejerIntegrable_holds : FejerIntegrable`  — `Integrable fejerK`;
* `fejerIntegralOne_holds : FejerIntegralOne` — `∫ fejerK = 1` (`= K̂(0)`);
* `fejerFarFourier_holds`                    — the far-FT vanishing
  `∀ t, 1 ≤ |t| → ∫ x, (fejerK x) e(t,x) = 0` in the exact `echar` shape that
  `VaalerBeurlingFT`'s `ftFar`/`PhiFarFourier` consumes (`K̂(t) = 0` for `|t| ≥ 1`).

No residual hypothesis remains: all three are outright theorems about the
concrete `fejerK`, each with `#print axioms = [propext, Classical.choice,
Quot.sound]`.

## Book

Vaaler, Bull. AMS 12 (1985), §2 eq. (2.29); §4 (the Fejér transform `K̂ = (1−|t|)₊`).
-/

import MathExtras.NumberTheory.Analysis.VaalerBeurlingFT
import MathExtras.Analysis.Fourier.SincSquare

noncomputable section

open MeasureTheory Complex Real
open scoped BigOperators FourierTransform

namespace MathExtras.NumberTheory.Analysis.VaalerFejerFT

open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerThm16Mechanism
open MathExtras.NumberTheory.Analysis.VaalerBeurlingFT

/-! ## The definitional bridge `fejerK = sincSqPi` -/

/-- **The concrete Fejér kernel is the `sinc²` kernel** (sorry-free).

`fejerK x = if x = 0 then 1 else (sin πx / π)² · x⁻²` agrees pointwise with
`MathExtras.Fourier.sincSqPi x = (Real.sinc (π x))²`.  At `x = 0` both are `1`;
for `x ≠ 0`, `Real.sinc (π x) = sin(πx)/(πx)`, so `sincSqPi x = sin²(πx)/(π²x²)
= (sin πx/π)² · x⁻²`. -/
theorem fejerK_eq_sincSqPi (x : ℝ) : fejerK x = MathExtras.Fourier.sincSqPi x := by
  unfold fejerK MathExtras.Fourier.sincSqPi Real.sinc
  by_cases hx : x = 0
  · subst hx; simp
  · have hπx : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx
    rw [if_neg hx, if_neg hπx]
    field_simp

/-- `fejerK = sincSqPi` as functions. -/
theorem fejerK_eq_sincSqPi_fun : fejerK = MathExtras.Fourier.sincSqPi :=
  funext fejerK_eq_sincSqPi

/-! ## `FejerIntegrable` — `K ∈ L¹(ℝ)` -/

/-- **(Vaaler Cor. 3, L¹ — Fejér piece.)**  The concrete Fejér kernel `fejerK`
is Lebesgue integrable, from the sorry-free `sincSqPi_integrable` via the bridge
`fejerK = sincSqPi`. -/
theorem fejerIntegrable_holds : FejerIntegrable := by
  unfold FejerIntegrable
  rw [fejerK_eq_sincSqPi_fun]
  exact MathExtras.Fourier.sincSqPi_integrable

/-! ## `FejerIntegralOne` — `∫ K = K̂(0) = 1` -/

/-- **(Vaaler eq. 2.29 / §4 at `t = 0`.)**  `∫ fejerK = 1`, from the sorry-free
`integral_sincSqPi` via the bridge `fejerK = sincSqPi`. -/
theorem fejerIntegralOne_holds : FejerIntegralOne := by
  unfold FejerIntegralOne
  rw [fejerK_eq_sincSqPi_fun]
  exact MathExtras.Fourier.integral_sincSqPi

/-! ## The far Fourier transform vanishing `K̂(t) = 0` for `|t| ≥ 1`

The character consumed by `VaalerBeurlingFT` is
`echar t x = exp(−2π i t x) = cos(2π t x) − i sin(2π t x)`.  The complex Fejér
transform `∫ x, (fejerK x) e(t,x)` therefore splits as
`(∫ K cos(2π t x)) − i (∫ K sin(2π t x)) = K̂(t)` (real part is the cosine moment
`(1−|t|)₊`, imaginary part is the sine moment `0`).  For `1 ≤ |t|` the triangle
`(1−|t|)₊ = 0`, so the whole transform vanishes. -/

/-- `echar t x = cos(2π t x) − i sin(2π t x)` (the real-line character expanded). -/
theorem echar_eq_cos_sub_sin (t x : ℝ) :
    echar t x = (Real.cos (2 * π * t * x) : ℂ)
        - Complex.I * (Real.sin (2 * π * t * x) : ℂ) := by
  unfold echar
  have hz : (-2 : ℂ) * π * Complex.I * t * x
      = ((-(2 * π * t * x) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hz, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- The cosine Fejér moment, in `fejerK` form. -/
theorem integral_fejerK_mul_cos (t : ℝ) :
    (∫ x : ℝ, fejerK x * Real.cos (2 * π * t * x))
      = MathExtras.Fourier.fejerTriangle t := by
  have h := MathExtras.Fourier.integral_sincSqPi_mul_cos_eq_fejerTriangle t
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [fejerK_eq_sincSqPi]

/-- The sine Fejér moment, in `fejerK` form. -/
theorem integral_fejerK_mul_sin (t : ℝ) :
    (∫ x : ℝ, fejerK x * Real.sin (2 * π * t * x)) = 0 := by
  have h := MathExtras.Fourier.integral_sincSqPi_mul_sin_eq_zero t
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [fejerK_eq_sincSqPi]

/-- `x ↦ (fejerK x) · cos(2π t x)` is integrable (bounded `cos` factor). -/
theorem integrable_fejerK_mul_cos (t : ℝ) :
    Integrable (fun x => fejerK x * Real.cos (2 * π * t * x)) := by
  have hInt : Integrable fejerK := fejerIntegrable_holds
  refine hInt.mul_bdd (c := 1)
    (Real.continuous_cos.comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _

/-- `x ↦ (fejerK x) · sin(2π t x)` is integrable (bounded `sin` factor). -/
theorem integrable_fejerK_mul_sin (t : ℝ) :
    Integrable (fun x => fejerK x * Real.sin (2 * π * t * x)) := by
  have hInt : Integrable fejerK := fejerIntegrable_holds
  refine hInt.mul_bdd (c := 1)
    (Real.continuous_sin.comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _

/-- **The complex Fejér transform splits into the cosine and sine moments.**

`∫ x, (fejerK x) e(t,x) = (∫ K cos(2π t x)) − i (∫ K sin(2π t x))`, the real /
imaginary parts of `K̂(t)`. -/
theorem integral_fejerK_echar_eq (t : ℝ) :
    (∫ x, (fejerK x : ℂ) * echar t x)
      = ((∫ x : ℝ, fejerK x * Real.cos (2 * π * t * x)) : ℝ)
        - Complex.I * ((∫ x : ℝ, fejerK x * Real.sin (2 * π * t * x)) : ℝ) := by
  have hcong : (fun x => (fejerK x : ℂ) * echar t x)
      = fun x => ((fejerK x * Real.cos (2 * π * t * x) : ℝ) : ℂ)
          - Complex.I * ((fejerK x * Real.sin (2 * π * t * x) : ℝ) : ℂ) := by
    funext x
    rw [echar_eq_cos_sub_sin]
    push_cast
    ring
  rw [hcong]
  rw [integral_sub (integrable_fejerK_mul_cos t).ofReal
    (((integrable_fejerK_mul_sin t).ofReal).const_mul _)]
  rw [MeasureTheory.integral_const_mul]
  norm_cast

/-- **(Vaaler eq. 2.29 / §4 — the far Fourier transform vanishing.)**

`K̂(t) = 0` for `|t| ≥ 1`, in the exact `echar` shape `VaalerBeurlingFT`'s
`ftFar`/`PhiFarFourier` consumes: `∀ t, 1 ≤ |t| → ∫ x, (fejerK x) e(t,x) = 0`.
Since `K̂(t)` is the triangle `(1−|t|)₊`, which vanishes for `|t| ≥ 1`. -/
theorem fejerFarFourier_holds :
    ∀ t : ℝ, 1 ≤ |t| → (∫ x, (fejerK x : ℂ) * echar t x) = 0 := by
  intro t ht
  rw [integral_fejerK_echar_eq, integral_fejerK_mul_cos, integral_fejerK_mul_sin,
    MathExtras.Fourier.fejerTriangle_eq_zero_of_one_le_abs ht]
  simp

#print axioms fejerK_eq_sincSqPi
#print axioms fejerIntegrable_holds
#print axioms fejerIntegralOne_holds
#print axioms echar_eq_cos_sub_sin
#print axioms fejerFarFourier_holds

end MathExtras.NumberTheory.Analysis.VaalerFejerFT

end
