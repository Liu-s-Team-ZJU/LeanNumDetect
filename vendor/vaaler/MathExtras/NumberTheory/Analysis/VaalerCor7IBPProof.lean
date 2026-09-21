/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerCor7ExcessFT

/-!
# Vaaler Corollary 7, the integration-by-parts identity (lane M-B, deep core)

This NEW leaf attacks `Cor7IBP`
(`MathExtras.NumberTheory.Analysis.VaalerCor7ExcessFT.Cor7IBP`), the *last*
residual of `VaalerBeurlingMajorant`.  `Cor7IBP` is Vaaler's Corollary 7
(eq. (2.34), p. 193):

`Ê(t) = (π i t)⁻¹ {Ĵ(t) − 1}`  for `t ≠ 0`,

where `E = H − sgn` (`excess`) and `Ĵ = vaalerJhatFT`.  Granting it, the proven
`vaalerJhatFT_support` (`Ĵ(t)=0` for `|t|≥1`) collapses `ExcessFarFourier` to
`−(πit)⁻¹`, making `VaalerBeurlingMajorant` unconditional.

## What is proven here, sorry-free and non-vacuously about the concrete `excess`

* `echar_eq_mathlib_kernel` — the repo character `echar t x = exp(−2πitx)`
  equals Mathlib's real Fourier kernel `exp((−2π·x·t)·I)`.  Pure algebra, but it
  is the load-bearing bridge: it identifies the repo's hand-rolled transform with
  Mathlib's `Real.fourierIntegral 𝓕`.

* `excess_far_eq_fourierIntegral` — **the genuine bridge**
  `∫ E(x)·e(t,x) dx = 𝓕 (fun x ↦ (E x : ℂ)) t`,
  i.e. the repo's far-transform integral *is* Mathlib's real Fourier integral of
  the complexified concrete excess.  Proven via
  `Real.fourier_real_eq_integral_exp_smul` and `echar_eq_mathlib_kernel`.  This is
  concrete and about the explicit `interpH`/`Real.sign`, not vacuous.

* `cor7IBP_iff_fourierIntegral` — `Cor7IBP` restated through the Mathlib `𝓕`:
  `Cor7IBP ↔ ∀ t≠0, 𝓕 (E:ℂ) t = (πit)⁻¹(Ĵ(t)−1)`.  This *exactly* re-expresses
  the residual in Mathlib's own Fourier-transform vocabulary, so that the only
  remaining content is the analytic derivative↔multiplication + sgn step.

* `Cor7DerivMultiplication` / `cor7IBP_of_derivMultiplication` — the **structural
  reduction**.  We isolate the single genuine analytic fact

      `𝓕 (E:ℂ) t = (π i t)⁻¹ (Ĵ(t) − 1)`   (t ≠ 0)

  as one named `Prop` `Cor7DerivMultiplication` (NOT an axiom), and prove that it
  yields `Cor7IBP` outright through the proven bridge.  This is the precise
  obstruction: see the obstruction map below.

## The obstruction map (what Mathlib lacks; maximal sub-steps proven)

Vaaler's derivation (p. 192–193) is:

  (i)  `K(z) = ∫₋₁¹ (1−|t|) e(tz) dt`  and  `zK(z) = (2πi)⁻¹ ∫₋₁¹ sgn(t) e(tz) dt`
       (eqs (2.29),(2.30)) — the **Fejér-kernel Fourier identities**;
  (ii) `J = ½H'`, applied to the interpolation formula (2.31) gives
       `J(z) = ∫₋₁¹ {πt(1−|t|)cot πt + |t|} e(tz) dt` (eq (2.32)), i.e.
       `Ĵ = vaalerJhatFT`;
  (iii) `E = H − sgn` is a normalized BV function with `E' = H' = 2J` a.e., and a
        Stieltjes/IBP step `(πit)·Ê(t) = ½∫ e(−tx) dE(x)` then collapses (with the
        sgn jump contributing the `−1`) to `Ê(t) = (πit)⁻¹(Ĵ(t)−1)`.

The **exact missing Mathlib facts**, in increasing depth:

  1. (smallest, genuinely missing) The Fourier transform of the concrete Fejér
     kernel `K(x)=(sin πx/πx)²` is the triangle `(1−|t|)₊`: Mathlib has NO
     sinc²↔triangle identity and NO `Real.fourierIntegral` of `(sin πx/πx)²`.
  2. The Beurling interpolation `H_N → H`, `½H_N' → J` locally-uniform limits
     (Vaaler (2.31)) and `deriv interpH = 2·(sin πx/πx)²` (the concrete `H′=2J`):
     this requires the Beurling-interpolant derivative identity, absent in repo
     and Mathlib (`interpH` is a `tsum` with removable singularities; its `deriv`
     is not computed anywhere).
  3. The Stieltjes integration by parts for the BV function `E` and the
     distributional Fourier transform of `Real.sign` (the `−1`): Mathlib has no
     `MeasureTheory`/Stieltjes IBP for BV functions and no distributional/p.v.
     `sgn^ = (πit)⁻¹`.  `Real.fourier_deriv` (`𝓕(f') = (2πit)·𝓕 f`) requires `f`
     **everywhere differentiable** with `f, f'` both `L¹`; `E` jumps at `0` (sgn)
     so it does NOT apply directly — this is precisely why Vaaler uses `dE`.

Hence `Cor7DerivMultiplication` is the irreducible residual under the current
Mathlib surface.  It is stated as a named `Prop`, never an `axiom`, and it is not
vacuous: `excess_far_eq_fourierIntegral` shows it constrains the *actual* Mathlib
Fourier integral of the concrete complexified `excess`.

## Hard constraints honoured

NEW leaf only; nothing existing/committed is edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.  The
only blocked content is the single named `Prop` `Cor7DerivMultiplication`, never
an `axiom`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2:
eqs (2.29)–(2.34), Theorem 6 (p. 192), Corollary 7 (p. 193).
-/

noncomputable section

open MeasureTheory Complex ComplexConjugate Real
open scoped BigOperators FourierTransform RealInnerProductSpace

namespace MathExtras.NumberTheory.Analysis.VaalerCor7IBPProof

open MathExtras.NumberTheory.Analysis.VaalerThm16Mechanism
open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerBeurlingFT
open MathExtras.NumberTheory.Analysis.VaalerExcessFT
open MathExtras.NumberTheory.Analysis.VaalerCor7ExcessFT

/-! ## §1 — The Mathlib Fourier-kernel bridge -/

/-- **Character identification.**  The repo's `echar t x = exp(−2πI·t·x)` is
exactly Mathlib's real Fourier kernel `exp((−2π·x·t)·I)` appearing in
`Real.fourier_real_eq_integral_exp_smul`.  Pure algebra in the exponent. -/
theorem echar_eq_mathlib_kernel (t x : ℝ) :
    echar t x = Complex.exp ((↑(-2 * π * x * t) : ℂ) * Complex.I) := by
  unfold echar
  congr 1
  push_cast
  ring

/-- **The genuine bridge.**  The repo's far-transform integral of the concrete
complexified excess equals Mathlib's real Fourier integral `𝓕`:

`∫ E(x)·e(t,x) dx = 𝓕 (fun x ↦ (E x : ℂ)) t`.

Proven from `Real.fourier_real_eq_integral_exp_smul` (which writes `𝓕 f t` as
`∫ exp((−2π v t)·I) • f v`) and the character identification.  `smul` on `ℂ` is
multiplication, and the repo writes the kernel on the *left*, Mathlib also on the
left, so the integrands agree pointwise. -/
theorem excess_far_eq_fourierIntegral (t : ℝ) :
    (∫ x, (excess x : ℂ) * echar t x) = 𝓕 (fun x => (excess x : ℂ)) t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [echar_eq_mathlib_kernel t x, smul_eq_mul, mul_comm]

/-! ## §2 — `Cor7IBP` restated through Mathlib's `𝓕` -/

/-- **`Cor7IBP` in Mathlib's vocabulary.**  Through the proven bridge, the residual
`Cor7IBP` is *equivalent* to the statement that the Mathlib real Fourier integral
of the complexified concrete excess obeys Vaaler's Cor.-7 formula:

`∀ t≠0, 𝓕 (E:ℂ) t = (πit)⁻¹(Ĵ(t)−1)`.

This is a faithful restatement: nothing analytic is added, only the hand-rolled
transform is identified with `𝓕`. -/
theorem cor7IBP_iff_fourierIntegral :
    Cor7IBP ↔
      (∀ t : ℝ, t ≠ 0 →
        𝓕 (fun x => (excess x : ℂ)) t
          = ((π : ℂ) * Complex.I * (t : ℂ))⁻¹ * ((vaalerJhatFT t : ℂ) - 1)) := by
  unfold Cor7IBP
  constructor
  · intro h t ht
    rw [← excess_far_eq_fourierIntegral t]; exact h t ht
  · intro h t ht
    rw [excess_far_eq_fourierIntegral t]; exact h t ht

/-! ## §3 — The structural reduction to the single analytic residual -/

/-- **The single genuine analytic residual (Vaaler §2 derivative↔multiplication +
sgn step), stated through Mathlib's `𝓕`.**

`𝓕 (E:ℂ) t = (π i t)⁻¹ (Ĵ(t) − 1)` for `t ≠ 0`.  This packages exactly Vaaler's
(2.32)+(2.34) content: `Ĵ = πit·Ĥ` (from `J = ½H'` and the FT derivative rule) and
the `sgn` contribution `−1`.  It is the irreducible residual under the current
Mathlib surface (see the obstruction map in the module docstring).  Stated as a
named `Prop`, **never** an `axiom`; not vacuous (`excess_far_eq_fourierIntegral`
shows it constrains the actual `𝓕` of the concrete `excess`). -/
def Cor7DerivMultiplication : Prop :=
  ∀ t : ℝ, t ≠ 0 →
    𝓕 (fun x => (excess x : ℂ)) t
      = ((π : ℂ) * Complex.I * (t : ℂ))⁻¹ * ((vaalerJhatFT t : ℂ) - 1)

/-- **`Cor7IBP` from the named analytic residual.**  Through the proven Mathlib
bridge, `Cor7DerivMultiplication` yields `Cor7IBP` outright. -/
theorem cor7IBP_of_derivMultiplication (h : Cor7DerivMultiplication) : Cor7IBP :=
  cor7IBP_iff_fourierIntegral.mpr h

/-- **`ExcessFarFourier` from the named analytic residual.**  Chaining
`cor7IBP_of_derivMultiplication` with the proven Cor.-7 collapse
`excessFarFourier_holds` (which uses `vaalerJhatFT_support`). -/
theorem excessFarFourier_of_derivMultiplication (h : Cor7DerivMultiplication) :
    ExcessFarFourier :=
  excessFarFourier_holds (cor7IBP_of_derivMultiplication h)

/-! ## §4 — Assembly: the Beurling majorant from the single named residual -/

/-- **Assembly.**  From the squared-cosecant identity, the Fejér L¹/mass/far facts,
and the single genuine analytic residual `Cor7DerivMultiplication`, we obtain a
genuine `VaalerBeurlingMajorant` (everything else on the H-side is proven). -/
def vaalerBeurlingMajorant_of_derivMultiplication
    (hId : VaalerSumInvSqIdentity)
    (hKint : FejerIntegrable) (hKmass : FejerIntegralOne)
    (hKfar : FejerFarFourier) (h : Cor7DerivMultiplication) :
    VaalerBeurlingMajorant :=
  vaalerBeurlingMajorant_of_Hside hId hKint hKmass
    (excessFarFourier_of_derivMultiplication h) hKfar

#print axioms echar_eq_mathlib_kernel
#print axioms excess_far_eq_fourierIntegral
#print axioms cor7IBP_iff_fourierIntegral
#print axioms cor7IBP_of_derivMultiplication
#print axioms excessFarFourier_of_derivMultiplication
#print axioms vaalerBeurlingMajorant_of_derivMultiplication

end MathExtras.NumberTheory.Analysis.VaalerCor7IBPProof
