/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerJDecayBound

/-!
# Vaaler eq. (2.27): the two-IBP `O(z^{-2})` decay, via the integration-by-parts engine

This NEW leaf attacks the single remaining residual `VaalerJTwoIBPDecay` of
`VaalerJDecayBound` (Vaaler eq. (2.27), `J(z) ≪ (1+|z|)^{-2}`).  It does so by building,
**fully and unconditionally**, the *integration-by-parts engine* that Vaaler's §2 IBP
argument runs on, and reducing `VaalerJTwoIBPDecay` to a single clean named `Prop`
packaging exactly the piecewise-`C²` data of the explicit Fejér transform `Ĵ`.

## The mathematics (Vaaler §2, two integrations by parts on one smooth piece)

`vaalerJ z = ∫_{-1}^1 Ĵ(τ) e(τz) dτ`, `e(τz) = echarPos τ z = exp(2π i z τ)`.  The
character has the explicit antiderivative `(2π i z)⁻¹ e(τz)` in `τ`
(`hasDerivAt_echarPos`).  On a single smooth piece `[a,b]` where `Ĵ` is `C²`, two
integrations by parts give

    ∫_a^b f(τ) e(τz) dτ
      = w⁻¹ (f(b)e(bz) − f(a)e(az))                       -- first IBP boundary
        − w⁻² (f'(b)e(bz) − f'(a)e(az))                   -- second IBP boundary
        + w⁻² ∫_a^b f''(τ) e(τz) dτ,        w := 2π i z   -- second IBP remainder

so, since `‖e‖ = 1`,

    ‖∫_a^b f e‖ ≤ |w|⁻¹(|f(a)|+|f(b)|) + |w|⁻²(|f'(a)|+|f'(b)| + ∫_a^b‖f''‖).

For `|z| ≥ 1` we have `|w| = 2π|z| ≥ 2π`, so the `|w|⁻¹` term is itself `≤ (2π)⁻¹|z|⁻¹`,
and `|z|⁻¹ ≤ |z|⁻²·|z| ≤ …`; more cleanly we expose the *full two-IBP closed form* and
the *one-piece norm bound* below.  When `f` vanishes at the endpoints (the genuine Fejér
situation `Ĵ(±1)=0`) the first boundary term drops out entirely and the whole piece is
`O(z^{-2})`.

## What is PROVEN here (sorry-free, axiom-free, non-vacuous)

* `hasDerivAt_echarPos` — `HasDerivAt (fun τ => echarPos τ z) (2π i z · echarPos τ z) τ`,
  the derivative of the character in `τ` (chain rule on `exp`).  Hence
  `(2π i z)⁻¹·echarPos · z` is an explicit antiderivative.
* `norm_two_pi_I_z` — `‖(2π i z : ℂ)‖ = 2π|z|`.
* `oneIBP_piece` — **(PROVEN)** the *first* IBP closed form on a piece `[a,b]`
  (`a ≤ b`): for `C¹` complex `f` (with integrable `f'`),
  `∫_a^b f·e = w⁻¹(f(b)e(bz) − f(a)e(az)) − w⁻¹∫_a^b f'·e`, `w = 2π i z`.
* `twoIBP_piece` — **(PROVEN)** the *two*-IBP closed form: applying `oneIBP_piece`
  again to `∫ f'·e` gives the displayed three-term formula above.
* `norm_twoIBP_piece_le` — **(PROVEN)** the one-piece norm bound
  `‖∫_a^b f·e‖ ≤ |w|⁻¹(‖f a‖+‖f b‖) + |w|⁻²(‖f' a‖+‖f' b‖+∫_a^b‖f''‖)` (unit-modulus
  character + the triangle inequality).
* `norm_twoIBP_piece_vanishing_le` — **(PROVEN)** the *endpoint-vanishing* specialisation
  (`f a = f b = 0`): `‖∫_a^b f·e‖ ≤ |w|⁻²(‖f' a‖+‖f' b‖+∫_a^b‖f''‖)`, i.e. genuinely
  `O(z^{-2})` with NO surviving `z^{-1}` term — the heart of Vaaler (2.27).

These are concrete, fully-proven facts about the explicit character `echarPos`; the
engine runs Mathlib's `intervalIntegral.integral_mul_deriv_eq_deriv_mul`.

## The single remaining genuine gap (named `Prop`, NOT an axiom)

The only thing left is to feed the engine the explicit piecewise-`C²` data of the Fejér
transform `Ĵ = vaalerJhatCont` on the two smooth pieces `[-1,0]`, `[0,1]` together with
the endpoint values `Ĵ(±1)=0` and the corner values `Ĵ'(0^±)`, `Ĵ''`.  That explicit
differentiation of `Ĵ(τ)=π τ(1−|τ|)cot πτ+|τ|` (its `cot`-derivatives and the corner
bookkeeping at `{−1,0,1}`) is isolated as the single named `Prop`:

* `VaalerJhatPiecewiseC2Data` — there exist `f', f'' : ℝ → ℂ` and uniform bounds making
  `vaalerJ` satisfy, on each of `[-1,0]`, `[0,1]`, the `C²` hypotheses
  (`HasDerivAt` chains + integrable `f''`) with `Ĵ` vanishing at `±1`, plus a uniform
  modulus bound on the endpoint `f'` values and the `∫‖f''‖`.

`vaalerJTwoIBPDecay_of_data` then derives `VaalerJTwoIBPDecay` from it via the proven
engine (`norm_twoIBP_piece_vanishing_le` summed over the two pieces, with the corner-`0`
terms cancelling/bounded), and `jDecayBound_of_twoIBP`/`jIntegrable_of_twoIBP` carry it
to `JIntegrable`.

## Hard constraints honoured

NEW leaf only; nothing existing/committed is edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.  The single
blocked piece is the named `Prop` `VaalerJhatPiecewiseC2Data`, never an `axiom`.  The IBP
engine itself (`oneIBP_piece`, `twoIBP_piece`, `norm_twoIBP_piece_le`,
`norm_twoIBP_piece_vanishing_le`) is fully proven and non-vacuous: a concrete identity
and estimate for `∫ f·echarPos` over any piece.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eq. (2.27), p. 192 (the two integrations by parts giving `J ≪ (1+|z|)^{-2}`).
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology intervalIntegral
open scoped BigOperators FourierTransform

namespace MathExtras.NumberTheory.Analysis.VaalerJ227Decay

open MathExtras.NumberTheory.Analysis.VaalerFejerCoefficientNonneg
open MathExtras.NumberTheory.Analysis.VaalerExcessFT
open MathExtras.NumberTheory.Analysis.VaalerCor7RouteB
open MathExtras.NumberTheory.Analysis.VaalerTheorem6JFT
open MathExtras.NumberTheory.Analysis.VaalerJIntegrable
open MathExtras.NumberTheory.Analysis.VaalerJDecayBound

/-! ## §1 — The character `echarPos`, its derivative, and `w = 2π i z` -/

/-- The frequency factor `w = 2π i z` (the derivative multiplier of the character). -/
def wfreq (z : ℝ) : ℂ := 2 * π * Complex.I * z

/-- `echarPos τ z = exp(w·τ)`, `w = 2π i z`: the character as an exponential of `w·τ`. -/
theorem echarPos_eq_exp_wfreq (τ z : ℝ) :
    echarPos τ z = Complex.exp (wfreq z * (τ : ℂ)) := by
  unfold echarPos wfreq
  congr 1
  ring

/-- **PROVEN.**  `HasDerivAt (fun τ => echarPos τ z) (w · echarPos τ z) τ`, the
derivative of the character in `τ` (`w = 2π i z`).  Chain rule on `exp(w·τ)`. -/
theorem hasDerivAt_echarPos (z τ : ℝ) :
    HasDerivAt (fun s : ℝ => echarPos s z) (wfreq z * echarPos τ z) τ := by
  have hof : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) τ := by
    simpa using (hasDerivAt_id τ).ofReal_comp
  have hlin : HasDerivAt (fun s : ℝ => wfreq z * (s : ℂ)) (wfreq z) τ := by
    simpa using hof.const_mul (wfreq z)
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (wfreq z * (s : ℂ)))
      (Complex.exp (wfreq z * (τ : ℂ)) * wfreq z) τ := by
    simpa using hlin.cexp
  have hgoal : HasDerivAt (fun s : ℝ => Complex.exp (wfreq z * (s : ℂ)))
      (wfreq z * echarPos τ z) τ := by
    rw [echarPos_eq_exp_wfreq, mul_comm]
    exact hexp
  refine hgoal.congr_of_eventuallyEq ?_
  filter_upwards with s
  rw [echarPos_eq_exp_wfreq]

/-- `‖w‖ = 2π|z|`. -/
theorem norm_wfreq (z : ℝ) : ‖wfreq z‖ = 2 * π * |z| := by
  unfold wfreq
  rw [show (2 : ℂ) * π * Complex.I * z = ((2 * π * z : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2),
    abs_of_pos Real.pi_pos]

/-- `w ≠ 0` for `z ≠ 0`. -/
theorem wfreq_ne_zero {z : ℝ} (hz : z ≠ 0) : wfreq z ≠ 0 := by
  unfold wfreq
  have : (2 : ℂ) * π * Complex.I * z ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
    · exact Complex.I_ne_zero
    · exact_mod_cast hz
  exact this

/-! ## §2 — The antiderivative of the character and the first IBP on a piece -/

/-- The explicit antiderivative `Φ τ = w⁻¹·echarPos τ z` of the character (`w = 2π i z`,
`z ≠ 0`): `HasDerivAt Φ (echarPos τ z) τ`. -/
theorem hasDerivAt_echarPos_antideriv {z : ℝ} (hz : z ≠ 0) (τ : ℝ) :
    HasDerivAt (fun s : ℝ => (wfreq z)⁻¹ * echarPos s z) (echarPos τ z) τ := by
  have h := (hasDerivAt_echarPos z τ).const_mul (wfreq z)⁻¹
  have : (wfreq z)⁻¹ * (wfreq z * echarPos τ z) = echarPos τ z := by
    rw [← mul_assoc, inv_mul_cancel₀ (wfreq_ne_zero hz), one_mul]
  rwa [this] at h

/-- **PROVEN — the first IBP on a smooth piece `[a,b]` (`a ≤ b`).**  For complex `f`
*continuous on* `[a,b]` and differentiable on the OPEN interior `(a,b)` (with derivative
`f'`, interval-integrable), with NO derivative required at the endpoints (faithful to a
function with corners at `a`, `b`):

    ∫_a^b f(τ)·e(τz) dτ
      = w⁻¹·(f b·e(bz) − f a·e(az)) − w⁻¹·∫_a^b f'(τ)·e(τz) dτ.

(`w = 2π i z`, `z ≠ 0`.)  We apply `integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`
with `u = f`, `v = Φ = w⁻¹·e`, `v' = e`, then pull out `w⁻¹` from the `f'·Φ` integral.
Derivatives are taken in `Ioi x` form on the open interior only. -/
theorem oneIBP_piece {z : ℝ} (hz : z ≠ 0) {a b : ℝ} (hab : a ≤ b)
    {f f' : ℝ → ℂ}
    (hfc : ContinuousOn f (Set.uIcc a b))
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt f (f' x) (Set.Ioi x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    (∫ τ in a..b, f τ * echarPos τ z) =
      (wfreq z)⁻¹ * (f b * echarPos b z - f a * echarPos a z)
        - (wfreq z)⁻¹ * ∫ τ in a..b, f' τ * echarPos τ z := by
  set Φ : ℝ → ℂ := fun s => (wfreq z)⁻¹ * echarPos s z with hΦ
  -- min a b = a, max a b = b since a ≤ b
  have hmin : min a b = a := min_eq_left hab
  have hmax : max a b = b := max_eq_right hab
  -- IBP: ∫ f·Φ' = f b·Φ b − f a·Φ a − ∫ f'·Φ , with Φ' = echarPos
  have hΦc : ContinuousOn Φ (Set.uIcc a b) := by
    apply Continuous.continuousOn
    simp only [hΦ]; unfold echarPos; fun_prop
  have hΦd : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt Φ (echarPos x z) (Set.Ioi x) x := fun x _ =>
    (hasDerivAt_echarPos_antideriv hz x).hasDerivWithinAt
  have hfd : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt f (f' x) (Set.Ioi x) x := by
    rw [hmin, hmax]; exact hf
  -- echarPos is interval-integrable (continuous)
  have hechar_int : IntervalIntegrable (fun s => echarPos s z) volume a b := by
    apply Continuous.intervalIntegrable
    unfold echarPos; fun_prop
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := f) (v := Φ) (u' := f') (v' := fun s => echarPos s z)
    hfc hΦc hfd hΦd hf' hechar_int
  -- key : ∫ τ in a..b, f τ * echarPos τ z = f b * Φ b − f a * Φ a − ∫ τ in a..b, f' τ * Φ τ
  rw [key]
  -- now rewrite Φ b, Φ a and pull w⁻¹ out of the remaining integral
  simp only [hΦ]
  rw [show ∀ x : ℝ, f x * ((wfreq z)⁻¹ * echarPos x z)
        = (wfreq z)⁻¹ * (f x * echarPos x z) from fun x => by ring]
  rw [show (∫ τ in a..b, f' τ * ((wfreq z)⁻¹ * echarPos τ z))
        = (wfreq z)⁻¹ * ∫ τ in a..b, f' τ * echarPos τ z by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr ?_
        intro x _; ring]
  ring

/-! ## §3 — The second IBP and the two-IBP closed form on a piece -/

/-- **PROVEN — the two-IBP closed form on a smooth piece `[a,b]` (`a ≤ b`).**  For
complex `f, f', f''` continuous on `[a,b]` and differentiable on the OPEN interior
(`f` with `f'`, `f'` with `f''`), and `f', f''` interval-integrable:

    ∫_a^b f·e = w⁻¹(f b·e_b − f a·e_a)
              − w⁻²(f' b·e_b − f' a·e_a)
              + w⁻²·∫_a^b f''·e,        w = 2π i z, e_x = echarPos x z.

Apply `oneIBP_piece` to `f` (with `f'`), then again to `∫ f'·e` (with `f''`). -/
theorem twoIBP_piece {z : ℝ} (hz : z ≠ 0) {a b : ℝ} (hab : a ≤ b)
    {f f' f'' : ℝ → ℂ}
    (hfc : ContinuousOn f (Set.uIcc a b))
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt f (f' x) (Set.Ioi x) x)
    (hf'c : ContinuousOn f' (Set.uIcc a b))
    (hf'd : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt f' (f'' x) (Set.Ioi x) x)
    (hf' : IntervalIntegrable f' volume a b)
    (hf'' : IntervalIntegrable f'' volume a b) :
    (∫ τ in a..b, f τ * echarPos τ z) =
      (wfreq z)⁻¹ * (f b * echarPos b z - f a * echarPos a z)
        - (wfreq z)⁻¹ ^ 2 * (f' b * echarPos b z - f' a * echarPos a z)
        + (wfreq z)⁻¹ ^ 2 * ∫ τ in a..b, f'' τ * echarPos τ z := by
  have h1 := oneIBP_piece hz hab hfc hf hf'
  have h2 := oneIBP_piece hz hab hf'c hf'd hf''
  rw [h1, h2]
  ring

/-! ## §4 — The one-piece norm bound (two IBP) -/

/-- `‖f x · echarPos x z‖ = ‖f x‖` (unit-modulus character). -/
theorem norm_mul_echarPos (f : ℝ → ℂ) (x z : ℝ) :
    ‖f x * echarPos x z‖ = ‖f x‖ := by
  rw [norm_mul, norm_echarPos, mul_one]

/-- **PROVEN — the one-piece two-IBP norm bound.**  Under the `twoIBP_piece`
hypotheses, for `z ≠ 0` (so `‖w‖ = 2π|z| > 0`):

    ‖∫_a^b f·e‖ ≤ ‖w‖⁻¹(‖f a‖+‖f b‖) + ‖w‖⁻²(‖f' a‖+‖f' b‖ + ∫_a^b ‖f''‖).

Triangle inequality on the three terms of the closed form, `‖e‖ = 1`, and
`‖∫ f''·e‖ ≤ ∫‖f''·e‖ = ∫‖f''‖`. -/
theorem norm_twoIBP_piece_le {z : ℝ} (hz : z ≠ 0) {a b : ℝ} (hab : a ≤ b)
    {f f' f'' : ℝ → ℂ}
    (hfc : ContinuousOn f (Set.uIcc a b))
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt f (f' x) (Set.Ioi x) x)
    (hf'c : ContinuousOn f' (Set.uIcc a b))
    (hf'd : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt f' (f'' x) (Set.Ioi x) x)
    (hf' : IntervalIntegrable f' volume a b)
    (hf'' : IntervalIntegrable f'' volume a b) :
    ‖∫ τ in a..b, f τ * echarPos τ z‖ ≤
      ‖wfreq z‖⁻¹ * (‖f a‖ + ‖f b‖)
        + (‖wfreq z‖⁻¹) ^ 2 * (‖f' a‖ + ‖f' b‖ + ∫ τ in a..b, ‖f'' τ‖) := by
  rw [twoIBP_piece hz hab hfc hf hf'c hf'd hf' hf'']
  set w := wfreq z with hw
  have hwne : w ≠ 0 := wfreq_ne_zero hz
  have hwnorm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  -- bound each of the three terms
  -- term 1
  have ht1 : ‖w⁻¹ * (f b * echarPos b z - f a * echarPos a z)‖
      ≤ ‖w‖⁻¹ * (‖f a‖ + ‖f b‖) := by
    rw [norm_mul, norm_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul_echarPos, norm_mul_echarPos]
    rw [add_comm]
  -- term 2
  have ht2 : ‖w⁻¹ ^ 2 * (f' b * echarPos b z - f' a * echarPos a z)‖
      ≤ (‖w‖⁻¹) ^ 2 * (‖f' a‖ + ‖f' b‖) := by
    rw [norm_mul, norm_pow, norm_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul_echarPos, norm_mul_echarPos]
    rw [add_comm]
  -- term 3
  have ht3 : ‖w⁻¹ ^ 2 * ∫ τ in a..b, f'' τ * echarPos τ z‖
      ≤ (‖w‖⁻¹) ^ 2 * ∫ τ in a..b, ‖f'' τ‖ := by
    rw [norm_mul, norm_pow, norm_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
    apply le_of_eq
    refine intervalIntegral.integral_congr ?_
    intro x _; exact norm_mul_echarPos f'' x z
  calc ‖w⁻¹ * (f b * echarPos b z - f a * echarPos a z)
          - w⁻¹ ^ 2 * (f' b * echarPos b z - f' a * echarPos a z)
          + w⁻¹ ^ 2 * ∫ τ in a..b, f'' τ * echarPos τ z‖
      ≤ ‖w⁻¹ * (f b * echarPos b z - f a * echarPos a z)
          - w⁻¹ ^ 2 * (f' b * echarPos b z - f' a * echarPos a z)‖
          + ‖w⁻¹ ^ 2 * ∫ τ in a..b, f'' τ * echarPos τ z‖ := norm_add_le _ _
    _ ≤ (‖w⁻¹ * (f b * echarPos b z - f a * echarPos a z)‖
          + ‖w⁻¹ ^ 2 * (f' b * echarPos b z - f' a * echarPos a z)‖)
          + ‖w⁻¹ ^ 2 * ∫ τ in a..b, f'' τ * echarPos τ z‖ := by
            gcongr; exact norm_sub_le _ _
    _ ≤ (‖w‖⁻¹ * (‖f a‖ + ‖f b‖) + (‖w‖⁻¹) ^ 2 * (‖f' a‖ + ‖f' b‖))
          + (‖w‖⁻¹) ^ 2 * ∫ τ in a..b, ‖f'' τ‖ := by
            apply add_le_add (add_le_add ht1 ht2) ht3
    _ = ‖w‖⁻¹ * (‖f a‖ + ‖f b‖)
          + (‖w‖⁻¹) ^ 2 * (‖f' a‖ + ‖f' b‖ + ∫ τ in a..b, ‖f'' τ‖) := by ring

/-- **PROVEN — the endpoint-vanishing one-piece bound (heart of Vaaler (2.27)).**
If additionally `f a = 0` and `f b = 0` (the genuine Fejér situation `Ĵ(±1)=0` at the
outer endpoints), the surviving `‖w‖⁻¹` boundary term drops out and the whole piece is
`O(‖w‖⁻²)`:

    ‖∫_a^b f·e‖ ≤ ‖w‖⁻²(‖f' a‖+‖f' b‖+∫_a^b‖f''‖). -/
theorem norm_twoIBP_piece_vanishing_le {z : ℝ} (hz : z ≠ 0) {a b : ℝ} (hab : a ≤ b)
    {f f' f'' : ℝ → ℂ}
    (hfc : ContinuousOn f (Set.uIcc a b))
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt f (f' x) (Set.Ioi x) x)
    (hf'c : ContinuousOn f' (Set.uIcc a b))
    (hf'd : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt f' (f'' x) (Set.Ioi x) x)
    (hf' : IntervalIntegrable f' volume a b)
    (hf'' : IntervalIntegrable f'' volume a b)
    (ha0 : f a = 0) (hb0 : f b = 0) :
    ‖∫ τ in a..b, f τ * echarPos τ z‖ ≤
      (‖wfreq z‖⁻¹) ^ 2 * (‖f' a‖ + ‖f' b‖ + ∫ τ in a..b, ‖f'' τ‖) := by
  have h := norm_twoIBP_piece_le hz hab hfc hf hf'c hf'd hf' hf''
  rw [ha0, hb0] at h
  simpa using h

/-! ## §5 — `‖w‖⁻² = (2π)⁻²·(z²)⁻¹` and the two-piece assembly -/

/-- `(‖w‖⁻¹)² = ((2π)²)⁻¹·(z²)⁻¹` for `z ≠ 0` (`‖w‖ = 2π|z|`). -/
theorem normW_inv_sq (z : ℝ) :
    (‖wfreq z‖⁻¹) ^ 2 = ((2 * π) ^ 2)⁻¹ * (z ^ 2)⁻¹ := by
  rw [norm_wfreq, mul_inv, mul_pow, inv_pow, inv_pow, ← sq_abs z]

/-! ## §6 — The single named residual: the piecewise-`C²` data of `Ĵ`

The IBP engine above is fully proven.  The *only* remaining ingredient is to supply the
explicit closed-form `C²` data of the Fejér transform `Ĵ` on the two smooth pieces
`[-1,0]` and `[0,1]`, with the outer endpoints `Ĵ(±1)=0`.  That explicit differentiation
of `Ĵ(τ)=π τ(1−|τ|)cot πτ+|τ|` (the `cot`-derivatives plus the corner bookkeeping at
`{−1,0,1}`) is isolated here as ONE named `Prop` (never an `axiom`, and a TRUE statement
about the explicit `vaalerJ`). -/

/-- **Residual (Vaaler (2.27) piecewise-`C²` data).**  There exist complex piece
functions for the two smooth pieces of `Ĵ`:

* `[-1,0]`:  `fL` (`= Ĵ`-integrand here) with `C²` data `fL', fL''`, vanishing at the
  outer endpoint (`fL(-1)=0`);
* `[0,1]`:   `fR` with `C²` data `fR', fR''`, vanishing at the outer endpoint
  (`fR(1)=0`);

and a uniform corner/`C²` budget `K`, such that

* (i)   the `vaalerJ` integral splits as `∫_{-1}^0 fL·e + ∫_0^1 fR·e`;
* (ii)  each piece carries the `C²` structure `twoIBP_piece` consumes (continuity on the
        closed piece, interior `HasDerivWithinAt` chains, integrable `fL''`, `fR''`);
* (iii) the OUTER endpoints vanish: `fL(-1)=0`, `fR(1)=0`;
* (iv)  the inner endpoint values *match*: `fL 0 = fR 0` (Ĵ continuous at `0`), so the
        surviving first-IBP boundary character terms cancel exactly across `0`;
* (v)   the second-IBP budgets `‖fL'(-1)‖+‖fL' 0‖+∫‖fL''‖` and
        `‖fR' 0‖+‖fR' 1‖+∫‖fR''‖` are each `≤ K`.

This is exactly the explicit-`Ĵ` content (its `cot`-derivatives and the corner jump of
`Ĵ'` at `0`); it is TRUE about the concrete `vaalerJ`, NOT a vacuous hypothesis and NOT
an `axiom`. -/
def VaalerJhatPiecewiseC2Data : Prop :=
  ∃ (fL fL' fL'' fR fR' fR'' : ℝ → ℂ) (K : ℝ),
    -- (i) the integrand split: vaalerJ = ∫_{-1}^0 fL·e + ∫_0^1 fR·e
    (∀ z : ℝ, vaalerJ z
        = (∫ τ in (-1 : ℝ)..(0 : ℝ), fL τ * echarPos τ z)
          + (∫ τ in (0 : ℝ)..(1 : ℝ), fR τ * echarPos τ z)) ∧
    -- (ii) C² structure on [-1,0]
    ContinuousOn fL (Set.uIcc (-1 : ℝ) 0) ∧
    (∀ x ∈ Set.Ioo (-1 : ℝ) 0, HasDerivWithinAt fL (fL' x) (Set.Ioi x) x) ∧
    ContinuousOn fL' (Set.uIcc (-1 : ℝ) 0) ∧
    (∀ x ∈ Set.Ioo (-1 : ℝ) 0, HasDerivWithinAt fL' (fL'' x) (Set.Ioi x) x) ∧
    IntervalIntegrable fL' volume (-1) 0 ∧ IntervalIntegrable fL'' volume (-1) 0 ∧
    -- (iii) C² structure on [0,1]
    ContinuousOn fR (Set.uIcc (0 : ℝ) 1) ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt fR (fR' x) (Set.Ioi x) x) ∧
    ContinuousOn fR' (Set.uIcc (0 : ℝ) 1) ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt fR' (fR'' x) (Set.Ioi x) x) ∧
    IntervalIntegrable fR' volume 0 1 ∧ IntervalIntegrable fR'' volume 0 1 ∧
    -- (iv) outer endpoints vanish (Ĵ(±1)=0)  and inner endpoints match (Ĵ cont. at 0)
    fL (-1) = 0 ∧ fR 1 = 0 ∧ fL 0 = fR 0 ∧
    -- (v) the second-IBP budgets are ≤ K
    (‖fL' (-1)‖ + ‖fL' 0‖ + ∫ τ in (-1 : ℝ)..(0 : ℝ), ‖fL'' τ‖) ≤ K ∧
    (‖fR' 0‖ + ‖fR' 1‖ + ∫ τ in (0 : ℝ)..(1 : ℝ), ‖fR'' τ‖) ≤ K

/-- **PROVEN — `VaalerJhatPiecewiseC2Data → VaalerJTwoIBPDecay`.**

Run the proven two-IBP closed form `twoIBP_piece` on each piece and sum.  The first-IBP
boundary character terms collapse:

* outer: `fL(-1)=0`, `fR(1)=0`;
* inner: `fL 0·e_0 − … + fR 0·e_0` cancel because `fL 0 = fR 0` (continuity of `Ĵ` at 0).

What survives is purely `w⁻²`:

    vaalerJ z = − w⁻²·(fL' 0·e_0 − fL'(-1)·e_{-1})
                − w⁻²·(fR' 1·e_1 − fR' 0·e_0)
                + w⁻²·(∫_{-1}^0 fL''·e + ∫_0^1 fR''·e),

so by `‖e‖=1`, the triangle inequality and `∫‖f''·e‖ = ∫‖f''‖`,

    ‖vaalerJ z‖ ≤ (‖w‖⁻¹)²·( budget_L + budget_R ) ≤ (‖w‖⁻¹)²·(2K),

and `(‖w‖⁻¹)² = ((2π)²)⁻¹·(z²)⁻¹` (`normW_inv_sq`), giving the `O(z^{-2})` tail with
constant `C₂ = 2·((2π)²)⁻¹·K`. -/
theorem vaalerJTwoIBPDecay_of_data (h : VaalerJhatPiecewiseC2Data) : VaalerJTwoIBPDecay := by
  obtain ⟨fL, fL', fL'', fR, fR', fR'', K, hsplit,
    hLc, hLd, hL'c, hL'd, hL'i, hL''i,
    hRc, hRd, hR'c, hR'd, hR'i, hR''i,
    hfLm1, hfR1, hf0, hKL, hKR⟩ := h
  refine ⟨2 * (((2 * π) ^ 2)⁻¹ * K), ?_⟩
  intro z hz1
  have hz : z ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hz1; norm_num at hz1
  set w := wfreq z with hw
  have hwnorm_pos : 0 < ‖w‖ := norm_pos_iff.mpr (wfreq_ne_zero hz)
  -- the two closed forms
  have hCL := twoIBP_piece (z := z) hz (by norm_num : (-1:ℝ) ≤ 0)
    hLc hLd hL'c hL'd hL'i hL''i
  have hCR := twoIBP_piece (z := z) hz (by norm_num : (0:ℝ) ≤ 1)
    hRc hRd hR'c hR'd hR'i hR''i
  -- assemble vaalerJ z and simplify the w⁻¹ boundary terms (outer = 0, inner cancel)
  have hsum : vaalerJ z =
      w⁻¹ ^ 2 * (- (fL' 0 * echarPos 0 z - fL' (-1) * echarPos (-1) z)
                 - (fR' 1 * echarPos 1 z - fR' 0 * echarPos 0 z))
      + w⁻¹ ^ 2 * ((∫ τ in (-1:ℝ)..0, fL'' τ * echarPos τ z)
                   + ∫ τ in (0:ℝ)..1, fR'' τ * echarPos τ z) := by
    rw [hsplit z, hCL, hCR, ← hw]
    -- outer endpoints vanish; inner endpoints match (fL 0 = fR 0)
    rw [hfLm1, hfR1, hf0]
    ring
  -- norm bound
  rw [hsum]
  have hbL : ‖∫ τ in (-1:ℝ)..0, fL'' τ * echarPos τ z‖ ≤ ∫ τ in (-1:ℝ)..0, ‖fL'' τ‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1:ℝ) ≤ 0)).trans ?_
    apply le_of_eq; refine intervalIntegral.integral_congr ?_
    intro x _; exact norm_mul_echarPos fL'' x z
  have hbR : ‖∫ τ in (0:ℝ)..1, fR'' τ * echarPos τ z‖ ≤ ∫ τ in (0:ℝ)..1, ‖fR'' τ‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)).trans ?_
    apply le_of_eq; refine intervalIntegral.integral_congr ?_
    intro x _; exact norm_mul_echarPos fR'' x z
  -- bound the two w⁻² terms
  have hwsq_nonneg : 0 ≤ (‖w‖⁻¹) ^ 2 := by positivity
  have hterm1 : ‖w⁻¹ ^ 2 * (- (fL' 0 * echarPos 0 z - fL' (-1) * echarPos (-1) z)
                 - (fR' 1 * echarPos 1 z - fR' 0 * echarPos 0 z))‖
      ≤ (‖w‖⁻¹) ^ 2 * ((‖fL' (-1)‖ + ‖fL' 0‖) + (‖fR' 0‖ + ‖fR' 1‖)) := by
    rw [norm_mul, norm_pow, norm_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg]
    apply add_le_add
    · refine (norm_sub_le _ _).trans ?_
      rw [norm_mul_echarPos, norm_mul_echarPos]; rw [add_comm]
    · refine (norm_sub_le _ _).trans ?_
      rw [norm_mul_echarPos, norm_mul_echarPos]; rw [add_comm]
  have hterm2 : ‖w⁻¹ ^ 2 * ((∫ τ in (-1:ℝ)..0, fL'' τ * echarPos τ z)
                   + ∫ τ in (0:ℝ)..1, fR'' τ * echarPos τ z)‖
      ≤ (‖w‖⁻¹) ^ 2 * ((∫ τ in (-1:ℝ)..0, ‖fL'' τ‖) + ∫ τ in (0:ℝ)..1, ‖fR'' τ‖) := by
    rw [norm_mul, norm_pow, norm_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (norm_add_le _ _).trans (add_le_add hbL hbR)
  -- combine
  have hcomb : ‖w⁻¹ ^ 2 * (- (fL' 0 * echarPos 0 z - fL' (-1) * echarPos (-1) z)
                 - (fR' 1 * echarPos 1 z - fR' 0 * echarPos 0 z))
      + w⁻¹ ^ 2 * ((∫ τ in (-1:ℝ)..0, fL'' τ * echarPos τ z)
                   + ∫ τ in (0:ℝ)..1, fR'' τ * echarPos τ z)‖
      ≤ (‖w‖⁻¹) ^ 2 * ((‖fL' (-1)‖ + ‖fL' 0‖ + ∫ τ in (-1:ℝ)..0, ‖fL'' τ‖)
          + (‖fR' 0‖ + ‖fR' 1‖ + ∫ τ in (0:ℝ)..1, ‖fR'' τ‖)) := by
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ (‖w‖⁻¹) ^ 2 * ((‖fL' (-1)‖ + ‖fL' 0‖) + (‖fR' 0‖ + ‖fR' 1‖))
              + (‖w‖⁻¹) ^ 2 * ((∫ τ in (-1:ℝ)..0, ‖fL'' τ‖) + ∫ τ in (0:ℝ)..1, ‖fR'' τ‖) :=
            add_le_add hterm1 hterm2
      _ = (‖w‖⁻¹) ^ 2 * ((‖fL' (-1)‖ + ‖fL' 0‖ + ∫ τ in (-1:ℝ)..0, ‖fL'' τ‖)
          + (‖fR' 0‖ + ‖fR' 1‖ + ∫ τ in (0:ℝ)..1, ‖fR'' τ‖)) := by ring
  refine hcomb.trans ?_
  -- (‖w‖⁻¹)² · (budgetL + budgetR) ≤ (‖w‖⁻¹)² · 2K = C₂·(z²)⁻¹
  have hbudget : (‖fL' (-1)‖ + ‖fL' 0‖ + ∫ τ in (-1:ℝ)..0, ‖fL'' τ‖)
          + (‖fR' 0‖ + ‖fR' 1‖ + ∫ τ in (0:ℝ)..1, ‖fR'' τ‖) ≤ 2 * K :=
    by linarith [hKL, hKR]
  calc (‖w‖⁻¹) ^ 2 * ((‖fL' (-1)‖ + ‖fL' 0‖ + ∫ τ in (-1:ℝ)..0, ‖fL'' τ‖)
          + (‖fR' 0‖ + ‖fR' 1‖ + ∫ τ in (0:ℝ)..1, ‖fR'' τ‖))
      ≤ (‖w‖⁻¹) ^ 2 * (2 * K) :=
        mul_le_mul_of_nonneg_left hbudget hwsq_nonneg
    _ = 2 * (((2 * π) ^ 2)⁻¹ * K) * (z ^ 2)⁻¹ := by
        rw [hw, normW_inv_sq]; ring

/-- **PROVEN — `VaalerJhatPiecewiseC2Data → JIntegrable`.**  Compose
`vaalerJTwoIBPDecay_of_data` with the committed `jIntegrable_of_twoIBP`. -/
theorem jIntegrable_of_data (h : VaalerJhatPiecewiseC2Data) : JIntegrable :=
  jIntegrable_of_twoIBP (vaalerJTwoIBPDecay_of_data h)

#print axioms hasDerivAt_echarPos
#print axioms norm_wfreq
#print axioms oneIBP_piece
#print axioms twoIBP_piece
#print axioms norm_twoIBP_piece_le
#print axioms norm_twoIBP_piece_vanishing_le
#print axioms normW_inv_sq
#print axioms vaalerJTwoIBPDecay_of_data
#print axioms jIntegrable_of_data

end MathExtras.NumberTheory.Analysis.VaalerJ227Decay
