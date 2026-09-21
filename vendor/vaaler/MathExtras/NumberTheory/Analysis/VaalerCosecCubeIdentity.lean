/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerGPoUReprDecay
import MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof
import MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail
import MathExtras.NumberTheory.Analysis.VaalerPoUCancellation
import MathExtras.NumberTheory.Analysis.VaalerGRegularityProof

/-!
# Discharge of `CosecCubeIdentity` — the cube cosecant identity as the termwise
derivative of the PROVEN squared cosecant identity

This NEW leaf discharges the single named residual
`VaalerGPoUReprDecay.CosecCubeIdentity`: for `x ∉ ℤ` (`sin πx ≠ 0`),

    `(∑ (x−(k+1))⁻³) + (∑ (x+(k+1))⁻³) + x⁻³ = cos πx · (π/sin πx)³`.

## Route (FROM THE BOOK — termwise differentiation of the squared identity)

The squared cosecant identity is PROVEN in `VaalerSumInvSqProof`:

    `(∑ (x−(k+1))⁻²) + (∑ (x+(k+1))⁻²) + x⁻² = (π/sin πx)²`   (`vaalerSumInvSqIdentity_holds`).

It holds on the OPEN set `ℝ ∖ ℤ`.  Both sides are differentiable there, so their
derivatives agree at every `x ∉ ℤ`.  The termwise derivatives are already PROVEN:

* `d/dx ∑ (x−(k+1))⁻² = ∑ −2(x−(k+1))⁻³`  — `hasDerivAt_negTailSum` (negative tail);
* `d/dx ∑ (x+(k+1))⁻² = ∑ −2(x+(k+1))⁻³`  — `hasDerivAt_posTail`  (positive tail, `x>0`);
* `d/dx x⁻² = −2 x⁻³`  — `hasDerivAt_invSq_shift 0`;
* `d/dx (π/sin πx)² = −2π³ cos πx / sin³ πx = −2·cos πx·(π/sin πx)³`  (chain/product rule).

Equating the two derivatives and dividing by `−2` gives the cube identity for `x>0`.
The identity is odd under `x ↦ −x` (both sides flip sign: `(x−n)⁻³ ↔ −(x+n)⁻³`,
`sin(−πx) = −sin πx`), so reflection extends it to all `x ∉ ℤ`.

## Hard constraints honoured

NEW leaf only; nothing existing/committed edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.  Build
green; `#print axioms` is `[propext, Classical.choice, Quot.sound]`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2.
-/

noncomputable section

open Real Filter Topology
open scoped BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerCosecCubeIdentity

open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerDerivInterpHProbe
open MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail
open MathExtras.NumberTheory.Analysis.VaalerGPoUReprDecay

/-! ## §0 — `sin πx ≠ 0 ↔ x ∉ range Int.cast`, and a neighbourhood of nonvanishing -/

/-- `sin πx ≠ 0 ⇒ x ∉ ℤ` (the converse of `sin_pi_mul_ne_zero_of_notMem`). -/
theorem notMem_of_sin_ne_zero {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    x ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨n, hn⟩
  apply hs
  rw [← hn, show (π : ℝ) * (n : ℝ) = (n : ℝ) * π by ring, Real.sin_int_mul_pi]

/-! ## §1 — Derivative of the squared cosecant `(π/sin πx)²` -/

/-- The closed-form derivative of `x ↦ (π/sin πx)²` off ℤ:
`d/dx (π/sin πx)² = −2 cos πx · (π/sin πx)³`. -/
theorem hasDerivAt_cosecSq {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    HasDerivAt (fun y : ℝ => (π / Real.sin (π * y)) ^ 2)
      (-2 * Real.cos (π * x) * (π / Real.sin (π * x)) ^ 3) x := by
  -- d/dx sin(πx) = cos(πx)·π
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (π * y)) (Real.cos (π * x) * π) x := by
    have hinner : HasDerivAt (fun y : ℝ => π * y) π x := by
      refine (((hasDerivAt_id x).const_mul π).congr_deriv (by ring)).congr_of_eventuallyEq ?_
      filter_upwards with y
      rfl
    refine ((Real.hasDerivAt_sin (π * x)).comp x hinner).congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl
  -- d/dx (π / sin πx) = π·(−cos πx·π)/sin²πx = −π² cos πx / sin² πx
  have hdiv : HasDerivAt (fun y : ℝ => π / Real.sin (π * y))
      (-(π * (Real.cos (π * x) * π)) / (Real.sin (π * x)) ^ 2) x := by
    refine (((hasDerivAt_const x (π : ℝ)).div hsin hs).congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl
  -- chain through u ↦ u²
  have hsq := hdiv.pow 2
  -- normalise the derivative value
  refine (hsq.congr_deriv ?_).congr_of_eventuallyEq ?_
  · -- goal: 2·(π/sin)·(−π²cos/sin²) = −2·cos·(π/sin)³
    simp only [Nat.cast_ofNat, pow_succ, pow_zero]
    field_simp [hs, Real.pi_ne_zero]
  · filter_upwards with y
    rfl

/-! ## §2 — The cube identity for `x > 0` by differentiating the squared identity -/

/-- The squared-cosecant LHS as a single function of `x` (matching the ordering of
`vaalerSumInvSqIdentity_holds`). -/
private def Lsq (x : ℝ) : ℝ :=
  (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2) + (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2) + x⁻¹ ^ 2

/-- The closed-form derivative of the squared-cosecant LHS off ℤ, for `x > 0`:
the sum of the three termwise derivatives. -/
theorem hasDerivAt_Lsq_pos {x : ℝ} (hxpos : 0 < x)
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    HasDerivAt Lsq
      ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3)
        + (∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) + (-2 * x⁻¹ ^ 3)) x := by
  have hxne : x ≠ 0 := hxpos.ne'
  -- negative tail derivative
  have hneg : HasDerivAt (fun z : ℝ => ∑' k : ℕ, (z - (k + 1 : ℕ))⁻¹ ^ 2)
      (∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3) x := hasDerivAt_negTailSum hx
  -- positive tail derivative
  have hpos : HasDerivAt (fun z : ℝ => ∑' k : ℕ, (z + (k + 1 : ℕ))⁻¹ ^ 2)
      (∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) x := hasDerivAt_posTail hxpos
  -- x⁻² derivative: d/dx (x − 0)⁻² = −2(x − 0)⁻³
  have hinv : HasDerivAt (fun z : ℝ => z⁻¹ ^ 2) (-2 * x⁻¹ ^ 3) x := by
    have h := hasDerivAt_invSq_shift 0 x (by simpa using hxne)
    simpa using h
  have hfun : Lsq = fun z : ℝ =>
      (∑' k : ℕ, (z - (k + 1 : ℕ))⁻¹ ^ 2) + (∑' k : ℕ, (z + (k + 1 : ℕ))⁻¹ ^ 2) + z⁻¹ ^ 2 := by
    funext z; rfl
  rw [hfun]
  exact (hneg.add hpos).add hinv

/-- **The cube cosecant identity for `x > 0`** (`x ∉ ℤ`).  Differentiating the PROVEN
squared identity termwise and equating derivatives, then dividing by `−2`. -/
theorem cosecCube_pos {x : ℝ} (hxpos : 0 < x) (hs : Real.sin (π * x) ≠ 0) :
    (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 3) + (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3) + x⁻¹ ^ 3
      = Real.cos (π * x) * (π / Real.sin (π * x)) ^ 3 := by
  have hx : x ∉ Set.range ((↑) : ℤ → ℝ) := notMem_of_sin_ne_zero hs
  -- LHS derivative
  have hL : HasDerivAt Lsq
      ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3)
        + (∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) + (-2 * x⁻¹ ^ 3)) x :=
    hasDerivAt_Lsq_pos hxpos hx
  -- RHS derivative
  have hR : HasDerivAt (fun y : ℝ => (π / Real.sin (π * y)) ^ 2)
      (-2 * Real.cos (π * x) * (π / Real.sin (π * x)) ^ 3) x := hasDerivAt_cosecSq hs
  -- the squared identity holds on a neighbourhood of x (sin ≠ 0 nearby)
  have hcont : ContinuousAt (fun y : ℝ => Real.sin (π * y)) x := by
    apply Continuous.continuousAt
    exact Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hnhds : ∀ᶠ y : ℝ in nhds x, Real.sin (π * y) ≠ 0 := hcont.eventually_ne hs
  have heq : Lsq =ᶠ[nhds x] fun y : ℝ => (π / Real.sin (π * y)) ^ 2 := by
    filter_upwards [hnhds] with y hy
    exact MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds y hy
  -- transport the LHS derivative across the eventual equality, then uniqueness
  have hL' : HasDerivAt (fun y : ℝ => (π / Real.sin (π * y)) ^ 2)
      ((∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3)
        + (∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3) + (-2 * x⁻¹ ^ 3)) x :=
    hL.congr_of_eventuallyEq heq.symm
  have hderiv := hL'.unique hR
  -- pull out −2 from each tsum on the LHS of hderiv
  have hMt : (∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 3)
      = -2 * ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 3 := by
    rw [← tsum_mul_left]
  have hPt : (∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 3)
      = -2 * ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3 := by
    rw [← tsum_mul_left]
  rw [hMt, hPt] at hderiv
  -- hderiv : −2·M3 + −2·P3 + −2·x⁻³ = −2·cos·(π/sin)³ ; divide by −2
  linarith [hderiv]

/-! ## §3 — Reflection to all `x ∉ ℤ`, and the discharge -/

/-- **The cube cosecant identity for all `x ∉ ℤ`** = `CosecCubeIdentity`.
Positive `x` is `cosecCube_pos`.  For `x < 0` apply it at `−x > 0` and reflect:
both sides are odd, the cube tails swap (`M₃(−x) = −P₃(x)`, `P₃(−x) = −M₃(x)`),
`(−x)⁻³ = −x⁻³`, `sin(−πx) = −sin πx`, `cos(−πx) = cos πx`. -/
theorem cosecCubeIdentity_holds : CosecCubeIdentity := by
  intro x hs
  -- x ≠ 0 since sin πx ≠ 0
  have hxne : x ≠ 0 := by
    intro h; apply hs; rw [h, mul_zero, Real.sin_zero]
  rcases lt_or_gt_of_ne hxne with hxneg | hxpos
  · -- x < 0 : apply at -x > 0 and reflect
    have hnxpos : 0 < -x := by linarith
    have hsn : Real.sin (π * -x) ≠ 0 := by
      rw [show π * -x = -(π * x) by ring, Real.sin_neg]; simpa using hs
    have hcube := cosecCube_pos hnxpos hsn
    -- reflect the four pieces in hcube to express in terms of x
    -- M3(-x) = ∑(-x-(k+1))⁻³ = −∑(x+(k+1))⁻³ = −P3(x)
    have hM : (∑' k : ℕ, (-x - (k + 1 : ℕ))⁻¹ ^ 3)
        = -∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3 := by
      rw [← tsum_neg]
      refine tsum_congr (fun k => ?_)
      rw [show -x - ((k : ℕ) + 1 : ℕ) = -(x + ((k : ℕ) + 1 : ℕ)) by push_cast; ring,
        inv_neg, neg_pow]
      norm_num
    -- P3(-x) = ∑(-x+(k+1))⁻³ = −∑(x-(k+1))⁻³ = −M3(x)
    have hP : (∑' k : ℕ, (-x + (k + 1 : ℕ))⁻¹ ^ 3)
        = -∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 3 := by
      rw [← tsum_neg]
      refine tsum_congr (fun k => ?_)
      rw [show -x + ((k : ℕ) + 1 : ℕ) = -(x - ((k : ℕ) + 1 : ℕ)) by push_cast; ring,
        inv_neg, neg_pow]
      norm_num
    -- (-x)⁻³ = −x⁻³
    have hX : (-x)⁻¹ ^ 3 = -(x⁻¹ ^ 3) := by rw [inv_neg, neg_pow]; norm_num
    -- sin/cos reflection
    have hsinr : Real.sin (π * -x) = -Real.sin (π * x) := by
      rw [show π * -x = -(π * x) by ring, Real.sin_neg]
    have hcosr : Real.cos (π * -x) = Real.cos (π * x) := by
      rw [show π * -x = -(π * x) by ring, Real.cos_neg]
    rw [hM, hP, hX, hsinr, hcosr] at hcube
    -- hcube : −P3 + −M3 + −x⁻³ = cos·(π/(−sin))³ = −cos·(π/sin)³
    have hπsin : (π / -Real.sin (π * x)) ^ 3 = -(π / Real.sin (π * x)) ^ 3 := by
      rw [div_neg, neg_pow]; norm_num
    rw [hπsin] at hcube
    linarith [hcube]
  · exact cosecCube_pos hxpos hs

/-! ## §4 — Downstream: `GPoUReprDecay` (and hence the `G`-decay chain) is now closed -/

/-- With `CosecCubeIdentity` discharged, the full PoU-representation residual
`GPoUReprDecay` is a theorem (via the committed `gPoUReprDecay_of_cosecCube`). -/
theorem gPoUReprDecay_proven :
    MathExtras.NumberTheory.Analysis.VaalerPoUCancellation.GPoUReprDecay :=
  gPoUReprDecay_of_cosecCube cosecCubeIdentity_holds

/-- **Capstone — `GLargeArgDecay` is now unconditional** (via the committed
`gLargeArgDecay_of_PoUReprDecay`). -/
theorem gLargeArgDecay_proven :
    MathExtras.NumberTheory.Analysis.VaalerDecayBounds.GLargeArgDecay :=
  MathExtras.NumberTheory.Analysis.VaalerPoUCancellation.gLargeArgDecay_of_PoUReprDecay
    gPoUReprDecay_proven

/-- **Capstone — `GDecayBound` is now unconditional** (via the committed
`gDecayBound_of_PoUReprDecay`). -/
theorem gDecayBound_proven :
    MathExtras.NumberTheory.Analysis.VaalerGRegularity.GDecayBound :=
  MathExtras.NumberTheory.Analysis.VaalerPoUCancellation.gDecayBound_of_PoUReprDecay
    gPoUReprDecay_proven

/-- **Capstone — `GIntegrable` is now unconditional**: combine the just-proven
`GDecayBound` with the committed `gContinuous_proven`. -/
theorem gIntegrable_proven :
    MathExtras.NumberTheory.Analysis.VaalerGCFourierMatch.GIntegrable :=
  MathExtras.NumberTheory.Analysis.VaalerGRegularity.gIntegrable_of_continuous_of_decay
    MathExtras.NumberTheory.Analysis.VaalerGRegularityProof.gContinuous_proven
    gDecayBound_proven

#print axioms hasDerivAt_cosecSq
#print axioms cosecCube_pos
#print axioms cosecCubeIdentity_holds
#print axioms gPoUReprDecay_proven
#print axioms gLargeArgDecay_proven
#print axioms gDecayBound_proven
#print axioms gIntegrable_proven

end MathExtras.NumberTheory.Analysis.VaalerCosecCubeIdentity

end
