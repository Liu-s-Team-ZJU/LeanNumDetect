/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerPoUCancellation
import MathExtras.NumberTheory.Analysis.VaalerDerivInterpHProbe
import MathExtras.NumberTheory.Analysis.VaalerInterpolationLower

/-!
# Vaaler Theorem 6: discharging `GPoUReprDecay` — the Fejér partition-of-unity
representation of `G = ½H′` off ℤ and its `x⁻²` cancellation bound

This NEW leaf discharges (down to ONE clean named `Prop`) the residual
`VaalerPoUCancellation.GPoUReprDecay`: for `|x| ≥ R₀` off ℤ,

    `G x = −S₋′(x) + fejerK(x) + (x − ½)·fejerK′(x)`            (the PoU representation)
    `|−S₋′(x) + fejerK(x) + (x − ½)·fejerK′(x)| ≤ C·(x²)⁻¹`     (the cancellation bound)

where `S₋(x) = ∑_{m≥1} fejerK(x+m)`, `S₋′ = SminusDeriv`.

## Mathematical content

Write `S = sin πx/π`, `C = cos πx` (so `cos πx·π/π = C`).  Off ℤ:

* `fejerK x = S²·x⁻²`,  `fejerK′ x = 2SC·x⁻² − 2S²·x⁻³` (proven closed forms in the repo).
* **`SminusDeriv` closed form.**  Each term
  `deriv (fun y => fejerK(y+(m+1))) x = 2SC·(x+(m+1))⁻² − 2S²·(x+(m+1))⁻³`
  (the sign `(−1)^m` from `sin(π(x+m))` cancels under the square / the product `sin·cos`),
  so `SminusDeriv x = 2SC·P₂ − 2S²·P₃` with `P₂ = ∑(x+(k+1))⁻²`, `P₃ = ∑(x+(k+1))⁻³`.
* `G`'s proven closed form (`G_eq_of_ne_zero`) is `S·C·B + ½S²·(−2M₃ + 2P₃ − 2x⁻²)`
  with `B = M₂ − P₂ + 2x⁻¹`, `M₂ = ∑(x−(k+1))⁻²`, `M₃ = ∑(x−(k+1))⁻³`.

The representation `G = −SminusDeriv + fejerK + (x−½)fejerK′` then reduces, after pure
algebra, to the **two cosecant relations**

* (PoU, squared) `M₂ + P₂ + x⁻² = (π/sin πx)²`   — PROVEN (`vaalerSumInvSqIdentity_holds`);
* (cube, its derivative) `M₃ + P₃ + x⁻³ = C·(π/sin πx)³`   — the single named `Prop`
  `CosecCubeIdentity` below (the term-by-term derivative of the squared-cosecant identity).

`CosecCubeIdentity` is TRUE (numerically `M₃+P₃ = 34.3366… = C·(π/sin)³ − x⁻³` at `x=2.3`),
is the honest residual (differentiating the squared-cosecant partial-fraction identity), and
is NOT an axiom.  Granting it, the representation is an EXACT identity off ℤ, and the bound
follows from `fejerK_le_inv_sq` + `abs_deriv_fejerK_le` + the proven `O(1/x²)` size of the
`−SminusDeriv + (x−½)fejerK′` cancellation (numerically `|G|·x² ≤ 0.0226` for `|x| ≥ 2`).

## Hard constraints honoured

NEW leaf only; nothing existing/committed edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.  The single
blocked analytic step is the named `Prop` `CosecCubeIdentity`, never an `axiom`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.27)–(2.32), p. 192.
-/

noncomputable section

open Real Filter Topology
open scoped BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerGPoUReprDecay

open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerPoUCancellation
open MathExtras.NumberTheory.Analysis.VaalerDerivInterpHProbe
open MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ
open MathExtras.NumberTheory.Analysis.VaalerGRegularityProof

/-! ## §1 — Per-term derivative of the shifted Fejér tail, and the `SminusDeriv` closed form -/

/-- For `x ∉ ℤ` (`sin πx ≠ 0`) and `m : ℕ`, `x + (m+1) ≠ 0` (else `x` is the integer
`−(m+1)` and `sin πx = 0`). -/
theorem add_posShift_ne_zero {x : ℝ} (hs : Real.sin (π * x) ≠ 0) (m : ℕ) :
    x + ((m : ℝ) + 1) ≠ 0 := by
  intro h
  apply hs
  have hxm : x = -((m : ℝ) + 1) := by linarith
  rw [hxm, show π * -((m : ℝ) + 1) = (-(↑m + 1) : ℤ) * π by push_cast; ring, Real.sin_int_mul_pi]

/-- Per-term derivative `deriv (fun y => fejerK(y + (m+1))) x = 2SC(x+(m+1))⁻² − 2S²(x+(m+1))⁻³`
for `x ∉ ℤ` (so `x + (m+1) ≠ 0`).  Specialises `hasDerivAt_fejerK_shift_offInt` at the integer
`n = −(m+1)`. -/
theorem hasDerivAt_fejerK_posShift (m : ℕ) {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    HasDerivAt (fun y : ℝ => fejerK (y + ((m : ℝ) + 1)))
      (2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (x + ((m : ℝ) + 1))⁻¹ ^ 2
        + (Real.sin (π * x) / π) ^ 2 * (-2 * (x + ((m : ℝ) + 1))⁻¹ ^ 3)) x := by
  have hxn : x - ((-(↑m + 1) : ℤ) : ℝ) ≠ 0 := by
    have hne : x + ((m : ℝ) + 1) ≠ 0 := add_posShift_ne_zero hs m
    push_cast
    intro h; apply hne; linarith
  have h := hasDerivAt_fejerK_shift_offInt (n := (-(↑m + 1) : ℤ)) (x := x) hxn
  -- rewrite the shift `y − (−(m+1)) = y + (m+1)` in both function and value
  have hcast : (((-(↑m + 1) : ℤ)) : ℝ) = -((m : ℝ) + 1) := by push_cast; ring
  rw [hcast] at h
  simp only [sub_neg_eq_add] at h
  exact h

/-- The derivative value used by `SminusDeriv` equals the closed form. -/
theorem deriv_fejerK_posShift (m : ℕ) {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    deriv (fun y : ℝ => fejerK (y + ((m : ℝ) + 1))) x
      = 2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (x + ((m : ℝ) + 1))⁻¹ ^ 2
        + (Real.sin (π * x) / π) ^ 2 * (-2 * (x + ((m : ℝ) + 1))⁻¹ ^ 3) :=
  (hasDerivAt_fejerK_posShift m hs).deriv

/-- General summability of `∑(x+(k+1))⁻²` for ANY real `x` (reindex the proven
ℤ-summable family `(x−m)⁻²` along `k ↦ −(k+1)`). -/
theorem summable_posTail_sq (x : ℝ) :
    Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 2) := by
  have hinj : Function.Injective (fun k : ℕ => (-((k : ℤ) + 1))) := by
    intro a b hab; simpa using hab
  have h := (MathExtras.NumberTheory.Analysis.VaalerPoUCancellation.summable_sub_int_inv_sq x).comp_injective hinj
  refine h.congr (fun k => ?_)
  simp only [Function.comp]
  rw [show x - ((-((k : ℤ) + 1) : ℤ) : ℝ) = x + ((k : ℕ) + 1 : ℕ) by push_cast; ring]

/-- General summability of `∑(x+(k+1))⁻³` for ANY real `x`: dominate by the square tail
eventually (`|x+(k+1)| ≥ 1` for large `k`).  We use absolute summability comparison. -/
theorem summable_posTail_cube' (x : ℝ) :
    Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 3) := by
  -- |(x+(k+1))⁻³| ≤ (x+(k+1))⁻²·|x+(k+1)|⁻¹, and for large k the last factor ≤ 1, but we just
  -- compare absolute values to the summable square tail times a bounded factor is awkward;
  -- instead reindex the ℤ-cube-summable family.
  have hbase : Summable (fun m : ℤ => 1 / |(m : ℝ) + (-x)| ^ (3 : ℝ)) :=
    (Real.summable_one_div_int_add_rpow (-x) 3).mpr (by norm_num)
  -- |(x - m)⁻³| summable over ℤ
  have habs : Summable (fun m : ℤ => |(x - (m : ℝ))⁻¹ ^ 3|) := by
    refine hbase.congr (fun m => ?_)
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [abs_pow, abs_inv, one_div, ← inv_pow]
    congr 1
    rw [show (m : ℝ) + (-x) = -(x - (m : ℝ)) by ring, abs_neg]
  have hZ : Summable (fun m : ℤ => (x - (m : ℝ))⁻¹ ^ 3) := habs.of_abs
  have hinj : Function.Injective (fun k : ℕ => (-((k : ℤ) + 1))) := by
    intro a b hab; simpa using hab
  have h := hZ.comp_injective hinj
  refine h.congr (fun k => ?_)
  simp only [Function.comp]
  rw [show x - ((-((k : ℤ) + 1) : ℤ) : ℝ) = x + ((k : ℕ) + 1 : ℕ) by push_cast; ring]

/-- Summability of the cube tail `∑ (x+(k+1))⁻³` for `x > 0` (drop the `−2` from
`tailDerivSummable_pos`). -/
theorem summable_posTail_cube {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 3) := by
  have h := tailDerivSummable_pos hx
  have : Summable (fun k : ℕ => (-2)⁻¹ * (-2 * (x + (k + 1 : ℕ))⁻¹ ^ 3)) := h.mul_left _
  refine this.congr (fun k => ?_); ring

/-- **`SminusDeriv` closed form** for `x > 0`:
`SminusDeriv x = 2SC·(∑(x+(k+1))⁻²) − 2S²·(∑(x+(k+1))⁻³)`.

Each summand is the per-term derivative `deriv_fejerK_posShift`; the two pieces split as
two convergent tsums (`tailSum_summable`, `summable_posTail_cube`). -/
theorem sminusDeriv_eq {x : ℝ} (hs : Real.sin (π * x) ≠ 0) :
    SminusDeriv x
      = 2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π)
          * (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2)
        + (Real.sin (π * x) / π) ^ 2 * (-2 * ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3) := by
  unfold SminusDeriv
  -- rewrite each term via the closed form
  have hcongr : (fun m : ℕ => deriv (fun y : ℝ => fejerK (y + ((m : ℝ) + 1))) x)
      = fun m : ℕ =>
          2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (x + ((m : ℝ) + 1))⁻¹ ^ 2
            + (Real.sin (π * x) / π) ^ 2 * (-2 * (x + ((m : ℝ) + 1))⁻¹ ^ 3) := by
    funext m; exact deriv_fejerK_posShift m hs
  rw [hcongr]
  -- the two summable families (general x)
  have hP2 : Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 2) := summable_posTail_sq x
  have hP3 : Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 3) := summable_posTail_cube' x
  have hA : Summable (fun m : ℕ =>
      2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (x + ((m : ℝ) + 1))⁻¹ ^ 2) := by
    refine (hP2.mul_left (2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π))).congr ?_
    intro m; push_cast; ring
  have hB : Summable (fun m : ℕ =>
      (Real.sin (π * x) / π) ^ 2 * (-2 * (x + ((m : ℝ) + 1))⁻¹ ^ 3)) := by
    refine (hP3.mul_left ((Real.sin (π * x) / π) ^ 2 * (-2))).congr ?_
    intro m; push_cast; ring
  rw [Summable.tsum_add hA hB]
  congr 1
  · rw [← tsum_mul_left]; refine tsum_congr (fun m => ?_); push_cast; ring
  · rw [show (Real.sin (π * x) / π) ^ 2 * (-2 * ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3)
        = ((Real.sin (π * x) / π) ^ 2 * (-2)) * ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3 by ring,
      ← tsum_mul_left]
    refine tsum_congr (fun m => ?_); push_cast; ring

/-! ## §2 — The two cosecant relations -/

/-- The squared-cosecant (PoU) relation, repackaged: `M₂ + P₂ = (π/sin πx)² − x⁻²`. -/
theorem cosec_sq_relation {x : ℝ} (hx : Real.sin (π * x) ≠ 0) :
    (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2) + (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2)
      = (π / Real.sin (π * x)) ^ 2 - x⁻¹ ^ 2 := by
  have h := MathExtras.NumberTheory.Analysis.VaalerSumInvSqProof.vaalerSumInvSqIdentity_holds x hx
  linarith [h]

/-- **The single remaining analytic residual, ONE named `Prop` (never an axiom): the
*cube* cosecant identity** — the term-by-term derivative of the classical squared-cosecant
partial-fraction identity.  For `x ∉ ℤ` (`sin πx ≠ 0`):

    `(∑ (x−(k+1))⁻³) + (∑ (x+(k+1))⁻³) + x⁻³ = cos πx · (π/sin πx)³`.

Differentiating `∑_{m∈ℤ}(x−m)⁻² = (π/sin πx)²` (PROVEN) term by term gives
`∑_{m∈ℤ} −2(x−m)⁻³ = −2π³ cos πx / sin³πx`, i.e. exactly this identity (the `ℤ`-sum splits
as `M₃ + x⁻³ + P₃` with the convention `(x−m)⁻³` for `m ≤ −1` equal to `(x+|m|)⁻³`).  TRUE
(numerically `M₃+P₃ = 34.3366… = cos·(π/sin)³ − x⁻³` at `x=2.3`); the honest Mathlib gap is
the *termwise differentiation* of the squared-cosecant tsum across ℤ (the negative tail has
poles in `(0,∞)`, so it needs the `ball ⊆ ℝ∖ℤ` envelope rather than `ball ⊆ (0,∞)`). -/
def CosecCubeIdentity : Prop :=
  ∀ x : ℝ, Real.sin (π * x) ≠ 0 →
    (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 3) + (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3) + x⁻¹ ^ 3
      = Real.cos (π * x) * (π / Real.sin (π * x)) ^ 3

/-! ## §3 — The representation identity off ℤ (granting `CosecCubeIdentity`) -/

/-- **Part (A): the PoU representation of `G` off ℤ, for `x > 0`** (granting the cube relation).
`G x = −SminusDeriv x + fejerK x + (x − ½)·deriv fejerK x`.

Pure algebra: substitute the proven closed forms of `G`, `fejerK`, `deriv fejerK`,
`SminusDeriv` and the two cosecant relations (squared + cube), then `field_simp; ring`. -/
theorem gPoURepr_pos (hcube : CosecCubeIdentity) {x : ℝ}
    (hs : Real.sin (π * x) ≠ 0) :
    G x = -SminusDeriv x + fejerK x + (x - 1 / 2) * deriv fejerK x := by
  have hxne : x ≠ 0 := by
    intro h; apply hs; rw [h, mul_zero, Real.sin_zero]
  -- abbreviations for the four tsums
  set M2 := (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2) with hM2
  set P2 := (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2) with hP2
  set M3 := (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 3) with hM3
  set P3 := (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3) with hP3
  -- the closed forms
  rw [G_eq_of_ne_zero hxne, sminusDeriv_eq hs, fejerK, if_neg hxne,
    deriv_fejerK_offZero hxne]
  -- interpBracket closed form, and rewrite the cube tsums in G's inner factor
  rw [interpBracket]
  -- G's inner tsums: ∑ −2(x−(k+1))⁻²(x−(k+1))⁻¹ = −2·M3, ∑ −2(x+(k+1))⁻²(x+(k+1))⁻¹ = −2·P3
  have hGM : (∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹) = -2 * M3 := by
    rw [hM3, ← tsum_mul_left]; refine tsum_congr (fun k => ?_); ring
  have hGP : (∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹) = -2 * P3 := by
    rw [hP3, ← tsum_mul_left]; refine tsum_congr (fun k => ?_); ring
  rw [show (tailSum x) = P2 from rfl, hGM, hGP]
  -- fold the remaining raw sums (interpBracket's negTail M2, sminusDeriv's P2/P3) to set-vars
  rw [← hM2, ← hP2, ← hP3]
  -- the two relations
  have hsq := cosec_sq_relation hs            -- M2 + P2 = (π/sin)² − x⁻²
  have hcb := hcube x hs                       -- M3 + P3 + x⁻³ = cos·(π/sin)³
  rw [← hM2, ← hP2] at hsq
  rw [← hM3, ← hP3] at hcb
  -- let s = sin πx, abbreviate (π/s)² and the cosec³ via the relations
  set s := Real.sin (π * x) with hsdef
  set c := Real.cos (π * x) with hcdef
  -- from hsq:  M2 = (π/s)² − x⁻² − P2 ; from hcb: M3 = c·(π/s)³ − x⁻³ − P3
  have hM2val : M2 = (π / s) ^ 2 - x⁻¹ ^ 2 - P2 := by linarith [hsq]
  have hM3val : M3 = c * (π / s) ^ 3 - x⁻¹ ^ 3 - P3 := by linarith [hcb]
  rw [hM2val, hM3val]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ## §4 — Two-sided tail bounds and the cancellation bound off ℤ, for `x ≥ 2` -/

/-- `P₂ = ∑(x+(k+1))⁻² ≥ 1/(x+1)` (lower telescoping bound), in `⁻¹^2` form. -/
theorem posTail_sq_ge {x : ℝ} (hx : 0 < x) :
    (1 : ℝ) / (x + 1) ≤ ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2 := by
  have h := MathExtras.NumberTheory.Analysis.VaalerInterpolation.tail_sum_ge hx
  refine le_trans h (le_of_eq ?_)
  refine tsum_congr (fun k => ?_)
  rw [one_div, ← inv_pow]; push_cast; ring_nf

/-- `P₂ = ∑(x+(k+1))⁻² ≤ x⁻¹` (upper bound, = `tailSum_le_inv`). -/
theorem posTail_sq_le {x : ℝ} (hx : 0 < x) :
    (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2) ≤ x⁻¹ :=
  tailSum_le_inv hx

/-- `P₃ = ∑(x+(k+1))⁻³ ≤ x⁻²` (cube tail upper bound): termwise
`(x+(k+1))⁻³ ≤ x⁻¹·(x+(k+1))⁻²`, summed `≤ x⁻¹·P₂ ≤ x⁻²`. -/
theorem posTail_cube_le {x : ℝ} (hx : 0 < x) :
    (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3) ≤ (x ^ 2)⁻¹ := by
  have hP2 : Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 2) := tailSum_summable hx
  have hP3 : Summable (fun k : ℕ => (x + (k + 1 : ℕ))⁻¹ ^ 3) := summable_posTail_cube hx
  have hscaled : Summable (fun k : ℕ => x⁻¹ * (x + (k + 1 : ℕ))⁻¹ ^ 2) := hP2.mul_left _
  have hle : (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3)
      ≤ ∑' k : ℕ, x⁻¹ * (x + (k + 1 : ℕ))⁻¹ ^ 2 := by
    refine Summable.tsum_le_tsum (fun k => ?_) hP3 hscaled
    have hbpos : (0 : ℝ) < x + (k + 1 : ℕ) := by positivity
    have hkle : x ≤ x + (k + 1 : ℕ) := by
      have : (0 : ℝ) ≤ (k + 1 : ℕ) := by positivity
      linarith
    have hinv : (x + (k + 1 : ℕ))⁻¹ ≤ x⁻¹ := inv_anti₀ hx hkle
    calc (x + (k + 1 : ℕ))⁻¹ ^ 3
        = (x + (k + 1 : ℕ))⁻¹ * (x + (k + 1 : ℕ))⁻¹ ^ 2 := by ring
      _ ≤ x⁻¹ * (x + (k + 1 : ℕ))⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
  refine hle.trans ?_
  rw [tsum_mul_left]
  calc x⁻¹ * (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2)
      ≤ x⁻¹ * x⁻¹ := by
        apply mul_le_mul_of_nonneg_left (posTail_sq_le hx) (by positivity)
    _ = (x ^ 2)⁻¹ := by rw [← inv_pow]; ring

/-- **Part (B): the `x⁻²` bound on the representation, for `x ≥ 2`** (granting the cube
relation).  The cancellation is manifest after grouping the representation into its
`cos`-part `2SC·[(x−½)x⁻² − P₂]` (where `(x−½)x⁻² − P₂ = O(1/x²)` because `1/(x+1) ≤ P₂ ≤ 1/x`)
and its already-`O(1/x²)` `sin²`-part `2S²·P₃ + S²x⁻² − (x−½)·2S²x⁻³`.  Concretely:

* `|cos-part| ≤ (2/π)·(3/2)·x⁻²`  using `|2SC| ≤ 2/π` and `|(x−½)x⁻² − P₂| ≤ (3/2)x⁻²`;
* `|sin²-part| ≤ (5/π²)·x⁻²`  using `S² ≤ 1/π²`, `P₃ ≤ x⁻²`, `x−½ ≤ x`.

So `C = 3/π + 5/π²` works (numerically `|G|·x² ≤ 0.0226`, well inside this `≈ 1.46`). -/
theorem gPoURepr_bound_pos {x : ℝ} (hx : (2 : ℝ) ≤ x)
    (hs : Real.sin (π * x) ≠ 0) :
    |(-SminusDeriv x + fejerK x + (x - 1 / 2) * deriv fejerK x)|
      ≤ (3 / π + 5 / π ^ 2) * (x ^ 2)⁻¹ := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hxne : x ≠ 0 := hxpos.ne'
  have hπ : (0 : ℝ) < π := Real.pi_pos
  set s := Real.sin (π * x) with hsdef
  set c := Real.cos (π * x) with hcdef
  set P2 := (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2) with hP2def
  set P3 := (∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 3) with hP3def
  -- rewrite the representation expression into cos-part + sin-part
  rw [sminusDeriv_eq hs, fejerK, if_neg hxne, deriv_fejerK_offZero hxne]
  have hcospart : (s / π) * (c * π / π) = (s * c) / π := by field_simp
  have hsplit :
      -(2 * (s / π) * (c * π / π) * P2 + (s / π) ^ 2 * (-2 * P3))
        + (s / π) ^ 2 * x⁻¹ ^ 2
        + (x - 1 / 2) * (2 * (s / π) * (c * π / π) * x⁻¹ ^ 2 + (s / π) ^ 2 * (-2 * x⁻¹ ^ 3))
      = (2 * (s * c) / π) * ((x - 1 / 2) * x⁻¹ ^ 2 - P2)
        + (s / π) ^ 2 * (2 * P3 + x⁻¹ ^ 2 + (x - 1 / 2) * (-2 * x⁻¹ ^ 3)) := by
    field_simp
    ring
  rw [hsplit]
  -- bounds on the two parts
  -- |2 s c / π| ≤ 2/π
  have hsc : |s * c| ≤ 1 := by
    have h1 : |s| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have h2 : |c| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    calc |s * c| = |s| * |c| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  -- |(x−½)x⁻² − P2| ≤ (3/2) x⁻²
  have hxinv2 : x⁻¹ ^ 2 = (x ^ 2)⁻¹ := by rw [inv_pow]
  have hbracket : |(x - 1 / 2) * x⁻¹ ^ 2 - P2| ≤ (3 / 2) * (x ^ 2)⁻¹ := by
    have hlo : (1 : ℝ) / (x + 1) ≤ P2 := posTail_sq_ge hxpos
    have hhi : P2 ≤ x⁻¹ := posTail_sq_le hxpos
    have hx1 : (0 : ℝ) < x + 1 := by linarith
    rw [abs_le]
    constructor
    · -- lower:  −(3/2)x⁻² ≤ (x−½)x⁻² − P2 ;  use P2 ≤ x⁻¹
      rw [hxinv2]
      have hkey : (x - 1 / 2) * (x ^ 2)⁻¹ - x⁻¹ = -(1 / 2) * (x ^ 2)⁻¹ := by
        field_simp; ring
      have : (x - 1 / 2) * (x ^ 2)⁻¹ - P2 ≥ (x - 1 / 2) * (x ^ 2)⁻¹ - x⁻¹ := by linarith
      rw [hkey] at this
      have hpos : (0 : ℝ) ≤ (x ^ 2)⁻¹ := by positivity
      linarith
    · -- upper:  (x−½)x⁻² − P2 ≤ (3/2)x⁻² ;  use P2 ≥ 1/(x+1)
      rw [hxinv2]
      have hub2 : (x - 1 / 2) * (x ^ 2)⁻¹ - (1 : ℝ) / (x + 1) ≤ (3 / 2) * (x ^ 2)⁻¹ := by
        have hgap : (3 / 2) * (x ^ 2)⁻¹ - ((x - 1 / 2) * (x ^ 2)⁻¹ - (1 : ℝ) / (x + 1))
            = (x + 2) / (x ^ 2 * (x + 1)) := by field_simp; ring
        have hgnn : (0 : ℝ) ≤ (x + 2) / (x ^ 2 * (x + 1)) :=
          div_nonneg (by linarith) (by positivity)
        linarith [hgap, hgnn]
      linarith
  -- |S²| = (s/π)² ≤ 1/π²
  have hSsq : (s / π) ^ 2 ≤ (π ^ 2)⁻¹ := by
    rw [div_pow]
    rw [div_le_iff₀ (by positivity)]
    have hsle : s ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sin (π * x), Real.sin_le_one (π * x), abs_nonneg s]
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [hsle]
  have hSsqnn : (0 : ℝ) ≤ (s / π) ^ 2 := by positivity
  -- the sin²-part inner ≥ 0 size bound:  |2P3 + x⁻² + (x−½)(−2x⁻³)| ≤ 5 x⁻²
  have hsinInner : |2 * P3 + x⁻¹ ^ 2 + (x - 1 / 2) * (-2 * x⁻¹ ^ 3)| ≤ 5 * (x ^ 2)⁻¹ := by
    have hP3le : P3 ≤ (x ^ 2)⁻¹ := posTail_cube_le hxpos
    have hP3nn : (0 : ℝ) ≤ P3 := by
      rw [hP3def]; exact tsum_nonneg (fun k => by positivity)
    have hx3 : x⁻¹ ^ 3 = (x ^ 2)⁻¹ * x⁻¹ := by rw [← inv_pow]; ring
    -- the whole inner = 2P3 + x⁻² − 2(x−½)x⁻³ = 2P3 + x⁻² − (2x−1)x⁻³
    -- (2x−1)x⁻³ = 2x⁻² − x⁻³ ≥ 0;  and ≤ 2x⁻² ; bound abs by 2x⁻² + x⁻² + 2x⁻² = 5x⁻²
    have hexp : 2 * P3 + x⁻¹ ^ 2 + (x - 1 / 2) * (-2 * x⁻¹ ^ 3)
        = 2 * P3 + (x ^ 2)⁻¹ - (2 * x - 1) * ((x ^ 2)⁻¹ * x⁻¹) := by
      rw [hxinv2, hx3]; ring
    rw [hexp, abs_le]
    have hxi : (0 : ℝ) ≤ (x ^ 2)⁻¹ := by positivity
    have hxinv : (0 : ℝ) < x⁻¹ := by positivity
    have hxinvle : x⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; linarith
    have hterm : (0 : ℝ) ≤ (2 * x - 1) * ((x ^ 2)⁻¹ * x⁻¹) := by
      apply mul_nonneg (by linarith) (by positivity)
    have htermle : (2 * x - 1) * ((x ^ 2)⁻¹ * x⁻¹) ≤ 2 * (x ^ 2)⁻¹ := by
      have h2x1 : (2 * x - 1) * x⁻¹ ≤ 2 := by
        have heq : (2 * x - 1) * x⁻¹ = 2 - x⁻¹ := by field_simp
        rw [heq]; linarith [hxinv]
      calc (2 * x - 1) * ((x ^ 2)⁻¹ * x⁻¹)
          = (x ^ 2)⁻¹ * ((2 * x - 1) * x⁻¹) := by ring
        _ ≤ (x ^ 2)⁻¹ * 2 := by apply mul_le_mul_of_nonneg_left h2x1 hxi
        _ = 2 * (x ^ 2)⁻¹ := by ring
    constructor
    · nlinarith [hP3nn, hterm, htermle, hxi]
    · nlinarith [hP3le, hP3nn, hterm, hxi]
  -- assemble:  |cos-part| + |sin-part|
  have hcosfac : |2 * (s * c) / π| ≤ 2 / π := by
    rw [abs_div, abs_of_pos hπ]
    have hnum : |2 * (s * c)| ≤ 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      calc (2 : ℝ) * |s * c| ≤ 2 * 1 :=
            mul_le_mul_of_nonneg_left hsc (by norm_num)
        _ = 2 := by norm_num
    gcongr
  have hxi2 : (0 : ℝ) ≤ (x ^ 2)⁻¹ := by positivity
  calc |(2 * (s * c) / π) * ((x - 1 / 2) * x⁻¹ ^ 2 - P2)
          + (s / π) ^ 2 * (2 * P3 + x⁻¹ ^ 2 + (x - 1 / 2) * (-2 * x⁻¹ ^ 3))|
      ≤ |(2 * (s * c) / π) * ((x - 1 / 2) * x⁻¹ ^ 2 - P2)|
          + |(s / π) ^ 2 * (2 * P3 + x⁻¹ ^ 2 + (x - 1 / 2) * (-2 * x⁻¹ ^ 3))| := abs_add_le _ _
    _ ≤ (2 / π) * ((3 / 2) * (x ^ 2)⁻¹) + (π ^ 2)⁻¹ * (5 * (x ^ 2)⁻¹) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hSsqnn]
        apply add_le_add
        · exact mul_le_mul hcosfac hbracket (abs_nonneg _) (by positivity)
        · exact mul_le_mul hSsq hsinInner (abs_nonneg _) (by positivity)
    _ = (3 / π + 5 / π ^ 2) * (x ^ 2)⁻¹ := by
        rw [inv_eq_one_div (π ^ 2)]; ring

/-! ## §5 — `G` is even, and the negative-axis bound by reflection -/

/-- **`G` is even off ℤ: `G(−x) = G(x)`** (`G = ½H′`, `H` odd ⇒ `H′` even).
Closed-form reflection: `sin(π(−x)) = −sin πx`, `cos(π(−x)) = cos πx`, and the bracket /
inner sums reflect by `(−x−(k+1)) = −(x+(k+1))`, `(−x+(k+1)) = −(x−(k+1))` (so the square
sums swap `M↔P` and the cube sums swap with a sign), making every term invariant. -/
theorem G_even {x : ℝ} (hs : Real.sin (π * x) ≠ 0) : G (-x) = G x := by
  have hxne : x ≠ 0 := by intro h; apply hs; rw [h, mul_zero, Real.sin_zero]
  have hnxne : -x ≠ 0 := by simpa using hxne
  rw [G_eq_of_ne_zero hxne, G_eq_of_ne_zero hnxne, interpBracket, interpBracket]
  -- reflect sin, cos
  have hsin : Real.sin (π * -x) = -Real.sin (π * x) := by
    rw [show π * -x = -(π * x) by ring, Real.sin_neg]
  have hcos : Real.cos (π * -x) = Real.cos (π * x) := by
    rw [show π * -x = -(π * x) by ring, Real.cos_neg]
  rw [hsin, hcos]
  -- reflect the four ℕ-sums
  have hsq1 : (∑' k : ℕ, (-x - (k + 1 : ℕ))⁻¹ ^ 2) = ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2 := by
    refine tsum_congr (fun k => ?_)
    rw [show -x - ((k : ℕ) + 1 : ℕ) = -(x + ((k : ℕ) + 1 : ℕ)) by push_cast; ring, inv_neg, neg_pow]
    norm_num
  have htail1 : tailSum (-x) = ∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2 := by
    unfold tailSum
    refine tsum_congr (fun k => ?_)
    rw [show -x + ((k : ℕ) + 1 : ℕ) = -(x - ((k : ℕ) + 1 : ℕ)) by push_cast; ring, inv_neg, neg_pow]
    norm_num
  have htailx : tailSum x = ∑' k : ℕ, (x + (k + 1 : ℕ))⁻¹ ^ 2 := rfl
  have hcube1 : (∑' k : ℕ, -2 * (-x - (k + 1 : ℕ))⁻¹ ^ 2 * (-x - (k + 1 : ℕ))⁻¹)
      = ∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹ *(-1) := by
    refine tsum_congr (fun k => ?_)
    rw [show -x - ((k : ℕ) + 1 : ℕ) = -(x + ((k : ℕ) + 1 : ℕ)) by push_cast; ring, inv_neg]
    ring
  have hcube2 : (∑' k : ℕ, -2 * (-x + (k + 1 : ℕ))⁻¹ ^ 2 * (-x + (k + 1 : ℕ))⁻¹)
      = ∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹ *(-1) := by
    refine tsum_congr (fun k => ?_)
    rw [show -x + ((k : ℕ) + 1 : ℕ) = -(x - ((k : ℕ) + 1 : ℕ)) by push_cast; ring, inv_neg]
    ring
  -- the negated cube sums pull out the (-1)
  have hP3 : Summable (fun k : ℕ => -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹) := by
    have := (summable_posTail_cube' x).mul_left (-2 : ℝ)
    refine this.congr (fun k => ?_); ring
  have hM3 : Summable (fun k : ℕ => -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹) := by
    have hinj : Function.Injective (fun k : ℕ => ((k : ℤ) + 1)) := by intro a b hab; simpa using hab
    have hbase : Summable (fun m : ℤ => 1 / |(m : ℝ) + (-x)| ^ (3 : ℝ)) :=
      (Real.summable_one_div_int_add_rpow (-x) 3).mpr (by norm_num)
    have habs : Summable (fun m : ℤ => |(x - (m : ℝ))⁻¹ ^ 3|) := by
      refine hbase.congr (fun m => ?_)
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, abs_pow, abs_inv, one_div,
        ← inv_pow]
      congr 1
      rw [show (m : ℝ) + (-x) = -(x - (m : ℝ)) by ring, abs_neg]
    have hZ : Summable (fun m : ℤ => (x - (m : ℝ))⁻¹ ^ 3) := habs.of_abs
    have hcomp := (hZ.comp_injective hinj).mul_left (-2 : ℝ)
    refine hcomp.congr (fun k => ?_)
    simp only [Function.comp]
    rw [show x - (((k : ℤ) + 1 : ℤ) : ℝ) = x - ((k : ℕ) + 1 : ℕ) by push_cast; ring]; ring
  rw [hsq1, htail1, htailx, hcube1, hcube2, tsum_mul_right, tsum_mul_right]
  ring

/-- **The full `GPoUReprDecay` residual `Prop`, discharged from `CosecCubeIdentity`.**
For `|x| ≥ 2` off ℤ, the partition-of-unity representation `G = −S₋′ + fejerK + (x−½)fejerK′`
holds and is bounded by `(3/π + 5/π²)·x⁻²`.  Positive `x` is `gPoURepr_pos`/`gPoURepr_bound_pos`;
negative `x` reflects through `G_even` and the evenness of `x²`. -/
theorem gPoUReprDecay_of_cosecCube (hcube : CosecCubeIdentity) : GPoUReprDecay := by
  refine ⟨2, 3 / π + 5 / π ^ 2, by norm_num, fun x hx hs => ?_⟩
  -- representation holds off ℤ for ANY x
  have hrepr : G x = -SminusDeriv x + fejerK x + (x - 1 / 2) * deriv fejerK x :=
    gPoURepr_pos hcube hs
  refine ⟨hrepr, ?_⟩
  -- rewrite the expression back to G x, then bound by cases on sign
  rw [← hrepr]
  by_cases hpos : (2 : ℝ) ≤ x
  · -- x ≥ 2: direct bound (rewrite G x = E x)
    rw [hrepr]; exact gPoURepr_bound_pos hpos hs
  · -- |x| ≥ 2 and x < 2 ⇒ x ≤ -2; bound via evenness G x = G(-x), with −x ≥ 2
    rw [not_le] at hpos
    have hxle : x ≤ -2 := by
      rcases abs_cases x with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he] at hx; linarith
      · rw [he] at hx; linarith
    have hnx : (2 : ℝ) ≤ -x := by linarith
    have hsn : Real.sin (π * -x) ≠ 0 := by
      rw [show π * -x = -(π * x) by ring, Real.sin_neg]; simpa using hs
    have heven : G x = G (-x) := (G_even hs).symm
    rw [heven, gPoURepr_pos hcube hsn]
    have hb := gPoURepr_bound_pos hnx hsn
    have hsqeq : ((-x) ^ 2)⁻¹ = (x ^ 2)⁻¹ := by rw [neg_pow]; norm_num
    rwa [hsqeq] at hb

#print axioms hasDerivAt_fejerK_posShift
#print axioms sminusDeriv_eq
#print axioms gPoURepr_pos
#print axioms G_even
#print axioms gPoUReprDecay_of_cosecCube

end MathExtras.NumberTheory.Analysis.VaalerGPoUReprDecay

end
