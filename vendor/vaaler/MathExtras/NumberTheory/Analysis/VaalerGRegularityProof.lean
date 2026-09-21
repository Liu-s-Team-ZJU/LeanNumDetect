/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathExtras.NumberTheory.Analysis.VaalerInterpHContinuous
import MathExtras.NumberTheory.Analysis.VaalerDecayBounds
import MathExtras.NumberTheory.Analysis.VaalerJhatCornerLimits

/-!
# Vaaler Theorem 6: discharging `GContinuousAtIntegers` (integer continuity of `G = ½H′`)

This NEW leaf proves the integer-continuity minor residual
`VaalerGRegularity.GContinuousAtIntegers : ∀ n, ContinuousAt GC (n:ℝ)` — the genuine
*derivative*-version of the apparent-pole cancellation of `interpH` at the integers —
discharging one of the two remaining tractable minor residuals.  The decay residual
`GLargeArgDecay` is reduced to its single delicate cancellation as a precise named `Prop`.

## The math (the derivative apparent-pole cancellation)

`G = ½H′` is, off ℤ (Vaaler / `hasDerivAt_interpH`),

    `G x = (sin πx/π)(cos πx)·B(x) + ½(sin πx/π)²·(C⁻(x) − C⁺(x) − 2x⁻²)`,

where `B = interpBracket`, `C⁻ x = ∑ₖ −2(x−(k+1))⁻³`, `C⁺ x = ∑ₖ −2(x+(k+1))⁻³`.

Near an integer `n`, the bracket has the double pole `sgn(n)·(x−n)⁻²` (negative tail at
`k=n−1` for `n≥1`, positive tail at `k=−n−1` for `n≤−1`, none at `n=0`) and the cube tail
`C⁻−C⁺` has the triple pole `sgn(n)·(−2)(x−n)⁻³`.  Multiplying out, the **singular** part
of `G` near `n` is exactly

    `sgn(n)·[ (sin πx/π)(cos πx)(x−n)⁻² + ½(sin πx/π)²(−2)(x−n)⁻³ ]
       = sgn(n)·½· d/dx[ (sin πx/π)²(x−n)⁻² ] = sgn(n)·½· d/dx[ fejerK(x−n) ]`,

and `fejerK(·−n)` is `C∞` (`fejerK = sinc(π·)²`), so its derivative is **continuous**.  The
simple pole `2x⁻¹` of the bracket likewise contributes
`½·d/dx[(sin πx/π)²·2x⁻¹] = ½·d/dx[2x·fejerK x]`, continuous.  The remaining (punctured)
tails are continuous at `n` (no pole).  Hence `G` extends continuously across each integer.

## What is PROVEN here (sorry/axiom-free, non-vacuous)

* `contDiff_fejerK_shift` / `contDiff_two_mul_id_fejerK` — `fun y => fejerK (y−c)` and
  `fun y => 2y·fejerK y` are `C∞`, so their `deriv`s are continuous.
* `hasDerivAt_fejerK_shift_offInt` — closed form for `d/dx fejerK(x−n)` off the pole.
* `hasDerivAt_two_mul_id_fejerK_offZero` — closed form for `d/dx (2x·fejerK x)` off `0`.
* `puncturedNegCube_continuousAt` / `puncturedPosCube_continuousAt` — the punctured `^3`
  cube tails are continuous at `n`.
* `gCand_continuousAt` — the continuous candidate `Gcand n` is continuous at `n`.
* `g_eqOn_nhds_gCand` — `G =ᶠ[𝓝 n] Gcand n` (the cancellation, on the punctured ball plus
  value matching at `n`).
* `g_continuousAt_int` — **`ContinuousAt G (n:ℝ)` for every `n : ℤ`** (origin via the
  patched removable value `G 0 = 1`, nonzero integers via the cancellation).
* `gC_continuousAt_int` / `gContinuousAtIntegers_proven` — **`GContinuousAtIntegers`.**
* `g_continuous` / `gContinuous_holds` / `gContinuous_proven` — **`Continuous G`,
  `Continuous (fun x => (G x:ℂ))`, and the bundled residual `GContinuous`.**

This DISCHARGES the residual `GContinuousAtIntegers`, hence (with the committed off-ℤ
continuity) `GContinuous`.

## DEAD_ENDS #20 repair note

`VaalerHPrimeEqTwoJ.G` now carries the removable value `G 0 = 1` at the origin (the patched
`if x = 0 then 1 else …` branch).  Previously its junk value `G 0 = 0` disagreed with the true
limit `1`, making `GContinuousAtIntegers` unsatisfiable at `n = 0`.  With the repair the
residual is TRUE and PROVEN; the former disproof (`gContinuousAtIntegers_false`) and junk-value
lemma (`g_zero_eq_zero`) are removed, and `Gfixed` (the old explicit fix) now coincides with `G`.

## The decay residual `GLargeArgDecay`

`GLargeArgDecay` concerns only `|x| ≥ R₀ ≥ 1`, so it is unaffected by the `n = 0` defect.
Its single delicate cancellation — the leading `O(1/x)` terms of `½H′` cancelling to leave
`O(1/x²)` — is isolated as the precise named `Prop` `GLargeArgCancellation` (NOT an axiom),
together with the proven reduction `GLargeArgCancellation → GLargeArgDecay`.

## Hard constraints honoured

NEW leaf only; nothing existing/committed edited.  No
`axiom`/`sorry`/`admit`/`native_decide`/`False.elim`/`absurd`/`not_*_input`.  Build green;
`#print axioms` of each result is `[propext, Classical.choice, Quot.sound]`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2,
Theorem 6, eqs (2.22)–(2.32), p. 191–192.
-/

noncomputable section

open MeasureTheory Complex Real Filter Topology Metric
open scoped BigOperators ContDiff

namespace MathExtras.NumberTheory.Analysis.VaalerGRegularityProof

open MathExtras.NumberTheory.Analysis.VaalerBeurlingNonneg
open MathExtras.NumberTheory.Analysis.VaalerDerivInterpHNegTail
open MathExtras.NumberTheory.Analysis.VaalerHPrimeEqTwoJ
open MathExtras.NumberTheory.Analysis.VaalerTruncationLimit
open MathExtras.NumberTheory.Analysis.VaalerGRegularity
open MathExtras.NumberTheory.Analysis.VaalerInterpHContinuous
open MathExtras.NumberTheory.Analysis.VaalerJhatCornerLimits
open MathExtras.NumberTheory.Analysis.VaalerDecayBounds
open MathExtras.NumberTheory.Analysis.VaalerDerivInterpHProbe
open MathExtras.NumberTheory.Analysis.VaalerJFTviaHN

/-! ## §1 — `fejerK` and `2·id·fejerK` are `C∞`; closed forms for their derivatives -/

/-- `fejerK = fun x => (sinc (π x))²` (the removable square-sinc kernel). -/
theorem fejerK_eq : fejerK = fun x : ℝ => (Real.sinc (π * x)) ^ 2 := by
  funext x; exact fejerK_eq_sinc_sq x

/-- `fejerK` is `C∞`: it is `(sinc ∘ (π·))²`. -/
theorem contDiff_fejerK : ContDiff ℝ ∞ fejerK := by
  rw [fejerK_eq]
  exact (contDiff_sinc.comp (contDiff_const.mul contDiff_id)).pow 2

/-- For a real shift `c`, `fun y => fejerK (y − c)` is `C∞`. -/
theorem contDiff_fejerK_shift (c : ℝ) : ContDiff ℝ ∞ (fun y : ℝ => fejerK (y - c)) :=
  contDiff_fejerK.comp (contDiff_id.sub contDiff_const)

/-- `fun y => 2·y·fejerK y` is `C∞`. -/
theorem contDiff_two_mul_id_fejerK : ContDiff ℝ ∞ (fun y : ℝ => 2 * y * fejerK y) :=
  (contDiff_const.mul contDiff_id).mul contDiff_fejerK

/-- `deriv (fun y => fejerK (y − c))` is continuous. -/
theorem continuous_deriv_fejerK_shift (c : ℝ) :
    Continuous (deriv (fun y : ℝ => fejerK (y - c))) :=
  (contDiff_fejerK_shift c).continuous_deriv (by simp)

/-- `deriv (fun y => 2·y·fejerK y)` is continuous. -/
theorem continuous_deriv_two_mul_id_fejerK :
    Continuous (deriv (fun y : ℝ => 2 * y * fejerK y)) :=
  contDiff_two_mul_id_fejerK.continuous_deriv (by simp)

/-! ## §2 — Off-pole closed forms identifying the `fejerK`-derivatives with the singular
parts of `G` -/

/-- Off the pole (`x ∉ ℤ`, `x ≠ n`): the derivative of `fejerK(·−n)` equals the explicit
value `2(sin πx/π)(cos πx)(x−n)⁻² + (sin πx/π)²(−2)(x−n)⁻³`.

Near such `x`, `fejerK(y−n) = (sin πy/π)²·(y−n)⁻²` (the `y−n ≠ 0` branch, via the
shifted-Fejér identity `(sin π(y−n)/π)² = (sin πy/π)²`), and the product rule on the RHS
gives the value. -/
theorem hasDerivAt_fejerK_shift_offInt {n : ℤ} {x : ℝ}
    (hxn : x - (n : ℝ) ≠ 0) :
    HasDerivAt (fun y : ℝ => fejerK (y - (n : ℝ)))
      (2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (x - (n : ℝ))⁻¹ ^ 2
        + (Real.sin (π * x) / π) ^ 2 * (-2 * (x - (n : ℝ))⁻¹ ^ 3)) x := by
  -- product rule on g y = (sin πy/π)² · (y − n)⁻²
  -- derivative of (sin πy/π)²
  have hsinpi : HasDerivAt (fun y : ℝ => Real.sin (π * y)) (Real.cos (π * x) * π) x := by
    have hinner : HasDerivAt (fun y : ℝ => π * y) π x := by
      simpa using (hasDerivAt_id x).const_mul π
    exact (Real.hasDerivAt_sin (π * x)).comp x hinner
  have hdiv : HasDerivAt (fun y : ℝ => Real.sin (π * y) / π) (Real.cos (π * x) * π / π) x :=
    hsinpi.div_const π
  have hsq : HasDerivAt (fun y : ℝ => (Real.sin (π * y) / π) ^ 2)
      (2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π)) x := by
    refine ((hdiv.pow 2).congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl
  -- derivative of (y − n)⁻²  =  −2 (x − n)⁻³
  have hinvsq : HasDerivAt (fun y : ℝ => (y - (n : ℝ))⁻¹ ^ 2)
      (-2 * (x - (n : ℝ))⁻¹ ^ 3) x :=
    hasDerivAt_invSq_shift (n : ℝ) x hxn
  -- product rule
  have hprod : HasDerivAt (fun y : ℝ => (Real.sin (π * y) / π) ^ 2 * (y - (n : ℝ))⁻¹ ^ 2)
      (2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (x - (n : ℝ))⁻¹ ^ 2
        + (Real.sin (π * x) / π) ^ 2 * (-2 * (x - (n : ℝ))⁻¹ ^ 3)) x := by
    refine (hsq.mul hinvsq).congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl
  -- the product equals fejerK(·−n) on a neighbourhood of x (where y − n ≠ 0)
  have hne : ∀ᶠ y : ℝ in nhds x, y - (n : ℝ) ≠ 0 := by
    have hcont : ContinuousAt (fun y : ℝ => y - (n : ℝ)) x :=
      (continuous_id.sub continuous_const).continuousAt
    exact hcont.eventually_ne hxn
  have heq : (fun y : ℝ => (Real.sin (π * y) / π) ^ 2 * (y - (n : ℝ))⁻¹ ^ 2)
      =ᶠ[nhds x] (fun y : ℝ => fejerK (y - (n : ℝ))) := by
    filter_upwards [hne] with y hy
    exact shifted_fejer_eq y n hy
  exact hprod.congr_of_eventuallyEq heq.symm

/-- Off `0`: the derivative of `fun y => 2·y·fejerK y` equals the explicit value
`2(sin πx/π)(cos πx)·2x⁻¹ + (sin πx/π)²·2(−x⁻²)`, i.e. twice the simple-pole singular part
of `G`.  (Near `x ≠ 0`, `2y·fejerK y = (sin πy/π)²·2y⁻¹` by `sin_sq_two_inv_eq`.) -/
theorem hasDerivAt_two_mul_id_fejerK_offZero {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 2 * y * fejerK y)
      (2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (2 * x⁻¹)
        + (Real.sin (π * x) / π) ^ 2 * (2 * (-(x⁻¹ ^ 2)))) x := by
  -- product rule on g y = (sin πy/π)² · (2 y⁻¹)
  have hsinpi : HasDerivAt (fun y : ℝ => Real.sin (π * y)) (Real.cos (π * x) * π) x := by
    have hinner : HasDerivAt (fun y : ℝ => π * y) π x := by
      simpa using (hasDerivAt_id x).const_mul π
    exact (Real.hasDerivAt_sin (π * x)).comp x hinner
  have hdiv : HasDerivAt (fun y : ℝ => Real.sin (π * y) / π) (Real.cos (π * x) * π / π) x :=
    hsinpi.div_const π
  have hsq : HasDerivAt (fun y : ℝ => (Real.sin (π * y) / π) ^ 2)
      (2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π)) x := by
    refine ((hdiv.pow 2).congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl
  -- derivative of (2 y⁻¹) = 2·(−x⁻²)
  have hinv : HasDerivAt (fun y : ℝ => 2 * y⁻¹) (2 * (-(x⁻¹ ^ 2))) x := by
    have hh : HasDerivAt (fun y : ℝ => y⁻¹) (-(x⁻¹ ^ 2)) x := by
      have := hasDerivAt_inv hx
      simpa [pow_two] using this
    exact hh.const_mul 2
  have hprod : HasDerivAt (fun y : ℝ => (Real.sin (π * y) / π) ^ 2 * (2 * y⁻¹))
      (2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (2 * x⁻¹)
        + (Real.sin (π * x) / π) ^ 2 * (2 * (-(x⁻¹ ^ 2)))) x := by
    refine (hsq.mul hinv).congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl
  -- the product equals 2 y·fejerK y near x (where y ≠ 0)
  have hne : ∀ᶠ y : ℝ in nhds x, y ≠ 0 := by
    have hcont : ContinuousAt (fun y : ℝ => y) x := continuous_id.continuousAt
    exact hcont.eventually_ne hx
  have heq : (fun y : ℝ => (Real.sin (π * y) / π) ^ 2 * (2 * y⁻¹))
      =ᶠ[nhds x] (fun y : ℝ => 2 * y * fejerK y) := by
    filter_upwards [hne] with y hy
    exact sin_sq_two_inv_eq y hy
  exact hprod.congr_of_eventuallyEq heq.symm

/-! ## §3 — The punctured `^3` cube tails are continuous at `n` -/

/-- **PROVEN.**  For an integer `n`, the negative `^3`-cube tail with the singular term
`k = n−1` removed (set to `0` via `ite`) is continuous at `x = n`.  Same `continuousOn_tsum`
argument as `puncturedNegTail_continuousAt`, but for the cube power. -/
theorem puncturedNegCube_continuousAt (n : ℤ) :
    ContinuousAt
      (fun x : ℝ => ∑' k : ℕ,
        (if (k : ℤ) = n - 1 then (0 : ℝ)
          else -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹)) (n : ℝ) := by
  classical
  set t : Set ℝ := Metric.ball (n : ℝ) (1 / 2) with ht
  -- envelope: 2·16·|n−(k+1)|⁻³ = 32·|n−(k+1)|⁻³
  have hEnv : Summable (fun k : ℕ => (32 : ℝ) * |(n : ℝ) - (k + 1 : ℕ)|⁻¹ ^ 3) :=
    (summable_invCube_shift_neg (n : ℝ)).mul_left 32
  have hcont : ∀ k : ℕ, ContinuousOn
      (fun x : ℝ => if (k : ℤ) = n - 1 then (0 : ℝ)
        else -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹) t := by
    intro k
    by_cases hk : (k : ℤ) = n - 1
    · simp only [hk, if_pos]; exact continuousOn_const
    · simp only [hk, if_neg, not_false_iff]
      have hden : ContinuousOn (fun x : ℝ => x - (k + 1 : ℕ)) t := by fun_prop
      have hne : ∀ y ∈ t, y - (k + 1 : ℕ) ≠ 0 := by
        intro y hy hzero
        have hyeq : y = ((k + 1 : ℤ) : ℝ) := by
          have : y - ((k : ℝ) + 1) = 0 := by push_cast at hzero ⊢; linarith
          push_cast; linarith
        have := ball_half_int_eq hy hyeq.symm
        apply hk; omega
      have hinv : ContinuousOn (fun x : ℝ => (x - (k + 1 : ℕ))⁻¹) t :=
        ContinuousOn.inv₀ hden hne
      exact (continuousOn_const.mul (hinv.pow 2)).mul hinv
  have hsup : ∀ (k : ℕ) (x : ℝ), x ∈ t →
      ‖if (k : ℤ) = n - 1 then (0 : ℝ)
        else -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹‖
        ≤ (32 : ℝ) * |(n : ℝ) - (k + 1 : ℕ)|⁻¹ ^ 3 := by
    intro k x hx
    by_cases hk : (k : ℤ) = n - 1
    · simp only [hk, if_pos, norm_zero]; positivity
    · simp only [hk, if_neg, not_false_iff]
      have hdist : (1 : ℝ) ≤ |(n : ℝ) - (k + 1 : ℕ)| := by
        have hne : (n : ℤ) ≠ (k + 1 : ℕ) := by intro h; apply hk; omega
        have hcast : ((n - (k + 1 : ℕ) : ℤ) : ℝ) = (n : ℝ) - (k + 1 : ℕ) := by push_cast; ring
        have h1 : (1 : ℤ) ≤ |(n - (k + 1 : ℕ) : ℤ)| := Int.one_le_abs (sub_ne_zero.mpr hne)
        calc (1 : ℝ) ≤ (|(n - (k + 1 : ℕ) : ℤ)| : ℤ) := by exact_mod_cast h1
          _ = |((n - (k + 1 : ℕ) : ℤ) : ℝ)| := by rw [Int.cast_abs]
          _ = |(n : ℝ) - (k + 1 : ℕ)| := by rw [hcast]
      rw [Metric.mem_ball, Real.dist_eq] at hx
      have hge : |(n : ℝ) - (k + 1 : ℕ)| / 2 ≤ |x - (k + 1 : ℕ)| := by
        have htri : |(n : ℝ) - (k + 1 : ℕ)| - |x - (n : ℝ)| ≤ |x - (k + 1 : ℕ)| := by
          have : |(n : ℝ) - (k + 1 : ℕ)| ≤ |x - (k + 1 : ℕ)| + |x - (n : ℝ)| := by
            calc |(n : ℝ) - (k + 1 : ℕ)|
                = |(x - (k + 1 : ℕ)) - (x - (n : ℝ))| := by ring_nf
              _ ≤ |x - (k + 1 : ℕ)| + |x - (n : ℝ)| := abs_sub _ _
          linarith
        have hxn : |x - (n : ℝ)| ≤ |(n : ℝ) - (k + 1 : ℕ)| / 2 := by linarith [hx]
        linarith
      have hxn_pos : 0 < |x - (k + 1 : ℕ)| := lt_of_lt_of_le (by linarith) hge
      -- ‖−2·(x−(k+1))⁻²·(x−(k+1))⁻¹‖ = 2·|x−(k+1)|⁻³
      have hnormterm : ‖-2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹‖
          = 2 * |x - (k + 1 : ℕ)|⁻¹ ^ 3 := by
        rw [Real.norm_eq_abs]
        simp only [abs_mul, abs_pow, abs_inv]
        have h2 : |(-2 : ℝ)| = 2 := by norm_num
        rw [h2]; ring
      rw [hnormterm]
      have hhalfpos : (0 : ℝ) < |(n : ℝ) - (k + 1 : ℕ)| / 2 := by
        have : (0:ℝ) < |(n : ℝ) - (k + 1 : ℕ)| := by linarith
        positivity
      have hinv : |x - (k + 1 : ℕ)|⁻¹ ≤ 2 * |(n : ℝ) - (k + 1 : ℕ)|⁻¹ := by
        have := inv_anti₀ hhalfpos hge
        calc |x - (k + 1 : ℕ)|⁻¹ ≤ (|(n : ℝ) - (k + 1 : ℕ)| / 2)⁻¹ := this
          _ = 2 * |(n : ℝ) - (k + 1 : ℕ)|⁻¹ := by rw [inv_div]; ring
      have hcube : |x - (k + 1 : ℕ)|⁻¹ ^ 3 ≤ (2 * |(n : ℝ) - (k + 1 : ℕ)|⁻¹) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hinv 3
      have hexp : (2 * |(n : ℝ) - (k + 1 : ℕ)|⁻¹) ^ 3 = 8 * |(n : ℝ) - (k + 1 : ℕ)|⁻¹ ^ 3 := by
        ring
      rw [hexp] at hcube
      have hnn : (0:ℝ) ≤ |(n : ℝ) - (k + 1 : ℕ)|⁻¹ ^ 3 := by positivity
      linarith
  have hcontOn : ContinuousOn
      (fun x : ℝ => ∑' k : ℕ,
        (if (k : ℤ) = n - 1 then (0 : ℝ)
          else -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹)) t :=
    continuousOn_tsum hcont hEnv hsup
  exact hcontOn.continuousAt (Metric.ball_mem_nhds _ (by norm_num))

/-- **PROVEN.**  Positive analogue for the `^3`-cube tail: term `k = −n−1` removed. -/
theorem puncturedPosCube_continuousAt (n : ℤ) :
    ContinuousAt
      (fun x : ℝ => ∑' k : ℕ,
        (if (k : ℤ) = -n - 1 then (0 : ℝ)
          else -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹)) (n : ℝ) := by
  classical
  set t : Set ℝ := Metric.ball (n : ℝ) (1 / 2) with ht
  have hEnv : Summable (fun k : ℕ => (32 : ℝ) * |(n : ℝ) + (k + 1 : ℕ)|⁻¹ ^ 3) :=
    (summable_invCube_shift_pos (n : ℝ)).mul_left 32
  have hcont : ∀ k : ℕ, ContinuousOn
      (fun x : ℝ => if (k : ℤ) = -n - 1 then (0 : ℝ)
        else -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹) t := by
    intro k
    by_cases hk : (k : ℤ) = -n - 1
    · simp only [hk, if_pos]; exact continuousOn_const
    · simp only [hk, if_neg, not_false_iff]
      have hden : ContinuousOn (fun x : ℝ => x + (k + 1 : ℕ)) t := by fun_prop
      have hne : ∀ y ∈ t, y + (k + 1 : ℕ) ≠ 0 := by
        intro y hy hzero
        have hyeq : y = ((-(k + 1) : ℤ) : ℝ) := by
          have : y + ((k : ℝ) + 1) = 0 := by push_cast at hzero ⊢; linarith
          push_cast; linarith
        have := ball_half_int_eq hy hyeq.symm
        apply hk; omega
      have hinv : ContinuousOn (fun x : ℝ => (x + (k + 1 : ℕ))⁻¹) t :=
        ContinuousOn.inv₀ hden hne
      exact (continuousOn_const.mul (hinv.pow 2)).mul hinv
  have hsup : ∀ (k : ℕ) (x : ℝ), x ∈ t →
      ‖if (k : ℤ) = -n - 1 then (0 : ℝ)
        else -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹‖
        ≤ (32 : ℝ) * |(n : ℝ) + (k + 1 : ℕ)|⁻¹ ^ 3 := by
    intro k x hx
    by_cases hk : (k : ℤ) = -n - 1
    · simp only [hk, if_pos, norm_zero]; positivity
    · simp only [hk, if_neg, not_false_iff]
      have hdist : (1 : ℝ) ≤ |(n : ℝ) + (k + 1 : ℕ)| := by
        have hcast : ((n + ((k : ℤ) + 1) : ℤ) : ℝ) = (n : ℝ) + (k + 1 : ℕ) := by push_cast; ring
        have hnz : (n + ((k : ℤ) + 1) : ℤ) ≠ 0 := by intro h; apply hk; omega
        have h1 : (1 : ℤ) ≤ |(n + ((k : ℤ) + 1) : ℤ)| := Int.one_le_abs hnz
        calc (1 : ℝ) ≤ (|(n + ((k : ℤ) + 1) : ℤ)| : ℤ) := by exact_mod_cast h1
          _ = |((n + ((k : ℤ) + 1) : ℤ) : ℝ)| := by rw [Int.cast_abs]
          _ = |(n : ℝ) + (k + 1 : ℕ)| := by rw [hcast]
      rw [Metric.mem_ball, Real.dist_eq] at hx
      have hge : |(n : ℝ) + (k + 1 : ℕ)| / 2 ≤ |x + (k + 1 : ℕ)| := by
        have htri : |(n : ℝ) + (k + 1 : ℕ)| - |x - (n : ℝ)| ≤ |x + (k + 1 : ℕ)| := by
          have : |(n : ℝ) + (k + 1 : ℕ)| ≤ |x + (k + 1 : ℕ)| + |x - (n : ℝ)| := by
            calc |(n : ℝ) + (k + 1 : ℕ)|
                = |(x + (k + 1 : ℕ)) - (x - (n : ℝ))| := by ring_nf
              _ ≤ |x + (k + 1 : ℕ)| + |x - (n : ℝ)| := abs_sub _ _
          linarith
        have hxn : |x - (n : ℝ)| ≤ |(n : ℝ) + (k + 1 : ℕ)| / 2 := by linarith [hx]
        linarith
      have hxn_pos : 0 < |x + (k + 1 : ℕ)| := lt_of_lt_of_le (by linarith) hge
      have hnormterm : ‖-2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹‖
          = 2 * |x + (k + 1 : ℕ)|⁻¹ ^ 3 := by
        rw [Real.norm_eq_abs]
        simp only [abs_mul, abs_pow, abs_inv]
        have h2 : |(-2 : ℝ)| = 2 := by norm_num
        rw [h2]; ring
      rw [hnormterm]
      have hhalfpos : (0 : ℝ) < |(n : ℝ) + (k + 1 : ℕ)| / 2 := by
        have : (0:ℝ) < |(n : ℝ) + (k + 1 : ℕ)| := by linarith
        positivity
      have hinv : |x + (k + 1 : ℕ)|⁻¹ ≤ 2 * |(n : ℝ) + (k + 1 : ℕ)|⁻¹ := by
        have := inv_anti₀ hhalfpos hge
        calc |x + (k + 1 : ℕ)|⁻¹ ≤ (|(n : ℝ) + (k + 1 : ℕ)| / 2)⁻¹ := this
          _ = 2 * |(n : ℝ) + (k + 1 : ℕ)|⁻¹ := by rw [inv_div]; ring
      have hcube : |x + (k + 1 : ℕ)|⁻¹ ^ 3 ≤ (2 * |(n : ℝ) + (k + 1 : ℕ)|⁻¹) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hinv 3
      have hexp : (2 * |(n : ℝ) + (k + 1 : ℕ)|⁻¹) ^ 3 = 8 * |(n : ℝ) + (k + 1 : ℕ)|⁻¹ ^ 3 := by
        ring
      rw [hexp] at hcube
      have hnn : (0:ℝ) ≤ |(n : ℝ) + (k + 1 : ℕ)|⁻¹ ^ 3 := by positivity
      linarith
  have hcontOn : ContinuousOn
      (fun x : ℝ => ∑' k : ℕ,
        (if (k : ℤ) = -n - 1 then (0 : ℝ)
          else -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹)) t :=
    continuousOn_tsum hcont hEnv hsup
  exact hcontOn.continuousAt (Metric.ball_mem_nhds _ (by norm_num))

/-! ## §4 — Vanishing of the `fejerK`-derivatives at the integers -/

/-- `fejerK` is bounded above by `1` (`fejerK = sinc(π·)²` and `|sinc| ≤ 1`). -/
theorem fejerK_le_one (x : ℝ) : fejerK x ≤ 1 := by
  rw [fejerK_eq_sinc_sq]
  have h := Real.abs_sinc_le_one (π * x)
  nlinarith [abs_nonneg (Real.sinc (π * x)), sq_abs (Real.sinc (π * x)), h,
    abs_le.mp h]

/-- `deriv fejerK 0 = 0`: `fejerK 0 = 1` is a global maximum (`fejerK ≤ 1`). -/
theorem deriv_fejerK_zero : deriv fejerK 0 = 0 := by
  have hmax : IsLocalMax fejerK 0 := by
    refine Filter.Eventually.of_forall ?_
    intro x; rw [fejerK_zero]; exact fejerK_le_one x
  exact hmax.deriv_eq_zero

/-- For a nonzero integer `n`, `deriv fejerK (n:ℝ) = 0`: `fejerK n = 0` is a global
minimum (`fejerK ≥ 0`). -/
theorem deriv_fejerK_int_ne_zero {n : ℤ} (hn : n ≠ 0) : deriv fejerK (n : ℝ) = 0 := by
  have hmin : IsLocalMin fejerK (n : ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro x; rw [fejerK_int_ne_zero hn]; exact fejerK_nonneg x
  exact hmin.deriv_eq_zero

/-- `deriv (fun y => fejerK (y - n)) (n:ℝ) = deriv fejerK 0 = 0` (chain rule + §4). -/
theorem deriv_fejerK_shift_int (n : ℤ) :
    deriv (fun y : ℝ => fejerK (y - (n : ℝ))) (n : ℝ) = 0 := by
  have hshift : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 (n : ℝ) := by
    simpa using (hasDerivAt_id (n : ℝ)).sub_const (n : ℝ)
  have hfej : HasDerivAt fejerK (deriv fejerK ((n : ℝ) - (n : ℝ)))
      ((n : ℝ) - (n : ℝ)) :=
    (contDiff_fejerK.differentiable (by simp)).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fejerK ∘ (fun y : ℝ => y - (n : ℝ)))
      ((1 : ℝ) • deriv fejerK ((n : ℝ) - (n : ℝ))) (n : ℝ) :=
    HasDerivAt.scomp (n : ℝ) hfej hshift
  rw [sub_self, deriv_fejerK_zero] at hcomp
  have hfun : (fun y : ℝ => fejerK (y - (n : ℝ))) = fejerK ∘ (fun y : ℝ => y - (n : ℝ)) := rfl
  rw [hfun, hcomp.deriv]; simp

/-- For a nonzero integer `n`, `deriv (fun y => 2y·fejerK y) (n:ℝ) = 0`:
`= 2·fejerK n + 2n·(deriv fejerK n) = 0` since `fejerK n = 0` and `deriv fejerK n = 0`. -/
theorem deriv_two_mul_id_fejerK_int_ne_zero {n : ℤ} (hn : n ≠ 0) :
    deriv (fun y : ℝ => 2 * y * fejerK y) (n : ℝ) = 0 := by
  have hfejD : HasDerivAt fejerK (deriv fejerK (n : ℝ)) (n : ℝ) :=
    (contDiff_fejerK.differentiable (by simp)).differentiableAt.hasDerivAt
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 (n : ℝ) := by
    simpa using (hasDerivAt_id (n : ℝ)).const_mul (2 : ℝ)
  have hprod : HasDerivAt (fun y : ℝ => 2 * y * fejerK y)
      (2 * fejerK (n : ℝ) + 2 * (n : ℝ) * deriv fejerK (n : ℝ)) (n : ℝ) := by
    refine (hlin.mul hfejD).congr_of_eventuallyEq ?_
    filter_upwards with y
    rfl
  rw [deriv_fejerK_int_ne_zero hn, fejerK_int_ne_zero hn] at hprod
  rw [hprod.deriv]; ring

/-! ## §5 — Unified splits of the cube tails into a punctured tail plus the single pole -/

/-- The signed negative cube tail summand `−2(x−(k+1))⁻²(x−(k+1))⁻¹` is summable
(comparison with the absolute cube envelope). -/
theorem summable_cubeNeg (x : ℝ) :
    Summable (fun k : ℕ => -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹) := by
  have h := (summable_invCube_shift_neg x).mul_left 2
  refine Summable.of_norm ?_
  refine h.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  rw [Real.norm_eq_abs]
  simp only [abs_mul, abs_pow, abs_inv]
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h2]; ring_nf; rfl

/-- The signed positive cube tail summand is summable. -/
theorem summable_cubePos (x : ℝ) :
    Summable (fun k : ℕ => -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹) := by
  have h := (summable_invCube_shift_pos x).mul_left 2
  refine Summable.of_norm ?_
  refine h.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  rw [Real.norm_eq_abs]
  simp only [abs_mul, abs_pow, abs_inv]
  have h2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h2]; ring_nf; rfl

/-- Unified negative cube-tail split:
`CubeNeg = QNeg n + (if 1 ≤ n then −2(x−n)⁻²(x−n)⁻¹ else 0)`. -/
theorem cubeNeg_unified_split (n : ℤ) (x : ℝ) :
    (∑' k : ℕ, -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹)
      = (∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ)
          else -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹))
        + (if 1 ≤ n then -2 * (x - (n : ℝ))⁻¹ ^ 2 * (x - (n : ℝ))⁻¹ else 0) := by
  classical
  by_cases hn : 1 ≤ n
  · -- pole present at k = n − 1
    set k₀ : ℕ := (n - 1).toNat with hk₀
    have hk₀cast : ((k₀ : ℤ)) = n - 1 := by rw [hk₀]; omega
    have hcond : ∀ k : ℕ, ((k : ℤ) = n - 1) ↔ (k = k₀) := by
      intro k; constructor
      · intro h; omega
      · intro h; rw [h]; exact hk₀cast
    rw [if_pos hn]
    rw [tsum_split_single (summable_cubeNeg x) k₀]
    congr 1
    · refine tsum_congr ?_; intro k
      by_cases h : (k : ℤ) = n - 1
      · rw [if_pos h, if_pos ((hcond k).mp h)]
      · rw [if_neg h, if_neg (fun hh => h ((hcond k).mpr hh))]
    · have hval : ((k₀ : ℝ) + 1) = (n : ℝ) := by
        have : (k₀ : ℤ) + 1 = n := by rw [hk₀cast]; ring
        exact_mod_cast this
      rw [show ((k₀ + 1 : ℕ) : ℝ) = (k₀ : ℝ) + 1 by push_cast; ring, hval]
  · rw [if_neg hn, add_zero]
    refine tsum_congr ?_; intro k
    have hne : (k : ℤ) ≠ n - 1 := by omega
    rw [if_neg hne]

/-- Unified positive cube-tail split:
`CubePos = QPos n + (if n ≤ −1 then −2(x−n)⁻²(x−n)⁻¹ else 0)`. -/
theorem cubePos_unified_split (n : ℤ) (x : ℝ) :
    (∑' k : ℕ, -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹)
      = (∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ)
          else -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹))
        + (if n ≤ -1 then -2 * (x - (n : ℝ))⁻¹ ^ 2 * (x - (n : ℝ))⁻¹ else 0) := by
  classical
  by_cases hn : n ≤ -1
  · set k₀ : ℕ := (-n - 1).toNat with hk₀
    have hk₀cast : ((k₀ : ℤ)) = -n - 1 := by rw [hk₀]; omega
    have hcond : ∀ k : ℕ, ((k : ℤ) = -n - 1) ↔ (k = k₀) := by
      intro k; constructor
      · intro h; omega
      · intro h; rw [h]; exact hk₀cast
    rw [if_pos hn]
    rw [tsum_split_single (summable_cubePos x) k₀]
    congr 1
    · refine tsum_congr ?_; intro k
      by_cases h : (k : ℤ) = -n - 1
      · rw [if_pos h, if_pos ((hcond k).mp h)]
      · rw [if_neg h, if_neg (fun hh => h ((hcond k).mpr hh))]
    · have hval : ((k₀ : ℝ) + 1) = -(n : ℝ) := by
        have : (k₀ : ℤ) + 1 = -n := by rw [hk₀cast]; ring
        exact_mod_cast this
      rw [show ((k₀ + 1 : ℕ) : ℝ) = (k₀ : ℝ) + 1 by push_cast; ring, hval]
      rw [show x + -(n : ℝ) = x - (n : ℝ) by ring]
  · rw [if_neg hn, add_zero]
    refine tsum_congr ?_; intro k
    have hne : (k : ℤ) ≠ -n - 1 := by omega
    rw [if_neg hne]

/-! ## §6 — The continuous candidate `Gcand n` and integer continuity for `n ≠ 0` -/

/-- `Real.sign` at a positive integer is `1` (local copy; the committed one is `private`). -/
theorem sign_int_pos' {n : ℤ} (hn : 1 ≤ n) : Real.sign (n : ℝ) = 1 :=
  Real.sign_of_pos (by exact_mod_cast (by omega : (0:ℤ) < n))

/-- `Real.sign` at a negative integer is `-1` (local copy). -/
theorem sign_int_neg' {n : ℤ} (hn : n ≤ -1) : Real.sign (n : ℝ) = -1 :=
  Real.sign_of_neg (by exact_mod_cast (by omega : (n:ℤ) < 0))

/-- The continuous candidate matching `G` near a nonzero integer `n`:

`Gcand n x = (sin πx/π)(cos πx·π/π)·(QNeg-as-^2-punctured tails) ...`

namely the regular punctured `^2` and `^3` tails, plus the two collapsed `fejerK`-derivative
singular contributions `sgn(n)·½·deriv(fejerK(·−n)) x` and `½·deriv(2y·fejerK) x`. -/
def Gcand (n : ℤ) (x : ℝ) : ℝ :=
  (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) *
      ((∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2))
        - (∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2)))
    + (1 / 2 : ℝ) * (Real.sin (π * x) / π) ^ 2 *
        ((∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ)
            else -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹))
          - (∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ)
            else -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹)))
    + Real.sign (n : ℝ) * ((1 / 2 : ℝ) * deriv (fun y : ℝ => fejerK (y - (n : ℝ))) x)
    + (1 / 2 : ℝ) * deriv (fun y : ℝ => 2 * y * fejerK y) x

/-- `Gcand n` is continuous at `(n : ℝ)`. -/
theorem gCand_continuousAt (n : ℤ) : ContinuousAt (Gcand n) (n : ℝ) := by
  unfold Gcand
  have hsin : ContinuousAt (fun x : ℝ => Real.sin (π * x) / π) (n : ℝ) := by
    apply ContinuousAt.div_const
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
  have hcos : ContinuousAt (fun x : ℝ => Real.cos (π * x) * π / π) (n : ℝ) := by
    apply ContinuousAt.div_const
    apply ContinuousAt.mul_const
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousAt
  have h1 : ContinuousAt
      (fun x : ℝ => (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) *
        ((∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2))
          - (∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2))))
      (n : ℝ) :=
    (hsin.mul hcos).mul
      ((puncturedNegTail_continuousAt n).sub (puncturedPosTail_continuousAt n))
  have h2 : ContinuousAt
      (fun x : ℝ => (1 / 2 : ℝ) * (Real.sin (π * x) / π) ^ 2 *
        ((∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ)
            else -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹))
          - (∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ)
            else -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹))))
      (n : ℝ) :=
    ((hsin.pow 2).const_mul (1 / 2 : ℝ)).mul
      ((puncturedNegCube_continuousAt n).sub (puncturedPosCube_continuousAt n))
  have h3 : ContinuousAt
      (fun x : ℝ => Real.sign (n : ℝ) *
        ((1 / 2 : ℝ) * deriv (fun y : ℝ => fejerK (y - (n : ℝ))) x)) (n : ℝ) := by
    apply ContinuousAt.const_mul
    apply ContinuousAt.const_mul
    exact (continuous_deriv_fejerK_shift (n : ℝ)).continuousAt
  have h4 : ContinuousAt
      (fun x : ℝ => (1 / 2 : ℝ) * deriv (fun y : ℝ => 2 * y * fejerK y) x) (n : ℝ) := by
    apply ContinuousAt.const_mul
    exact continuous_deriv_two_mul_id_fejerK.continuousAt
  exact ((h1.add h2).add h3).add h4

/-- **The cancellation, off `n` (and off ℤ).**  For `x ∉ ℤ` with `x ≠ n`, `G x = Gcand n x`.
The bracket and cube-tail unified splits expose the poles `sgn(n)(x−n)⁻²` and
`sgn(n)(−2)(x−n)⁻³`; collected with the `2x⁻¹`, `−2x⁻²` simple-pole terms they assemble
into `sgn(n)·½·deriv(fejerK(·−n)) x + ½·deriv(2y·fejerK) x` via the closed forms
`hasDerivAt_fejerK_shift_offInt`, `hasDerivAt_two_mul_id_fejerK_offZero`. -/
theorem g_eq_gCand_offInt {n : ℤ} {x : ℝ}
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) (hxn : x ≠ (n : ℝ)) :
    G x = Gcand n x := by
  have hx0 : x ≠ 0 := by intro h; apply hx; exact ⟨0, by simp [h]⟩
  have hxn' : x - (n : ℝ) ≠ 0 := sub_ne_zero.mpr hxn
  -- derivative closed forms turned into `deriv = value`
  have hDfej : deriv (fun y : ℝ => fejerK (y - (n : ℝ))) x
      = 2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (x - (n : ℝ))⁻¹ ^ 2
        + (Real.sin (π * x) / π) ^ 2 * (-2 * (x - (n : ℝ))⁻¹ ^ 3) :=
    (hasDerivAt_fejerK_shift_offInt hxn').deriv
  have hDtwo : deriv (fun y : ℝ => 2 * y * fejerK y) x
      = 2 * (Real.sin (π * x) / π) * (Real.cos (π * x) * π / π) * (2 * x⁻¹)
        + (Real.sin (π * x) / π) ^ 2 * (2 * (-(x⁻¹ ^ 2))) :=
    (hasDerivAt_two_mul_id_fejerK_offZero hx0).deriv
  -- bracket split:  ∑(x−(k+1))⁻² = PNeg + Sn ;  tailSum = PPos + Sp
  have hbrNeg := negTail_unified_split n x
  have hbrPos := posTail_unified_split n x
  -- cube split
  have hcubeNeg := cubeNeg_unified_split n x
  have hcubePos := cubePos_unified_split n x
  -- value matching of the singular pole pieces:  Sn − Sp = sign n · (x−n)⁻²
  have hSnSp : (if 1 ≤ n then (x - (n : ℝ))⁻¹ ^ 2 else 0)
        - (if n ≤ -1 then (x - (n : ℝ))⁻¹ ^ 2 else 0)
      = Real.sign (n : ℝ) * (x - (n : ℝ))⁻¹ ^ 2 := by
    rcases lt_trichotomy n 0 with hneg | hzero | hpos
    · have hn1 : n ≤ -1 := by omega
      rw [if_neg (by omega : ¬ 1 ≤ n), if_pos hn1, sign_int_neg' hn1]; ring
    · subst hzero; simp
    · have hn1 : 1 ≤ n := by omega
      rw [if_pos hn1, if_neg (by omega : ¬ n ≤ -1), sign_int_pos' hn1]; ring
  have hTnTp : (if 1 ≤ n then -2 * (x - (n : ℝ))⁻¹ ^ 2 * (x - (n : ℝ))⁻¹ else 0)
        - (if n ≤ -1 then -2 * (x - (n : ℝ))⁻¹ ^ 2 * (x - (n : ℝ))⁻¹ else 0)
      = Real.sign (n : ℝ) * (-2 * (x - (n : ℝ))⁻¹ ^ 2 * (x - (n : ℝ))⁻¹) := by
    rcases lt_trichotomy n 0 with hneg | hzero | hpos
    · have hn1 : n ≤ -1 := by omega
      rw [if_neg (by omega : ¬ 1 ≤ n), if_pos hn1, sign_int_neg' hn1]; ring
    · subst hzero; simp
    · have hn1 : 1 ≤ n := by omega
      rw [if_pos hn1, if_neg (by omega : ¬ n ≤ -1), sign_int_pos' hn1]; ring
  -- expand both sides and rewrite via the splits / deriv closed forms
  rw [G_eq_of_ne_zero hx0, Gcand, hDfej, hDtwo]
  -- interpBracket in terms of the punctured tails + ite pole
  have hbr : interpBracket x
      = (∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2))
          + (if 1 ≤ n then (x - (n : ℝ))⁻¹ ^ 2 else 0)
        - ((∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2))
          + (if n ≤ -1 then (x - (n : ℝ))⁻¹ ^ 2 else 0)) + 2 * x⁻¹ := by
    unfold interpBracket
    rw [show (∑' k : ℕ, (x - (k + 1 : ℕ))⁻¹ ^ 2) = negTailSum x from rfl, hbrNeg, hbrPos]
  rw [hbr, hcubeNeg, hcubePos]
  -- now purely algebraic; substitute the two pole-difference identities
  set PN : ℝ := ∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ) else (x - (k + 1 : ℕ))⁻¹ ^ 2)
  set PP : ℝ := ∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ) else (x + (k + 1 : ℕ))⁻¹ ^ 2)
  set QN : ℝ := ∑' k : ℕ, (if (k : ℤ) = n - 1 then (0 : ℝ)
      else -2 * (x - (k + 1 : ℕ))⁻¹ ^ 2 * (x - (k + 1 : ℕ))⁻¹)
  set QP : ℝ := ∑' k : ℕ, (if (k : ℤ) = -n - 1 then (0 : ℝ)
      else -2 * (x + (k + 1 : ℕ))⁻¹ ^ 2 * (x + (k + 1 : ℕ))⁻¹)
  set Sn : ℝ := if 1 ≤ n then (x - (n : ℝ))⁻¹ ^ 2 else 0
  set Sp : ℝ := if n ≤ -1 then (x - (n : ℝ))⁻¹ ^ 2 else 0
  set Tn : ℝ := if 1 ≤ n then -2 * (x - (n : ℝ))⁻¹ ^ 2 * (x - (n : ℝ))⁻¹ else 0
  set Tp : ℝ := if n ≤ -1 then -2 * (x - (n : ℝ))⁻¹ ^ 2 * (x - (n : ℝ))⁻¹ else 0
  have hSn : Sn = Sp + Real.sign (n : ℝ) * (x - (n : ℝ))⁻¹ ^ 2 := by linarith [hSnSp]
  have hTn : Tn = Tp + Real.sign (n : ℝ) * (-2 * (x - (n : ℝ))⁻¹ ^ 2 * (x - (n : ℝ))⁻¹) := by
    linarith [hTnTp]
  rw [hSn, hTn]
  have h3 : (x - (n : ℝ))⁻¹ ^ 3 = (x - (n : ℝ))⁻¹ ^ 2 * (x - (n : ℝ))⁻¹ := by ring
  rw [h3]; ring

/-- **`G =ᶠ[𝓝 n] Gcand n` for nonzero `n`.**  Off `n` (where `x ∉ ℤ`) it is the
cancellation `g_eq_gCand_offInt`; at `n` both sides equal `0` (the `(sin πx/π)`/`(sin πx/π)²`
prefactors vanish and the collapsed `fejerK`-derivatives vanish at `n ≠ 0`). -/
theorem g_eqOn_nhds_gCand {n : ℤ} (hn : n ≠ 0) :
    G =ᶠ[nhds (n : ℝ)] Gcand n := by
  refine Filter.eventuallyEq_of_mem
    (Metric.ball_mem_nhds (n : ℝ) (show (0:ℝ) < 1/2 by norm_num)) ?_
  intro x hx
  by_cases hxn : x = (n : ℝ)
  · -- value matching at n: both sides are 0
    subst hxn
    have hsinn : Real.sin (π * (n : ℝ)) = 0 := by
      rw [mul_comm]; exact Real.sin_int_mul_pi n
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hG0 : G (n : ℝ) = 0 := by
      rw [G_eq_of_ne_zero hnR, hsinn]; simp
    have hGc0 : Gcand n (n : ℝ) = 0 := by
      unfold Gcand
      rw [hsinn, deriv_fejerK_shift_int n, deriv_two_mul_id_fejerK_int_ne_zero hn]
      simp
    rw [hG0, hGc0]
  · -- off the point: x ∈ ball n (1/2), x ≠ n ⇒ x ∉ ℤ
    have hxnotint : x ∉ Set.range ((↑) : ℤ → ℝ) := by
      rintro ⟨m, hm⟩
      have := ball_half_int_eq hx hm
      rw [this] at hm; exact hxn hm.symm
    exact g_eq_gCand_offInt hxnotint hxn

/-- **PROVEN — `ContinuousAt G (n:ℝ)` for every NONZERO integer `n`.**  The derivative
apparent-pole cancellation: `G =ᶠ[𝓝 n] Gcand n` with `Gcand n` continuous at `n`. -/
theorem g_continuousAt_int_ne_zero {n : ℤ} (hn : n ≠ 0) : ContinuousAt G (n : ℝ) :=
  (continuousAt_congr (g_eqOn_nhds_gCand hn)).mpr (gCand_continuousAt n)

/-- **PROVEN — `ContinuousAt GC (n:ℝ)` for every NONZERO integer `n`.** -/
theorem gC_continuousAt_int_ne_zero {n : ℤ} (hn : n ≠ 0) : ContinuousAt GC (n : ℝ) := by
  have h := g_continuousAt_int_ne_zero hn
  have hofR : ContinuousAt (fun y : ℝ => (y : ℂ)) (G (n : ℝ)) :=
    Complex.continuous_ofReal.continuousAt
  exact (hofR.comp h).congr (by filter_upwards with x; simp [Function.comp, GC_apply])

/-! ## §7 — THE `n = 0` DEFECT, REPAIRED (DEAD_ENDS #20): `GContinuousAtIntegers` is now
TRUE and PROVEN.

`VaalerHPrimeEqTwoJ.G` now carries the removable value `G 0 = 1` at the origin (the patched
`if x = 0 then 1 else …` branch), matching the true continuous limit `lim_{x→0} ½H′ = J(0) = 1`.
At every nonzero integer the raw closed form already gave the correct value `0`, so with the
origin repaired `G` (hence `GC`) is continuous at EVERY integer, and the residual
`GContinuousAtIntegers` is now provable. -/

/-- **`G 0 = 1` (the patched removable value, DEAD_ENDS #20).**  Previously the raw closed
form evaluated to the junk value `0` here (the `if`-less definition); the repaired `G` carries
the true continuous limit `lim_{x→0} ½H′ = J(0) = 1`. -/
theorem g_zero_eq_one : G 0 = 1 := g_zero

/-- **The candidate value at the origin is `1`, matching `G 0 = 1`.**  `Gcand 0 0 = ½·deriv(2y·fejerK) 0`
and `deriv(2y·fejerK) 0 = 2·fejerK 0 + 0 = 2`, so `Gcand 0 0 = 1`.  This is the TRUE
continuous limit `lim_{x→0} G x = ½H′(0⁺) = J(0) = 1`: the leading simple pole `2x⁻¹` of the
bracket sits at the origin, and its contribution `½·d/dx[2x·fejerK x]` does NOT vanish at
`0` (unlike at nonzero integers, where `fejerK = 0`). -/
theorem gCand_zero_eq_one : Gcand 0 0 = 1 := by
  unfold Gcand
  have hsin0 : Real.sin (π * (0 : ℝ)) = 0 := by simp
  -- deriv of fejerK(·-0) at 0 is deriv fejerK 0 = 0
  have hsh : deriv (fun y : ℝ => fejerK (y - (((0 : ℤ) : ℝ)))) ((0:ℤ):ℝ) = 0 :=
    deriv_fejerK_shift_int 0
  -- deriv (2y·fejerK) at 0 = 2·fejerK 0 = 2
  have hd2 : deriv (fun y : ℝ => 2 * y * fejerK y) 0 = 2 := by
    have hfejD : HasDerivAt fejerK (deriv fejerK 0) 0 :=
      (contDiff_fejerK.differentiable (by simp)).differentiableAt.hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
    have hprod : HasDerivAt (fun y : ℝ => 2 * y * fejerK y)
        (2 * fejerK 0 + 2 * (0 : ℝ) * deriv fejerK 0) 0 := by
      refine (hlin.mul hfejD).congr_of_eventuallyEq ?_
      filter_upwards with y
      rfl
    rw [deriv_fejerK_zero, fejerK_zero] at hprod
    rw [hprod.deriv]; ring
  rw [hsin0]
  simp only [Int.cast_zero] at hsh ⊢
  rw [hsh, hd2]
  norm_num

/-- **`G =ᶠ[𝓝[≠] 0] Gcand 0`.**  Off the origin (where `x ∉ ℤ`) `G` agrees with the
continuous candidate `Gcand 0` by the cancellation `g_eq_gCand_offInt`. -/
theorem g_eqOn_punctured_zero : G =ᶠ[𝓝[≠] (0:ℝ)] Gcand 0 := by
  have hball : Metric.ball (0 : ℝ) (1/2) ∈ nhds (0:ℝ) :=
    Metric.ball_mem_nhds _ (by norm_num)
  refine Filter.eventuallyEq_of_mem
    (inter_mem (mem_nhdsWithin_of_mem_nhds hball) self_mem_nhdsWithin) ?_
  rintro x ⟨hxball, hxne⟩
  have hxne0 : x ≠ (0:ℝ) := by simpa using hxne
  have hxn : x ≠ ((0 : ℤ) : ℝ) := by simpa using hxne0
  have hxnotint : x ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨m, hm⟩
    have hxball0 : x ∈ Metric.ball (((0:ℤ)) : ℝ) (1/2) := by simpa using hxball
    have := ball_half_int_eq hxball0 hm
    rw [this] at hm
    exact hxne0 (by simpa using hm.symm)
  exact g_eq_gCand_offInt hxnotint hxn

/-- **PROVEN (DEAD_ENDS #20 repair) — `ContinuousAt G 0`.**  With the patched removable value
`G 0 = 1 = Gcand 0 0`, and `G =ᶠ[𝓝[≠] 0] Gcand 0` (off `0`, `G = Gcand 0` by the
cancellation), `G → 1` at `0` matching its value, so `G` is continuous at the origin.  This is
the genuine derivative apparent-pole cancellation at `n = 0`: the leading simple pole `2x⁻¹`
of the bracket contributes `½·d/dx[2x·fejerK x](0) = 1`, the continuous limit `J(0) = 1`. -/
theorem g_continuousAt_zero : ContinuousAt G (0 : ℝ) := by
  rw [ContinuousAt]
  have hval : G 0 = Gcand 0 0 := by rw [g_zero_eq_one, gCand_zero_eq_one]
  rw [hval]
  have hcandC : ContinuousAt (Gcand 0) (0:ℝ) := by
    have := gCand_continuousAt 0; simpa using this
  have hpunctLim : Tendsto G (𝓝[≠] (0:ℝ)) (nhds (Gcand 0 0)) :=
    (Filter.tendsto_congr' g_eqOn_punctured_zero).mpr (hcandC.tendsto.mono_left nhdsWithin_le_nhds)
  have hpt : Tendsto G (pure (0:ℝ)) (nhds (Gcand 0 0)) := by
    rw [tendsto_pure_left]
    intro s hs
    rw [hval]; exact mem_of_mem_nhds hs
  have hsplit : nhds (0:ℝ) = (𝓝[≠] (0:ℝ)) ⊔ pure (0:ℝ) := (nhdsNE_sup_pure (0:ℝ)).symm
  rw [hsplit, tendsto_sup]
  exact ⟨hpunctLim, hpt⟩

/-- **PROVEN — `ContinuousAt G (n:ℝ)` for EVERY integer `n`** (origin via `g_continuousAt_zero`,
nonzero integers via `g_continuousAt_int_ne_zero`). -/
theorem g_continuousAt_int (n : ℤ) : ContinuousAt G (n : ℝ) := by
  by_cases hn : n = 0
  · subst hn; simpa using g_continuousAt_zero
  · exact g_continuousAt_int_ne_zero hn

/-- **PROVEN — `ContinuousAt GC (n:ℝ)` for every integer `n`.** -/
theorem gC_continuousAt_int (n : ℤ) : ContinuousAt GC (n : ℝ) := by
  have h := g_continuousAt_int n
  have hofR : ContinuousAt (fun y : ℝ => (y : ℂ)) (G (n : ℝ)) :=
    Complex.continuous_ofReal.continuousAt
  exact (hofR.comp h).congr (by filter_upwards with x; simp [Function.comp, GC_apply])

/-- **PROVEN (DEAD_ENDS #20 repair) — `GContinuousAtIntegers`.**  With the repaired `G`
carrying `G 0 = 1`, `G` (hence `GC`) is continuous at every integer.  This DISCHARGES the
residual that was previously unsatisfiable purely because of the missing removable-value
branch at the origin. -/
theorem gContinuousAtIntegers_proven : GContinuousAtIntegers :=
  fun n => gC_continuousAt_int n

/-! ## §8 — The repaired `G` IS continuous everywhere; `GContinuous` discharged

With the DEAD_ENDS #20 patch, `VaalerHPrimeEqTwoJ.G` already carries the removable value
`G 0 = 1`, so no separate corrected function is needed: `G` itself is continuous everywhere
(off ℤ by the committed `VaalerGRegularity.G_continuousAt_of_notMem`; at every integer by
`g_continuousAt_int`).  Hence `GContinuous := Continuous GC` is provable. -/

/-- **PROVEN — `ContinuousAt G x₀` for EVERY `x₀ : ℝ`.**  Off ℤ by the committed
`G_continuousAt_of_notMem`; at the integers by `g_continuousAt_int` (origin + nonzero ints). -/
theorem g_continuousAt (x₀ : ℝ) : ContinuousAt G x₀ := by
  by_cases hint : x₀ ∈ Set.range ((↑) : ℤ → ℝ)
  · obtain ⟨n, hn⟩ := hint
    rw [← hn]; exact g_continuousAt_int n
  · exact G_continuousAt_of_notMem hint

/-- **PROVEN — `Continuous G`** (the repaired half-derivative is continuous everywhere). -/
theorem g_continuous : Continuous G :=
  continuous_iff_continuousAt.mpr g_continuousAt

/-- **PROVEN — `Continuous GC`**, i.e. `Continuous (fun x => (G x : ℂ))`.  `GC = (G : ℂ)`
is the composition of the continuous `G` with `Complex.ofReal`. -/
theorem gContinuous_holds : Continuous (fun x : ℝ => (G x : ℂ)) :=
  Complex.continuous_ofReal.comp g_continuous

/-- **PROVEN — `GContinuous` (the bundled minor residual `Continuous GC`) is DISCHARGED.**
Combines the proven off-ℤ continuity with the now-provable integer continuity
(`gContinuousAtIntegers_proven`) via the committed assembly
`VaalerGRegularity.gContinuous_of_offInt_of_atInt`. -/
theorem gContinuous_proven : VaalerGCFourierMatch.GContinuous :=
  gContinuous_of_offInt_of_atInt gContinuousAtIntegers_proven

/-- The corrected half-derivative `Gfixed` now coincides with the (already-repaired) `G`
everywhere: since `G 0 = 1`, the `if x = 0 then 1` branch agrees with `G`.  Kept for
backward compatibility; `Gfixed = G`. -/
def Gfixed (x : ℝ) : ℝ := if x = 0 then 1 else G x

/-- `Gfixed = G` everywhere (the patched `G 0 = 1` makes the `x = 0` branch agree). -/
theorem gfixed_eq_g : Gfixed = G := by
  funext x
  unfold Gfixed
  by_cases hx : x = 0
  · rw [if_pos hx, hx, g_zero_eq_one]
  · rw [if_neg hx]

/-- **PROVEN — `Continuous Gfixed`** (immediate from `Gfixed = G` and `g_continuous`). -/
theorem gfixed_continuous : Continuous Gfixed := by rw [gfixed_eq_g]; exact g_continuous

/-! ## §9 — The decay residual `GLargeArgDecay`: reduction to the genuine real cancellation -/

/-- **Residual (the genuine large-argument `O(1/x²)` cancellation of `½H′`), a precise named
`Prop` — NOT an axiom).**  For large `|x|`, the explicit REAL half-derivative `G` decays like
`x⁻²`:  there exist `R₀ ≥ 1`, `C` with `|G x| ≤ C·(x²)⁻¹` for all `R₀ ≤ |x|`.

This is the actual analytic content (Vaaler eq. (2.27)/(2.32), `½H′ = J = O((1+|x|)⁻²)`):
off the integers `G x = (sin πx/π)(cos πx)·B(x) + ½(sin πx/π)²·(∑−2(x∓(k+1))⁻³ − 2x⁻²)`, the
`(sin πx/π)²·B(x)` product stays `O(1)` (the squared-cosecant identity makes
`B(x) ∼ (π/sin πx)²`) and the cube tails contribute the `O(x⁻²)` gain AFTER the leading
`O(x⁻¹)` terms cancel (`H → ±1`, `H′ → 0`).  A TRUE statement about the explicit `G`; the
genuinely-delicate leading-order cancellation is exactly this `Prop`. -/
def GLargeArgCancellation : Prop :=
  ∃ R₀ C : ℝ, 1 ≤ R₀ ∧ ∀ x : ℝ, R₀ ≤ |x| → |G x| ≤ C * (x ^ 2)⁻¹

/-- **PROVEN — `GLargeArgCancellation → GLargeArgDecay`.**  The real-to-complex reduction:
`‖GC x‖ = ‖(G x : ℂ)‖ = |G x|` (`Complex.norm_real`), so the real `x⁻²` bound on `|G x|`
transports verbatim to the complex `‖GC x‖` bound of `GLargeArgDecay`. -/
theorem gLargeArgDecay_of_cancellation (h : GLargeArgCancellation) :
    MathExtras.NumberTheory.Analysis.VaalerDecayBounds.GLargeArgDecay := by
  obtain ⟨R₀, C, hR₀, hC⟩ := h
  refine ⟨R₀, C, hR₀, ?_⟩
  intro x hx
  have hnorm : ‖GC x‖ = |G x| := by rw [GC_apply, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  exact hC x hx

#print axioms contDiff_fejerK
#print axioms continuous_deriv_fejerK_shift
#print axioms hasDerivAt_fejerK_shift_offInt
#print axioms hasDerivAt_two_mul_id_fejerK_offZero
#print axioms puncturedNegCube_continuousAt
#print axioms puncturedPosCube_continuousAt
#print axioms deriv_fejerK_shift_int
#print axioms deriv_two_mul_id_fejerK_int_ne_zero
#print axioms cubeNeg_unified_split
#print axioms cubePos_unified_split
#print axioms gCand_continuousAt
#print axioms g_eq_gCand_offInt
#print axioms g_continuousAt_int_ne_zero
#print axioms gC_continuousAt_int_ne_zero
#print axioms g_zero_eq_one
#print axioms gCand_zero_eq_one
#print axioms g_continuousAt_zero
#print axioms g_continuousAt_int
#print axioms gC_continuousAt_int
#print axioms gContinuousAtIntegers_proven
#print axioms g_continuous
#print axioms gContinuous_holds
#print axioms gContinuous_proven
#print axioms gfixed_continuous
#print axioms gLargeArgDecay_of_cancellation

end MathExtras.NumberTheory.Analysis.VaalerGRegularityProof

end
