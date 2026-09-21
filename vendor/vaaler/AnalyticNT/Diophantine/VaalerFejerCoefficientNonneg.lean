/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Nonnegativity of Vaaler's Fejér Fourier transform `Ĵ(t) = πt(1−t)cot(πt) + t`

## Statement

This leaf proves, sorry-free, the single scalar real-analysis inequality onto which
the entire minor-arc cosecant Hilbert core reduces (see the sibling file
`MathExtras.NumberTheory.Analysis.CosecFejerCoefficientConstruction`):

  `Ĵ(t) := π·t·(1−t)·cot(π·t) + t  ≥  0`   for all `t ∈ [0,1]`.

This is the nonnegativity of the Fourier transform of the Fejér kernel
`J = (sin πz / πz)²` in Vaaler, *Some extremal functions in Fourier analysis*,
Bull. AMS **12** (1985), Theorem 6, eq. (2.28).  Its nonnegativity is precisely
what makes Vaaler's nonnegative-coefficient interpolation of the cosecant data
solvable.

## Proof

On the literal Lean form the endpoints are trivial: `cot 0 = cos 0 / sin 0 = 1/0 = 0`
gives `Ĵ(0) = 0`, while at `t = 1` the `(1 − t)` factor annihilates the cotangent
term, leaving `Ĵ(1) = 1`.  (The paper's continuous values `Ĵ(0)=1`, `Ĵ(1)=0` differ
from the literal-formula values only at the removable singularities, where `≥ 0`
holds either way.)  The substance is the interior `t ∈ (0,1)`.  There `sin(πt) > 0`, and clearing the positive denominator
reduces `Ĵ(t) ≥ 0` to the trigonometric inequality

  `g(t) := π·(1−t)·cos(πt) + sin(πt)  ≥  0`.

Writing `u = 1 − t` and using `cos(πt) = −cos(πu)`, `sin(πt) = sin(πu)`, this is
`sin(πu) − π·u·cos(πu) ≥ 0`.  If `cos(πu) ≤ 0` it is immediate; if `cos(πu) > 0`
(i.e. `πu < π/2`) it is `tan(πu) ≥ πu`, the standard Mathlib bound `Real.le_tan`.

## Scope note (what this does and does not close)

This file proves the **scalar nonnegativity** `Ĵ ≥ 0` (`vaalerJhat_nonneg`), which is
the irreducible analytic fact named in the sibling file as the obstruction to
solvability of Vaaler's nonnegative-coefficient cosecant interpolation.  It is the
honest mathematical content of "Vaaler Thm 6 eq. (2.28)".  It does **not** by itself
mechanically rewrite the `def CosecFejerCoefficientInterpolation` (a full existence
statement about explicit interpolating coefficients), which would additionally
require the discrete moment-matching construction; see the report accompanying this
file.

## Book
Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985),
Thm 6 eq. (2.28).
-/

noncomputable section

open Real

namespace MathExtras.NumberTheory.Analysis.VaalerFejerCoefficientNonneg

/-- Vaaler's Fejér Fourier transform `Ĵ(t) = π·t·(1−t)·cot(π·t) + t`
(Bull. AMS 12 (1985), Thm 6, eq. (2.28)). -/
def vaalerJhat (t : ℝ) : ℝ := Real.pi * t * (1 - t) * Real.cot (Real.pi * t) + t

/-- **The binding trigonometric inequality.**  For `u ∈ (0,1)`,
`sin(π·u) − π·u·cos(π·u) ≥ 0`.  When `cos(π·u) ≤ 0` it is immediate; when
`cos(π·u) > 0` (so `π·u < π/2`) it is the standard bound `tan(π·u) ≥ π·u`
(`Real.le_tan`) multiplied by the positive `cos(π·u)`. -/
theorem sin_sub_mul_cos_nonneg {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 ≤ Real.sin (Real.pi * u) - Real.pi * u * Real.cos (Real.pi * u) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπu_pos : 0 < Real.pi * u := mul_pos hπ hu0
  have hπu_lt_pi : Real.pi * u < Real.pi := by
    have := mul_lt_mul_of_pos_left hu1 hπ; simpa using this
  have hsin_pos : 0 < Real.sin (Real.pi * u) :=
    Real.sin_pos_of_pos_of_lt_pi hπu_pos hπu_lt_pi
  rcases le_or_gt (Real.cos (Real.pi * u)) 0 with hcos | hcos
  · -- cos ≤ 0 : both terms nonnegative
    have h1 : 0 ≤ -(Real.pi * u * Real.cos (Real.pi * u)) := by
      have : 0 ≤ Real.pi * u := le_of_lt hπu_pos
      nlinarith [mul_nonneg this (neg_nonneg.mpr hcos)]
    linarith [hsin_pos]
  · -- cos > 0 : πu < π/2, use tan(πu) ≥ πu
    have hπu_lt_half : Real.pi * u < Real.pi / 2 := by
      -- cos(πu) > 0 with 0 < πu < π forces πu < π/2
      by_contra hge
      have hge' : Real.pi / 2 ≤ Real.pi * u := le_of_not_gt hge
      have : Real.cos (Real.pi * u) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hge' (by linarith)
      linarith
    have htan : Real.pi * u ≤ Real.tan (Real.pi * u) :=
      Real.le_tan (le_of_lt hπu_pos) hπu_lt_half
    -- tan = sin/cos ; `πu ≤ sin/cos` ⇒ `πu·cos ≤ sin` (cos > 0)
    rw [Real.tan_eq_sin_div_cos] at htan
    have hmul : Real.pi * u * Real.cos (Real.pi * u) ≤ Real.sin (Real.pi * u) :=
      (le_div_iff₀ hcos).mp htan
    linarith

/-- **Interior nonnegativity.**  For `t ∈ (0,1)`, `Ĵ(t) ≥ 0`.

`sin(πt) > 0`, so clearing the positive denominator in `cot(πt) = cos(πt)/sin(πt)`
reduces to `t·(π(1−t)cos(πt) + sin(πt)) ≥ 0`.  With `u = 1−t`, the bracket is
`sin(πu) − π·u·cos(πu) ≥ 0` (`sin_sub_mul_cos_nonneg`). -/
theorem vaalerJhat_nonneg_of_mem_Ioo {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 ≤ vaalerJhat t := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπt_pos : 0 < Real.pi * t := mul_pos hπ ht0
  have hπt_lt_pi : Real.pi * t < Real.pi := by
    have := mul_lt_mul_of_pos_left ht1 hπ; simpa using this
  have hsin_pos : 0 < Real.sin (Real.pi * t) :=
    Real.sin_pos_of_pos_of_lt_pi hπt_pos hπt_lt_pi
  have hsin_ne : Real.sin (Real.pi * t) ≠ 0 := ne_of_gt hsin_pos
  -- the bracket nonnegativity, via u = 1 - t
  have hbracket : 0 ≤ Real.pi * (1 - t) * Real.cos (Real.pi * t)
      + Real.sin (Real.pi * t) := by
    set u := 1 - t with hu
    have hu0 : 0 < u := by simp only [hu]; linarith
    have hu1 : u < 1 := by simp only [hu]; linarith
    have hcosrw : Real.cos (Real.pi * t) = -Real.cos (Real.pi * u) := by
      have : Real.pi * t = Real.pi - Real.pi * u := by simp only [hu]; ring
      rw [this, Real.cos_pi_sub]
    have hsinrw : Real.sin (Real.pi * t) = Real.sin (Real.pi * u) := by
      have : Real.pi * t = Real.pi - Real.pi * u := by simp only [hu]; ring
      rw [this, Real.sin_pi_sub]
    have hkey := sin_sub_mul_cos_nonneg hu0 hu1
    rw [hcosrw, hsinrw]
    nlinarith [hkey]
  -- Ĵ(t) = (t / sin(πt)) · (π(1-t)cos(πt) + sin(πt)) ≥ 0
  have hcot : Real.cot (Real.pi * t)
      = Real.cos (Real.pi * t) / Real.sin (Real.pi * t) := Real.cot_eq_cos_div_sin _
  have hfactor : vaalerJhat t
      = (t / Real.sin (Real.pi * t))
        * (Real.pi * (1 - t) * Real.cos (Real.pi * t) + Real.sin (Real.pi * t)) := by
    unfold vaalerJhat
    rw [hcot]
    field_simp
  rw [hfactor]
  apply mul_nonneg
  · exact div_nonneg (le_of_lt ht0) (le_of_lt hsin_pos)
  · exact hbracket

/-- **(VAALER Thm 6, eq. (2.28)) Nonnegativity of the Fejér Fourier transform.**

For all `t ∈ [0,1]`, `Ĵ(t) = π·t·(1−t)·cot(π·t) + t ≥ 0`.

The endpoints give `Ĵ(0) = 0` and `Ĵ(1) = 1` on the literal Lean form, and the
interior `t ∈ (0,1)` is `vaalerJhat_nonneg_of_mem_Ioo`. -/
theorem vaalerJhat_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ vaalerJhat t := by
  rcases eq_or_lt_of_le ht0 with hte0 | ht0'
  · -- t = 0 : Ĵ 0 = 0
    subst_vars
    simp [vaalerJhat]
  · rcases eq_or_lt_of_le ht1 with hte1 | ht1'
    · -- t = 1 : the `(1 - t)` factor kills the cot term, so `Ĵ 1 = 1 ≥ 0`.
      rw [hte1]
      have h1 : vaalerJhat 1 = 1 := by
        unfold vaalerJhat; simp
      rw [h1]; norm_num
    · exact vaalerJhat_nonneg_of_mem_Ioo ht0' ht1'

#print axioms sin_sub_mul_cos_nonneg
#print axioms vaalerJhat_nonneg_of_mem_Ioo
#print axioms vaalerJhat_nonneg

end MathExtras.NumberTheory.Analysis.VaalerFejerCoefficientNonneg
