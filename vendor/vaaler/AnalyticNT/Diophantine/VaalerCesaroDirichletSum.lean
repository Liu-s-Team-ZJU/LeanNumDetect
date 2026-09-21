/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The Cesàro/Fejér cosine telescoping sum (the closed form of the averaged remainder)

This NEW leaf proves the pure-trigonometric **Cesàro-Dirichlet identity** that is the exact
algebraic heart of the averaged oscillatory remainder `R_avg_M` of the minor-arc residual
`GCCesaroPlancherelData`
(`MathExtras.NumberTheory.Analysis.VaalerGCCesaroPlancherel`).

For `sin θ ≠ 0`,

    ∑_{N < M} cos((2N+1)·θ)  =  sin(2 M θ) / (2 · sin θ).

This is the Cesàro mean of the sharp oscillatory cores `cos(π(2N+1)t)`: averaging the sharp
truncations `HNcore N` (whose Fourier remainder carries `cos(π(2N+1)t)`) over `N < M` collapses
the cosine sum to the single Fejér/Dirichlet kernel `sin(2Mθ)/(2 sin θ)`, whose `L²` norm
(after the triangle / `cot` envelope) decays like `M^{-1/2}` — the smoothing that makes the
Fourier-side `L²`-convergence to `Ĵ` succeed.

## What this file PROVES (sorry/axiom-free, non-vacuous)

* `two_sin_mul_cos_odd` — **PROVEN**: the per-term telescoping identity
  `2·sin θ·cos((2N+1)θ) = sin(2(N+1)θ) − sin(2Nθ)` (product-to-sum, via `Real.sin_add`/
  `Real.sin_sub`).
* `sum_cos_odd_telescope` — **PROVEN**: `2·sin θ·∑_{N<M} cos((2N+1)θ) = sin(2Mθ)`
  (telescoping `Finset.sum_range_succ`).
* `sum_cos_odd_eq` — **PROVEN**: for `sin θ ≠ 0`,
  `∑_{N<M} cos((2N+1)θ) = sin(2Mθ)/(2 sin θ)` (divide out `2 sin θ`).

## Numerical confirmation (mpmath, dps 30)

`∑_{N<M} cos(π(2N+1)t) − sin(2πMt)/(2 sin πt) ≈ 0` (≤ `1e-30`) for `M ∈ {3,7,13}`,
`t ∈ {0.13, 0.37, 0.6, 0.91}`.

## Book

Vaaler, "Some extremal functions in Fourier analysis", Bull. AMS 12 (1985), §2, Theorem 6
(eqs (2.31)→(2.32), the oscillatory remainder); Zygmund, *Trigonometric Series* III.3 (Fejér's
theorem; the Dirichlet/Fejér kernel `sin(2Mθ)/(2 sin θ)`).
-/

noncomputable section

open Real
open scoped BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerCesaroDirichletSum

/-- **PROVEN — the product-to-sum telescoping term.**

    `2·sin θ·cos((2N+1)·θ) = sin(2(N+1)·θ) − sin(2N·θ)`.

Writing `2(N+1)θ = (2N+1)θ + θ` and `2Nθ = (2N+1)θ − θ`, expand the right side by
`Real.sin_add`/`Real.sin_sub`; the `cos·sin` cross terms add, the `sin·cos` terms cancel. -/
theorem two_sin_mul_cos_odd (θ : ℝ) (N : ℕ) :
    2 * Real.sin θ * Real.cos ((2 * (N : ℝ) + 1) * θ)
      = Real.sin (2 * ((N : ℝ) + 1) * θ) - Real.sin (2 * (N : ℝ) * θ) := by
  have h1 : 2 * ((N : ℝ) + 1) * θ = (2 * (N : ℝ) + 1) * θ + θ := by ring
  have h2 : 2 * (N : ℝ) * θ = (2 * (N : ℝ) + 1) * θ - θ := by ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]
  ring

/-- **PROVEN — the telescoping sum (cleared of the denominator).**

    `2·sin θ · ∑_{N<M} cos((2N+1)·θ) = sin(2 M θ)`.

Multiply through by `2 sin θ`, apply `two_sin_mul_cos_odd` termwise, and telescope the
`Finset.range` sum (`Finset.sum_range_succ`). -/
theorem sum_cos_odd_telescope (θ : ℝ) (M : ℕ) :
    2 * Real.sin θ * (∑ N ∈ Finset.range M, Real.cos ((2 * (N : ℝ) + 1) * θ))
      = Real.sin (2 * (M : ℝ) * θ) := by
  rw [Finset.mul_sum]
  -- replace each summand by the telescoping difference, then telescope.
  have key : (∑ N ∈ Finset.range M,
        2 * Real.sin θ * Real.cos ((2 * (N : ℝ) + 1) * θ))
      = Real.sin (2 * (M : ℝ) * θ) := by
    induction M with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, two_sin_mul_cos_odd θ K]
      push_cast; ring_nf
  exact key

/-- **PROVEN — the Cesàro/Fejér cosine-sum closed form.**

For `sin θ ≠ 0`,

    `∑_{N<M} cos((2N+1)·θ) = sin(2 M θ) / (2·sin θ)`.

Immediate from `sum_cos_odd_telescope` after dividing by the nonzero `2 sin θ`. -/
theorem sum_cos_odd_eq {θ : ℝ} (hθ : Real.sin θ ≠ 0) (M : ℕ) :
    (∑ N ∈ Finset.range M, Real.cos ((2 * (N : ℝ) + 1) * θ))
      = Real.sin (2 * (M : ℝ) * θ) / (2 * Real.sin θ) := by
  have h2 : (2 : ℝ) * Real.sin θ ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨by norm_num, hθ⟩
  rw [eq_div_iff h2, mul_comm]
  exact sum_cos_odd_telescope θ M

#print axioms two_sin_mul_cos_odd
#print axioms sum_cos_odd_telescope
#print axioms sum_cos_odd_eq

end MathExtras.NumberTheory.Analysis.VaalerCesaroDirichletSum
