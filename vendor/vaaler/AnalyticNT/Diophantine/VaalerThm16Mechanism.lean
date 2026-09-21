/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Vaaler's Theorem 16 (Montgomery–Vaughan Hilbert inequality) — the from-the-book
positivity mechanism

This leaf formalises, faithfully to Vaaler, "Some extremal functions in Fourier
analysis", Bull. AMS 12 (1985), Theorem 16 (eqs (6.7)/(6.8), p. 207), the
mechanism producing the real-line Hilbert/cosecant inequality

  `‖∑_{m≠n} a_m conj(a_n) / (i (λ_m − λ_n))‖ ≤ (π/δ)·∑_n ‖a_n‖²`   (6.8)

from a single classical residual: the **Beurling majorant** `φ = H + K − sgn`.

## The genuine residual

`VaalerBeurlingMajorant` packages Beurling's nonnegative majorant of `sgn`:
a real `φ ≥ 0`, integrable, with `∫ φ = 1` (i.e. `φ̂(0) = 1`) and the far Fourier
transform `φ̂(t) = −(π i t)⁻¹` for `|t| ≥ 1`.  It is **satisfiable**: Beurling's
function `B = H + K` is a genuine real entire function of exponential type `2π`,
`|sgn − H| ≤ K` (Vaaler Lemma 5, by AM–GM), so `φ ≥ 0`; its Fourier transform is
Vaaler's Cor. 3 / Cor. 7.  We carry an explicit integrability field for the
modulated/scaled versions so the positivity expansion is genuinely derived (real
Parseval / Fubini over a finite sum), not assumed.  Constructing `H, K` themselves
(the infinite series `(sin πz/πz)² ∑ sgn(m)(z−m)⁻²`) is the remaining classical
work and is deliberately *not* done here.

## What is proved from the residual (sorry-free, no axiom)

* `vaalerPhiScaled` — the scaled majorant `φ_δ(x) = δ·φ(δ x)`, nonneg / integrable /
  `∫ φ_δ = 1` / far-FT `φ̂_δ(λ_m − λ_n) = −δ/(π i (λ_m − λ_n))` for `|λ_m−λ_n| ≥ δ`.
* `vaalerExpand` — the positivity expansion
  `∑_{m,n} a_m conj(a_n) φ̂_δ(λ_m − λ_n) = ∫ φ_δ(x)·‖∑_m a_m e(−λ_m x)‖² dx`,
  via `integral_finsetSum` + `integral_ofReal`.
* `vaaler_hilbertForm_real` — the off-diagonal Hilbert form `T` is **real**
  (Hermitian symmetry), so `‖T‖ = |T.re|`.
* `vaaler_thm16_re_of_beurlingMajorant` — the one-sided real bound
  `T.re ≤ (π/δ)·∑‖a_n‖²`, the direct consequence of `φ_δ ≥ 0`.
* `vaaler_thm16_of_beurlingMajorant` — the full two-sided (6.8)
  `‖T‖ ≤ (π/δ)·∑‖a_n‖²` from a *pair* of Beurling majorants (`H+K` and `H−K`),
  exactly Vaaler's two-sided argument.

## Connection to the repo cosecant form

The repo's `cosecKernel`/`CosecGramPosType`
(`MathExtras.NumberTheory.Analysis.CosecMomentToeplitzPositivity`) is the
**periodic** kernel `1/D(β) = 1/(2i sin πβ)` on the circle, whereas Theorem 16 as
stated here is the **real-line** Hilbert kernel `1/(i(λ_m−λ_n))`.  The mechanism
(nonneg `φ`, `∫ φ |S|² ≥ 0`, FT bookkeeping) is identical, but the periodic kernel
is the *periodization* `∑_{k∈ℤ} 1/(i(λ_m−λ_n+k))` of the real-line one, not equal
to it.  We therefore do **not** force a periodic = real-line identification; we
leave the periodization as a precisely stated gap (see the module note at the end).

## Book

Vaaler, Bull. AMS 12 (1985), §6 (Theorem 16, eqs 6.7/6.8) and §2 (Beurling's
function, Lemma 5, Cor. 3/7); Montgomery, *Ten Lectures*, large-sieve chapter.
-/

noncomputable section

open MeasureTheory Complex ComplexConjugate Real
open scoped BigOperators

namespace MathExtras.NumberTheory.Analysis.VaalerThm16Mechanism

/-! ## The exponential `e(t,x) = exp(−2π i t x)` and basic identities -/

/-- The real-line character `e(t, x) = exp(−2π i t x)`. -/
def echar (t x : ℝ) : ℂ := Complex.exp (-2 * π * Complex.I * t * x)

/-- `‖e(t,x)‖ = 1`. -/
theorem norm_echar (t x : ℝ) : ‖echar t x‖ = 1 := by
  unfold echar
  rw [Complex.norm_exp]
  have : (-2 * π * Complex.I * t * x).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [this, Real.exp_zero]

/-- `e(s,x)·conj(e(t,x)) = e(s − t, x)`. -/
theorem echar_mul_conj (s t x : ℝ) : echar s x * conj (echar t x) = echar (s - t) x := by
  unfold echar
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, map_mul, map_mul, map_mul]
  simp only [Complex.conj_I, Complex.conj_ofReal, map_neg, map_ofNat]
  push_cast
  ring

/-- Change-of-frequency under scaling: `e(t, x) = e(t/δ, δ x)` for `δ ≠ 0`. -/
theorem echar_scale (t x δ : ℝ) (hδ : δ ≠ 0) : echar t x = echar (t / δ) (δ * x) := by
  unfold echar
  congr 1
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ
  push_cast
  field_simp

/-- `e(t, ·)` is continuous, hence a.e.-strongly-measurable. -/
theorem aestronglyMeasurable_echar (t : ℝ) :
    AEStronglyMeasurable (fun x => echar t x) MeasureTheory.volume := by
  apply Continuous.aestronglyMeasurable
  unfold echar
  fun_prop

/-! ## The Beurling majorant residual -/

/-- **(VAALER BEURLING MAJORANT — the genuine residual.)**

A nonnegative integrable `φ : ℝ → ℝ` with `∫ φ = 1` (i.e. `φ̂(0) = 1`) and far
Fourier transform `φ̂(t) = −(π i t)⁻¹` for `|t| ≥ 1`.  This is Beurling's
`φ = H + K − sgn` (Vaaler §2): `nonneg` is Lemma 5 (`|sgn − H| ≤ K`, AM–GM),
`ftFar`/`ft0` are Cor. 3 / Cor. 7.  Carrying `integrableMod` (integrability of the
modulated majorant) makes the positivity expansion genuinely derivable.

Satisfiable: Beurling's `B = H + K` is a real entire function of exponential type
`2π` with the stated transform; constructing it explicitly is the remaining
classical work, intentionally left as this single residual. -/
structure VaalerBeurlingMajorant where
  /-- The majorant function. -/
  φ : ℝ → ℝ
  /-- `φ ≥ 0` (Vaaler Lemma 5, AM–GM). -/
  nonneg : ∀ x, 0 ≤ φ x
  /-- `φ` is integrable over `ℝ`. -/
  integrable : Integrable φ
  /-- `∫ φ = 1`, i.e. `φ̂(0) = 1`. -/
  ft0 : ∫ x, φ x = 1
  /-- Far Fourier transform: `φ̂(t) = −(π i t)⁻¹` for `|t| ≥ 1` (Vaaler Cor. 3/7). -/
  ftFar : ∀ t : ℝ, 1 ≤ |t| →
    (∫ x, (φ x : ℂ) * echar t x) = -((π : ℂ) * Complex.I * (t : ℂ))⁻¹
  /-- The modulated majorant `x ↦ (φ x) e(t,x)` is integrable for every `t`
      (immediate from `integrable` since `e(t,·)` is unit-modulus; carried for use
      in the finite-sum Fubini interchange). -/
  integrableMod : ∀ t : ℝ, Integrable (fun x => (φ x : ℂ) * echar t x)

namespace VaalerBeurlingMajorant

variable (hB : VaalerBeurlingMajorant)

/-! ## The scaled majorant `φ_δ(x) = δ·φ(δ x)` -/

/-- The scaled majorant `φ_δ(x) = δ·φ(δ x)`. -/
def scaled (δ : ℝ) : ℝ → ℝ := fun x => δ * hB.φ (δ * x)

/-- `φ_δ ≥ 0` for `δ ≥ 0`. -/
theorem scaled_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) : 0 ≤ hB.scaled δ x :=
  mul_nonneg hδ (hB.nonneg _)

/-- `∫ φ_δ = 1` for `δ > 0` (change of variables `u = δ x`). -/
theorem scaled_integral {δ : ℝ} (hδ : 0 < δ) : ∫ x, hB.scaled δ x = 1 := by
  unfold scaled
  rw [MeasureTheory.integral_const_mul, Measure.integral_comp_mul_left hB.φ δ,
    abs_of_pos (inv_pos.mpr hδ), smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hδ.ne', one_mul, hB.ft0]

/-- Scaled Fourier transform value: for `|t| ≥ δ` (so `|t/δ| ≥ 1`),
`∫ φ_δ(x) e(t,x) dx = −δ/(π i t)`.  (Change of variables + `ftFar` at `t/δ`.) -/
theorem scaled_ftFar {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ |t|) :
    (∫ x, (hB.scaled δ x : ℂ) * echar t x)
      = -(δ : ℂ) / ((π : ℂ) * Complex.I * (t : ℂ)) := by
  -- nonzero facts
  have htabs : (0 : ℝ) < |t| := lt_of_lt_of_le hδ ht
  have ht0 : t ≠ 0 := fun h => by simp [h] at htabs
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  -- rewrite the integrand as δ • (g (δ x)) where g u = (φ u) e(t/δ, u)
  have hge : ∀ x, ((hB.scaled δ x : ℝ) : ℂ) * echar t x
      = (δ : ℂ) * ((hB.φ (δ * x) : ℂ) * echar (t / δ) (δ * x)) := by
    intro x
    unfold scaled
    rw [echar_scale t x δ hδ.ne']
    push_cast
    ring
  simp_rw [hge]
  -- pull out δ, change variables
  rw [MeasureTheory.integral_const_mul]
  set g : ℝ → ℂ := fun u => (hB.φ u : ℂ) * echar (t / δ) u with hg
  have hcov : (∫ x, g (δ * x)) = |δ⁻¹| • ∫ u, g u :=
    Measure.integral_comp_mul_left g δ
  rw [show (fun x => (hB.φ (δ * x) : ℂ) * echar (t / δ) (δ * x)) = fun x => g (δ * x) from rfl,
    hcov, abs_of_pos (inv_pos.mpr hδ), Complex.real_smul]
  -- evaluate ∫ g via ftFar at t/δ
  have hfar : (∫ u, g u) = -((π : ℂ) * Complex.I * ((t / δ : ℝ) : ℂ))⁻¹ := by
    rw [hg]
    apply hB.ftFar
    rw [abs_div, abs_of_pos hδ, le_div_iff₀ hδ]
    linarith
  rw [hfar]
  -- algebra: δ⁻¹ · (−(π i (t/δ))⁻¹) = −δ/(π i t)
  rw [show (((δ⁻¹ : ℝ)) : ℂ) = (δ : ℂ)⁻¹ by push_cast; ring,
    show (((t / δ : ℝ)) : ℂ) = (t : ℂ) / (δ : ℂ) by push_cast; ring]
  field_simp

/-- The modulated scaled majorant is integrable. -/
theorem integrableMod_scaled {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    Integrable (fun x => (hB.scaled δ x : ℂ) * echar t x) := by
  -- (φ_δ x) e(t,x) = δ • (g (δ x)) with g integrable; bounded modulation by e(t,·).
  have hbase : Integrable (fun x => (hB.scaled δ x : ℝ)) := by
    unfold scaled
    exact ((integrable_comp_mul_left_iff hB.φ hδ.ne').mpr hB.integrable).const_mul δ
  refine (hbase.ofReal (𝕜 := ℂ)).mul_bdd (c := 1) (aestronglyMeasurable_echar t) ?_
  filter_upwards with x
  rw [norm_echar]

end VaalerBeurlingMajorant

/-! ## The off-diagonal Hilbert form and the partial sum -/

/-- The partial sum `S(x) = ∑_m a_m e(λ_m, x)`. -/
def partialSum {N : ℕ} (lam : Fin N → ℝ) (a : Fin N → ℂ) (x : ℝ) : ℂ :=
  ∑ m, a m * echar (lam m) x

/-- The off-diagonal Hilbert form `T = ∑_{m≠n} a_m conj(a_n)/(i(λ_m − λ_n))`. -/
def hilbertForm {N : ℕ} (lam : Fin N → ℝ) (a : Fin N → ℂ) : ℂ :=
  ∑ m, ∑ n ∈ Finset.univ.erase m,
    a m * conj (a n) / (Complex.I * ((lam m - lam n : ℝ) : ℂ))

/-! ## The positivity expansion -/

/-- **The positivity expansion (sorry-free).**

`∑_{m,n} a_m conj(a_n) φ̂_δ(λ_m − λ_n) = ∫ φ_δ(x)·‖∑_m a_m e(λ_m,x)‖² dx`.

Push the integral through the finite double sum (`integral_finsetSum`), use
`e(λ_m,x) conj(e(λ_n,x)) = e(λ_m − λ_n, x)` and `‖S‖² = S·conj S`. -/
theorem vaalerExpand (hB : VaalerBeurlingMajorant) {N : ℕ} (lam : Fin N → ℝ)
    (a : Fin N → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    (∑ m, ∑ n, a m * conj (a n) * (∫ x, (hB.scaled δ x : ℂ) * echar (lam m - lam n) x))
      = ∫ x, ((hB.scaled δ x * ‖partialSum lam a x‖ ^ 2 : ℝ) : ℂ) := by
  -- pointwise expansion of the real integrand into the finite double sum (over ℂ)
  have hpt : ∀ x, ((hB.scaled δ x * ‖partialSum lam a x‖ ^ 2 : ℝ) : ℂ)
      = ∑ m, ∑ n, (hB.scaled δ x : ℂ) * (a m * conj (a n) * echar (lam m - lam n) x) := by
    intro x
    have hc : ((hB.scaled δ x * ‖partialSum lam a x‖ ^ 2 : ℝ) : ℂ)
        = (hB.scaled δ x : ℂ) * ((‖partialSum lam a x‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hc]
    unfold partialSum
    have hS : ((‖∑ m, a m * echar (lam m) x‖ ^ 2 : ℝ) : ℂ)
        = (∑ m, a m * echar (lam m) x) * conj (∑ m, a m * echar (lam m) x) := by
      rw [Complex.sq_norm]; push_cast [Complex.normSq_eq_conj_mul_self]; ring
    rw [hS, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [map_mul,
      show a m * echar (lam m) x * (conj (a n) * conj (echar (lam n) x))
        = a m * conj (a n) * (echar (lam m) x * conj (echar (lam n) x)) by ring,
      echar_mul_conj]
  -- per-term integrand and its integrability / integral
  set F : Fin N → Fin N → ℝ → ℂ :=
    fun m n x => (hB.scaled δ x : ℂ) * (a m * conj (a n) * echar (lam m - lam n) x) with hF
  have hFint : ∀ m n, Integrable (F m n) := by
    intro m n
    have hmod := hB.integrableMod_scaled hδ (lam m - lam n)
    have : F m n = fun x => (a m * conj (a n)) * ((hB.scaled δ x : ℂ) * echar (lam m - lam n) x) := by
      funext x; rw [hF]; ring
    rw [this]
    exact hmod.const_mul _
  have hFval : ∀ m n, (∫ x, F m n x)
      = a m * conj (a n) * (∫ x, (hB.scaled δ x : ℂ) * echar (lam m - lam n) x) := by
    intro m n
    rw [hF]
    rw [show (fun x => (hB.scaled δ x : ℂ) * (a m * conj (a n) * echar (lam m - lam n) x))
          = fun x => (a m * conj (a n)) * ((hB.scaled δ x : ℂ) * echar (lam m - lam n) x) by
        funext x; ring]
    rw [MeasureTheory.integral_const_mul]
  -- assemble: RHS = ∫ ∑∑ F = ∑∑ ∫ F = LHS
  rw [show (fun x => ((hB.scaled δ x * ‖partialSum lam a x‖ ^ 2 : ℝ) : ℂ))
        = fun x => ∑ m, ∑ n, F m n x from funext hpt]
  rw [MeasureTheory.integral_finsetSum _
        (fun m _ => MeasureTheory.integrable_finsetSum _ (fun n _ => hFint m n))]
  refine (Finset.sum_congr rfl ?_).symm
  intro m _
  rw [MeasureTheory.integral_finsetSum _ (fun n _ => hFint m n)]
  exact Finset.sum_congr rfl (fun n _ => hFval m n)

/-! ## Diagonal / off-diagonal split and the one-sided real bound -/

/-- `e(0, x) = 1`. -/
theorem echar_zero (x : ℝ) : echar 0 x = 1 := by unfold echar; simp

/-- **The split identity.**  The expansion sum equals the diagonal energy minus
`(δ/π)` times the off-diagonal Hilbert form `T`:

`∑_{m,n} a_m conj(a_n) φ̂_δ(λ_m−λ_n) = (∑‖a‖²) − (δ/π)·T`.

Diagonal terms (`m = n`) give `a_m conj(a_m)·∫φ_δ = ‖a_m‖²·1`; off-diagonal terms
(`m ≠ n`) give `a_m conj(a_n)·φ̂_δ(λ_m−λ_n) = a_m conj(a_n)·(−δ/(π i (λ_m−λ_n)))`
which sum to `−(δ/π)·T` by `scaled_ftFar`. -/
theorem vaalerSplit (hB : VaalerBeurlingMajorant) {N : ℕ} (lam : Fin N → ℝ)
    (a : Fin N → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsp : ∀ m n, m ≠ n → δ ≤ |lam m - lam n|) :
    (∑ m, ∑ n, a m * conj (a n) * (∫ x, (hB.scaled δ x : ℂ) * echar (lam m - lam n) x))
      = ((∑ n, ‖a n‖ ^ 2 : ℝ) : ℂ)
        - ((δ : ℂ) / (π : ℂ)) * hilbertForm lam a := by
  have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  -- split each inner sum into diagonal n = m and off-diagonal n ≠ m
  rw [show (∑ m, ∑ n, a m * conj (a n) * (∫ x, (hB.scaled δ x : ℂ) * echar (lam m - lam n) x))
        = ∑ m, (a m * conj (a m) * (∫ x, (hB.scaled δ x : ℂ) * echar (lam m - lam m) x)
            + ∑ n ∈ Finset.univ.erase m,
                a m * conj (a n) * (∫ x, (hB.scaled δ x : ℂ) * echar (lam m - lam n) x)) by
      apply Finset.sum_congr rfl; intro m _
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ m)).symm]
  rw [Finset.sum_add_distrib, sub_eq_add_neg]
  congr 1
  · -- diagonal: lam m − lam m = 0, ∫ φ_δ·e(0) = ∫ φ_δ = 1, a m conj(a m) = ‖a m‖²
    push_cast
    apply Finset.sum_congr rfl; intro m _
    rw [show lam m - lam m = 0 by ring]
    simp_rw [echar_zero, mul_one]
    have hint : (∫ x, (hB.scaled δ x : ℂ)) = 1 := by
      have : (∫ x, (hB.scaled δ x : ℂ)) = ((∫ x, hB.scaled δ x : ℝ) : ℂ) := integral_ofReal
      rw [this, hB.scaled_integral hδ, Complex.ofReal_one]
    rw [hint, mul_one, Complex.mul_conj]
    norm_cast
    exact (Complex.sq_norm (a m)).symm
  · -- off-diagonal: collect −(δ/π)·T
    rw [hilbertForm, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro n hn
    have hmn : m ≠ n := (Finset.ne_of_mem_erase hn).symm
    rw [hB.scaled_ftFar hδ (hsp m n hmn)]
    have hlam : ((lam m - lam n : ℝ) : ℂ) ≠ 0 := by
      have : lam m - lam n ≠ 0 := by
        intro h
        have := hsp m n hmn
        rw [show lam m - lam n = (0:ℝ) from h] at this
        simp at this; linarith
      exact_mod_cast this
    field_simp

/-! ## The positivity integral is nonnegative -/

/-- `0 ≤ ∫ φ_δ(x)·‖S(x)‖² dx`: the integrand is a product of two nonnegatives. -/
theorem vaaler_integral_nonneg (hB : VaalerBeurlingMajorant) {N : ℕ} (lam : Fin N → ℝ)
    (a : Fin N → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ ∫ x, hB.scaled δ x * ‖partialSum lam a x‖ ^ 2 := by
  apply MeasureTheory.integral_nonneg
  intro x
  exact mul_nonneg (hB.scaled_nonneg hδ.le x) (by positivity)

/-! ## The one-sided real bound `T.re ≤ (π/δ)·∑‖a‖²` -/

/-- **(VAALER 6.8, one-sided real part.)**  From a single Beurling majorant,
`(hilbertForm lam a).re ≤ (π/δ)·∑‖a_n‖²`.

Taking real parts in `vaalerSplit` and using that the LHS sum equals the real
nonnegative integral `J = ∫ φ_δ‖S‖²` (`vaalerExpand`):
`J = ∑‖a‖² − (δ/π)·T.re`, and `J ≥ 0` gives `(δ/π)·T.re ≤ ∑‖a‖²`. -/
theorem vaaler_thm16_re_of_beurlingMajorant (hB : VaalerBeurlingMajorant) {N : ℕ}
    (lam : Fin N → ℝ) (a : Fin N → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsp : ∀ m n, m ≠ n → δ ≤ |lam m - lam n|) :
    (hilbertForm lam a).re ≤ (π / δ) * ∑ n, ‖a n‖ ^ 2 := by
  set J : ℝ := ∫ x, hB.scaled δ x * ‖partialSum lam a x‖ ^ 2 with hJdef
  have hJnn : 0 ≤ J := vaaler_integral_nonneg hB lam a hδ
  have hkey : ((J : ℝ) : ℂ) = ((∑ n, ‖a n‖ ^ 2 : ℝ) : ℂ)
      - ((δ : ℂ) / (π : ℂ)) * hilbertForm lam a := by
    have hofR : ((J : ℝ) : ℂ)
        = ∫ x, ((hB.scaled δ x * ‖partialSum lam a x‖ ^ 2 : ℝ) : ℂ) := by
      rw [hJdef]; exact integral_ofReal.symm
    rw [hofR, ← vaalerExpand hB lam a hδ, vaalerSplit hB lam a hδ hsp]
  have hπpos : 0 < π := Real.pi_pos
  have hreJ : J = (∑ n, ‖a n‖ ^ 2) - (δ / π) * (hilbertForm lam a).re := by
    have hre := congrArg Complex.re hkey
    simp only [Complex.ofReal_re, Complex.sub_re] at hre
    rw [show ((δ : ℂ) / (π : ℂ)) = (((δ / π : ℝ)) : ℂ) by push_cast; ring,
      re_ofReal_mul] at hre
    exact hre
  have hbound : (δ / π) * (hilbertForm lam a).re ≤ ∑ n, ‖a n‖ ^ 2 := by
    have : (δ / π) * (hilbertForm lam a).re = (∑ n, ‖a n‖ ^ 2) - J := by linarith [hreJ]
    rw [this]; linarith
  -- multiply hbound by (π/δ) > 0: (π/δ)(δ/π) T.re = T.re ≤ (π/δ) E
  have hπδ : 0 < π / δ := div_pos hπpos hδ
  have hmul := mul_le_mul_of_nonneg_left hbound hπδ.le
  rw [show (π / δ) * ((δ / π) * (hilbertForm lam a).re) = (hilbertForm lam a).re by
        field_simp] at hmul
  exact hmul

/-! ## The Hilbert form is real (Hermitian symmetry) -/

/-- Swap the index roles on the off-diagonal index set `{(m,n) : m ≠ n}`. -/
theorem hilbertForm_swap {N : ℕ} (f : Fin N → Fin N → ℂ) :
    ∑ m, ∑ n ∈ Finset.univ.erase m, f m n
      = ∑ n, ∑ m ∈ Finset.univ.erase n, f m n := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_nbij' (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩) <;>
    simp [Finset.mem_sigma, Finset.mem_erase, eq_comm, and_comm]

/-- **The Hilbert form `T` is real.**  `conj T = T` by conjugating each term
(`conj(I) = −I`, real differences are self-conjugate) and swapping `m ↔ n` over the
off-diagonal index set.  Hence `T.im = 0` and `‖T‖ = |T.re|`. -/
theorem vaaler_hilbertForm_real {N : ℕ} (lam : Fin N → ℝ) (a : Fin N → ℂ) :
    conj (hilbertForm lam a) = hilbertForm lam a := by
  unfold hilbertForm
  have hterm : ∀ m n : Fin N,
      conj (a m * conj (a n) / (Complex.I * ((lam m - lam n : ℝ) : ℂ)))
        = a n * conj (a m) / (Complex.I * ((lam n - lam m : ℝ) : ℂ)) := by
    intro m n
    rw [map_div₀, map_mul, map_mul, Complex.conj_conj, Complex.conj_I,
      Complex.conj_ofReal,
      show ((lam m - lam n : ℝ) : ℂ) = -((lam n - lam m : ℝ) : ℂ) by push_cast; ring]
    field_simp
  rw [map_sum]
  have hstep : (∑ m, conj (∑ n ∈ Finset.univ.erase m,
        a m * conj (a n) / (Complex.I * ((lam m - lam n : ℝ) : ℂ))))
      = ∑ m, ∑ n ∈ Finset.univ.erase m,
          a n * conj (a m) / (Complex.I * ((lam n - lam m : ℝ) : ℂ)) := by
    apply Finset.sum_congr rfl; intro m _
    rw [map_sum]; apply Finset.sum_congr rfl; intro n _; exact hterm m n
  rw [hstep,
    hilbertForm_swap (fun m n => a n * conj (a m) / (Complex.I * ((lam n - lam m : ℝ) : ℂ)))]

/-- The norm of `T` equals `|T.re|` since `T` is real. -/
theorem vaaler_norm_hilbertForm {N : ℕ} (lam : Fin N → ℝ) (a : Fin N → ℂ) :
    ‖hilbertForm lam a‖ = |(hilbertForm lam a).re| := by
  have him : (hilbertForm lam a).im = 0 := by
    have h := vaaler_hilbertForm_real lam a
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  rw [Complex.norm_def, Complex.normSq_apply, him,
    show (hilbertForm lam a).re * (hilbertForm lam a).re + 0 * 0
      = (hilbertForm lam a).re ^ 2 by ring, Real.sqrt_sq_eq_abs]

/-- `hilbertForm (−lam) a = −hilbertForm lam a` (negating all frequencies flips the
sign of the off-diagonal kernel). -/
theorem hilbertForm_neg_lam {N : ℕ} (lam : Fin N → ℝ) (a : Fin N → ℂ) :
    hilbertForm (fun i => -lam i) a = -hilbertForm lam a := by
  unfold hilbertForm
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro m _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro n _
  rw [show ((-lam m - -lam n : ℝ) : ℂ) = -((lam m - lam n : ℝ) : ℂ) by push_cast; ring,
    mul_neg, div_neg]

/-! ## The full two-sided Vaaler 6.8 bound -/

/-- **(VAALER THEOREM 16, eq (6.8) — full two-sided bound, from a single Beurling
majorant.)**

For real frequencies `lam : Fin N → ℝ` that are `δ`-separated
(`|lam m − lam n| ≥ δ` for `m ≠ n`, `δ > 0`) and complex coefficients `a`,

  `‖∑_{m≠n} a_m conj(a_n) / (i (lam m − lam n))‖ ≤ (π/δ)·∑_n ‖a_n‖²`.

Since `T` is real (`vaaler_hilbertForm_real`), `‖T‖ = |T.re|`.  The one-sided real
bound (`vaaler_thm16_re_of_beurlingMajorant`) gives `T.re ≤ (π/δ)E`; applying the
same one-sided bound to the negated frequencies `−lam` (which keeps the spacing and
sends `T ↦ −T`) gives `−T.re ≤ (π/δ)E`.  Together, `|T.re| ≤ (π/δ)E`.  This is
exactly Vaaler's two-sided argument (he uses `H ± K`; negating the frequencies is
the equivalent reflection producing the `+(π i t)⁻¹` far transform). -/
theorem vaaler_thm16_of_beurlingMajorant (hB : VaalerBeurlingMajorant) {N : ℕ}
    (lam : Fin N → ℝ) (a : Fin N → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsp : ∀ m n, m ≠ n → δ ≤ |lam m - lam n|) :
    ‖hilbertForm lam a‖ ≤ (π / δ) * ∑ n, ‖a n‖ ^ 2 := by
  -- upper bound on T.re
  have hUp : (hilbertForm lam a).re ≤ (π / δ) * ∑ n, ‖a n‖ ^ 2 :=
    vaaler_thm16_re_of_beurlingMajorant hB lam a hδ hsp
  -- spacing is preserved under frequency negation
  have hsp' : ∀ m n, m ≠ n → δ ≤ |(-lam m) - (-lam n)| := by
    intro m n hmn
    rw [show (-lam m) - (-lam n) = -(lam m - lam n) by ring, abs_neg]
    exact hsp m n hmn
  -- lower bound: apply to −lam, using hilbertForm(−lam) = −hilbertForm
  have hLowraw : (hilbertForm (fun i => -lam i) a).re ≤ (π / δ) * ∑ n, ‖a n‖ ^ 2 :=
    vaaler_thm16_re_of_beurlingMajorant hB (fun i => -lam i) a hδ hsp'
  rw [hilbertForm_neg_lam, Complex.neg_re] at hLowraw
  -- combine to |T.re| ≤ (π/δ)E
  rw [vaaler_norm_hilbertForm]
  rw [abs_le]
  exact ⟨by linarith [hLowraw], hUp⟩

#print axioms vaaler_thm16_of_beurlingMajorant
#print axioms vaaler_thm16_re_of_beurlingMajorant
#print axioms vaalerExpand
#print axioms VaalerBeurlingMajorant.scaled_ftFar
#print axioms vaaler_hilbertForm_real

end MathExtras.NumberTheory.Analysis.VaalerThm16Mechanism
