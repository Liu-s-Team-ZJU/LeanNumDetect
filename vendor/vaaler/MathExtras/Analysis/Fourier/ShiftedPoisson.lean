/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Shifted Poisson summation formula

The classical Poisson summation formula relates a sum of a rapidly decaying
function over the integer lattice to a sum of its Fourier transform over the
dual lattice:

    ∑_{n ∈ ℤ} f(n) = ∑_{n ∈ ℤ} 𝓕f(n).

The *shifted* form, which is what is required by Helfgott's analysis (in
particular by the Beurling–Vaaler majorant construction in
`MathExtras/Analysis/SpecialFunctions/VaalerExtremalTrigPolynomial.lean`),
introduces a real shift `τ ∈ ℝ`:

    ∑_{n ∈ ℤ} f(n + τ) = ∑_{n ∈ ℤ} 𝓕f(n) · exp(2π i n τ).

This is the form sometimes called the *Poisson summation with a phase* or
*Poisson summation for the periodised translate*; cf. Vaaler 1985,
*Some extremal functions in Fourier analysis*, Bull. AMS 12 no. 2, eq. (5.3),
and Stein–Shakarchi, *Fourier Analysis*, vol. I, Princeton 2003, §5.3
Theorem 3.1; Folland, *Real Analysis*, 2nd ed., 1999, §8.4, Theorem 8.32.

## Mathlib content already covers this

Inspecting `Mathlib.Analysis.Fourier.PoissonSummation` shows that the
"unshifted" lemma actually carries a real parameter `x : ℝ`:

* `Real.tsum_eq_tsum_fourier` proves
  `∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle)`
  for continuous `f : ℝ → ℂ` with locally-summable shifted norms;
* `Real.tsum_eq_tsum_fourier_of_rpow_decay` does the same under
  rpow decay of `f` and `𝓕 f`;
* `SchwartzMap.tsum_eq_tsum_fourier` is the Schwartz specialisation.

Combined with `Real.fourier_coe_apply` (which expands
`fourier n (x : AddCircle 1)` to `exp (2π i n x)`), these *are* the shifted
formula. Below we record this fact in the explicit Helfgott-facing form,
both for general continuous `f` with rpow decay and for Schwartz `f`. No new
analytic content is introduced; this file is wrapping plumbing.
-/

import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Data.Int.Interval

/-!
# Shifted Poisson summation (explicit phase form)

Repackages Mathlib's `Real.tsum_eq_tsum_fourier`(`_of_rpow_decay`) and the
Schwartz specialisation into the explicit-phase shifted Poisson identity
`∑ₙ f(τ+n) = ∑ₙ 𝓕f(n)·exp(2πi n τ)`, plus finite-band (`Finset` / `natAbs ≤ N`)
specialisations. No new analytic content — plumbing for Helfgott's Vaaler /
Beurling–Vaaler majorant constructions.
-/

noncomputable section

open Complex Real
open scoped FourierTransform Real

namespace MathExtras.Fourier

lemma int_mem_Icc_neg_natCast_natCast_iff_natAbs_le (N : ℕ) (n : ℤ) :
    n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) ↔ n.natAbs ≤ N := by
  rw [Finset.mem_Icc]
  constructor
  · intro hn
    have h_abs : |n| ≤ (N : ℤ) := abs_le.mpr ⟨by linarith, by linarith⟩
    have hcast : (n.natAbs : ℤ) ≤ (N : ℤ) := by
      simpa [Int.natCast_natAbs] using h_abs
    exact_mod_cast hcast
  · intro hn
    have hcast : (n.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hn
    have hn_le_abs : n ≤ (n.natAbs : ℤ) := Int.le_natAbs
    have hneg_le_abs : -n ≤ ((-n).natAbs : ℤ) := Int.le_natAbs
    have hneg_abs : ((-n).natAbs : ℤ) = (n.natAbs : ℤ) := by
      rw [Int.natAbs_neg]
    have hn_le : n ≤ (N : ℤ) := le_trans hn_le_abs hcast
    have hneg_le : -n ≤ (N : ℤ) := by
      rw [hneg_abs] at hneg_le_abs
      exact le_trans hneg_le_abs hcast
    exact ⟨by linarith, hn_le⟩

/-- **Shifted Poisson summation, explicit phase form.**

Under the hypotheses of `Real.tsum_eq_tsum_fourier`, for every real shift `τ`,

  `∑_{n ∈ ℤ} f(τ + n) = ∑_{n ∈ ℤ} 𝓕f(n) · exp(2π i n τ)`.

This is a direct repackaging of `Real.tsum_eq_tsum_fourier`, using
`Real.fourier_coe_apply` to make the phase `exp(2π i n τ)` explicit in the
right-hand side (so the lemma can be used by callers that work with
`Complex.exp (2 * π * Complex.I * n * τ)` rather than with `fourier n`).

This is Vaaler 1985 eq. (5.3), Stein–Shakarchi vol. I §5.3 Thm. 3.1
(with the shift made explicit), or Folland §8.4 Thm. 8.32. -/
theorem shifted_poisson_summation_continuous {f : C(ℝ, ℂ)}
    (h_norm :
      ∀ K : TopologicalSpace.Compacts ℝ,
        Summable fun n : ℤ => ‖(f.comp <| ContinuousMap.addRight n).restrict K‖)
    (h_sum : Summable fun n : ℤ => 𝓕 (f : ℝ → ℂ) n) (τ : ℝ) :
    ∑' n : ℤ, f (τ + n) =
      ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n *
        Complex.exp (2 * π * Complex.I * n * τ) := by
  have hbase := Real.tsum_eq_tsum_fourier (f := f) h_norm h_sum τ
  -- Rewrite each `fourier n (τ : UnitAddCircle)` summand to its explicit
  -- exponential form.  This is `Real.fourier_coe_apply` at `T = 1`.
  have hpoint : ∀ n : ℤ,
      𝓕 (f : ℝ → ℂ) n * fourier n (τ : UnitAddCircle) =
        𝓕 (f : ℝ → ℂ) n *
          Complex.exp (2 * π * Complex.I * n * τ) := by
    intro n
    have hcoe : fourier n (τ : UnitAddCircle) =
        Complex.exp (2 * π * Complex.I * n * τ / 1) :=
      fourier_coe_apply (T := (1 : ℝ)) (n := n) (x := τ)
    simp [hcoe]
  calc
    ∑' n : ℤ, f (τ + n)
        = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n * fourier n (τ : UnitAddCircle) := hbase
    _ = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n *
            Complex.exp (2 * π * Complex.I * n * τ) := by
            exact tsum_congr hpoint

/-- **Finite-band shifted Poisson summation, continuous form.**

This is the form used in Vaaler's finite trigonometric-polynomial
constructions: once the Fourier transform vanishes off a finite set `S`, the
right side of shifted Poisson summation is a finite Fourier polynomial.  It is
just `shifted_poisson_summation_continuous` followed by `tsum_eq_sum`. -/
theorem shifted_poisson_summation_continuous_finite_support {f : C(ℝ, ℂ)}
    (h_norm :
      ∀ K : TopologicalSpace.Compacts ℝ,
        Summable fun n : ℤ => ‖(f.comp <| ContinuousMap.addRight n).restrict K‖)
    (h_sum : Summable fun n : ℤ => 𝓕 (f : ℝ → ℂ) n)
    (S : Finset ℤ)
    (h_support : ∀ n : ℤ, n ∉ S → 𝓕 (f : ℝ → ℂ) n = 0) (τ : ℝ) :
    ∑' n : ℤ, f (τ + n) =
      ∑ n ∈ S, 𝓕 (f : ℝ → ℂ) n *
        Complex.exp (2 * π * Complex.I * n * τ) := by
  rw [shifted_poisson_summation_continuous h_norm h_sum τ]
  exact tsum_eq_sum (s := S) (fun n hn => by
    rw [h_support n hn, zero_mul])

/-- **Shifted Poisson summation under rpow decay.**

For continuous `f : ℝ → ℂ` with `f` and `𝓕 f` both `O(|x|^(-b))` for some
`b > 1`, and every real shift `τ`,

  `∑_{n ∈ ℤ} f(τ + n) = ∑_{n ∈ ℤ} 𝓕f(n) · exp(2π i n τ)`.

This is the rpow-decay specialisation; in particular it applies to the
Beurling-`B` minus `sign` defect, which has `O(x^{-2})` tails. -/
theorem shifted_poisson_summation_rpow_decay {f : ℝ → ℂ}
    (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[Filter.cocompact ℝ] (|·| ^ (-b)))
    (hFf : (𝓕 f) =O[Filter.cocompact ℝ] (|·| ^ (-b))) (τ : ℝ) :
    ∑' n : ℤ, f (τ + n) =
      ∑' n : ℤ, 𝓕 f n *
        Complex.exp (2 * π * Complex.I * n * τ) := by
  have hbase := Real.tsum_eq_tsum_fourier_of_rpow_decay hc hb hf hFf τ
  have hpoint : ∀ n : ℤ,
      𝓕 f n * fourier n (τ : UnitAddCircle) =
        𝓕 f n * Complex.exp (2 * π * Complex.I * n * τ) := by
    intro n
    have hcoe : fourier n (τ : UnitAddCircle) =
        Complex.exp (2 * π * Complex.I * n * τ / 1) :=
      fourier_coe_apply (T := (1 : ℝ)) (n := n) (x := τ)
    simp [hcoe]
  calc
    ∑' n : ℤ, f (τ + n)
        = ∑' n : ℤ, 𝓕 f n * fourier n (τ : UnitAddCircle) := hbase
    _ = ∑' n : ℤ, 𝓕 f n *
            Complex.exp (2 * π * Complex.I * n * τ) := tsum_congr hpoint

/-- **Finite-band shifted Poisson summation under rpow decay.**

This specializes Vaaler's shifted Poisson formula to the common case where
`𝓕 f` has finite integer support.  The hypotheses are exactly those of
`shifted_poisson_summation_rpow_decay`, plus the finite-support certificate. -/
theorem shifted_poisson_summation_rpow_decay_finite_support {f : ℝ → ℂ}
    (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[Filter.cocompact ℝ] (|·| ^ (-b)))
    (hFf : (𝓕 f) =O[Filter.cocompact ℝ] (|·| ^ (-b)))
    (S : Finset ℤ) (h_support : ∀ n : ℤ, n ∉ S → 𝓕 f n = 0) (τ : ℝ) :
    ∑' n : ℤ, f (τ + n) =
      ∑ n ∈ S, 𝓕 f n *
        Complex.exp (2 * π * Complex.I * n * τ) := by
  rw [shifted_poisson_summation_rpow_decay hc hb hf hFf τ]
  exact tsum_eq_sum (s := S) (fun n hn => by
    rw [h_support n hn, zero_mul])

/-- **Finite-band shifted Poisson summation under rpow decay.**

This is the integer-band form used by Vaaler's finite Fourier coefficients:
if `𝓕 f n = 0` whenever `N < n.natAbs`, then the dual side of shifted Poisson
is the finite sum over `-N ≤ n ≤ N`. -/
theorem shifted_poisson_summation_rpow_decay_natAbs_band {f : ℝ → ℂ}
    (hc : Continuous f) {b : ℝ} (hb : 1 < b)
    (hf : f =O[Filter.cocompact ℝ] (|·| ^ (-b)))
    (hFf : (𝓕 f) =O[Filter.cocompact ℝ] (|·| ^ (-b)))
    (N : ℕ) (h_support : ∀ n : ℤ, N < n.natAbs → 𝓕 f n = 0) (τ : ℝ) :
    ∑' n : ℤ, f (τ + n) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), 𝓕 f n *
        Complex.exp (2 * π * Complex.I * n * τ) := by
  exact shifted_poisson_summation_rpow_decay_finite_support hc hb hf hFf
    (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun n hn => h_support n (Nat.lt_of_not_ge (fun hle =>
      hn ((int_mem_Icc_neg_natCast_natCast_iff_natAbs_le N n).mpr hle)))) τ

/-- **Shifted Poisson summation for Schwartz functions.**

For `f : 𝓢(ℝ, ℂ)` and every real shift `τ`,

  `∑_{n ∈ ℤ} f(τ + n) = ∑_{n ∈ ℤ} 𝓕f(n) · exp(2π i n τ)`.

This is the cleanest form for downstream consumers when the input is already
Schwartz (e.g. Gaussian-tapered cut-offs). -/
theorem shifted_poisson_summation_schwartz (f : SchwartzMap ℝ ℂ) (τ : ℝ) :
    ∑' n : ℤ, f (τ + n) =
      ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n *
        Complex.exp (2 * π * Complex.I * n * τ) := by
  have hbase := SchwartzMap.tsum_eq_tsum_fourier f τ
  have hpoint : ∀ n : ℤ,
      𝓕 (f : ℝ → ℂ) n * fourier n (τ : UnitAddCircle) =
        𝓕 (f : ℝ → ℂ) n *
          Complex.exp (2 * π * Complex.I * n * τ) := by
    intro n
    have hcoe : fourier n (τ : UnitAddCircle) =
        Complex.exp (2 * π * Complex.I * n * τ / 1) :=
      fourier_coe_apply (T := (1 : ℝ)) (n := n) (x := τ)
    simp [hcoe]
  calc
    ∑' n : ℤ, f (τ + n)
        = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n * fourier n (τ : UnitAddCircle) := hbase
    _ = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n *
            Complex.exp (2 * π * Complex.I * n * τ) := tsum_congr hpoint

/-- **Finite-band shifted Poisson summation for Schwartz functions.**

For Schwartz input, a finite integer support certificate on the Fourier
transform turns the shifted Poisson identity into an explicit finite
trigonometric polynomial. -/
theorem shifted_poisson_summation_schwartz_finite_support
    (f : SchwartzMap ℝ ℂ) (S : Finset ℤ)
    (h_support : ∀ n : ℤ, n ∉ S → 𝓕 (f : ℝ → ℂ) n = 0) (τ : ℝ) :
    ∑' n : ℤ, f (τ + n) =
      ∑ n ∈ S, 𝓕 (f : ℝ → ℂ) n *
        Complex.exp (2 * π * Complex.I * n * τ) := by
  rw [shifted_poisson_summation_schwartz f τ]
  exact tsum_eq_sum (s := S) (fun n hn => by
    rw [h_support n hn, zero_mul])

/-- **Finite-band shifted Poisson summation for Schwartz functions.**

Schwartz version of the Vaaler integer-band specialization: finite support of
`𝓕 f` in `n.natAbs ≤ N` turns shifted Poisson into a finite Fourier series over
`[-N, N]`. -/
theorem shifted_poisson_summation_schwartz_natAbs_band
    (f : SchwartzMap ℝ ℂ) (N : ℕ)
    (h_support : ∀ n : ℤ, N < n.natAbs → 𝓕 (f : ℝ → ℂ) n = 0) (τ : ℝ) :
    ∑' n : ℤ, f (τ + n) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), 𝓕 (f : ℝ → ℂ) n *
        Complex.exp (2 * π * Complex.I * n * τ) := by
  exact shifted_poisson_summation_schwartz_finite_support f
    (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun n hn => h_support n (Nat.lt_of_not_ge (fun hle =>
      hn ((int_mem_Icc_neg_natCast_natCast_iff_natAbs_le N n).mpr hle)))) τ

end MathExtras.Fourier
