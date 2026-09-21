/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharp large sieve: scoping the dilated minor-arc residual (Track S)

This file scopes the SHARP large-sieve content that the dilated minor-arc
Type-II residual `DilatedLargeSieveOnMinorTruncated` requires, following
Helfgott, *Minor arcs for Goldbach's problem* (arXiv:1205.5252v4), §4.2
("The sum `S₂`: the large sieve, primes and tails"), and discharges its
*most reachable* arithmetic atom sorry-free.

## The §4.2 mechanism (research verdict)

Helfgott's minor-arc bilinear ℓ²-mass is the sum

  `S₂(U',W',W) = ∑_{U'<m≤x/W} |∑_{W'<p≤W} (log p) e(α m p)|²`            (4.37)

with `α = a/q + δ/x`, `gcd(a,q)=1`, `q ≤ Q = (3/4)x^{2/3}`, `|δ/x| ≤ 1/qQ`.
This is bounded by the **SHARP large sieve `N + δ⁻¹`** — explicitly *"the
optimal `N + δ⁻¹ − 1` form due to Selberg and Montgomery–Vaughan"* (proof of
Lemma 4.3, eq. (4.38)); it is NOT the soft mean-value / Gallagher form (which
gives only `K = 1`, no saving).

The saving comes from **Farey/Vinogradov well-spacing of the dilated
frequencies**, NOT from the large-sieve constant alone:

* Split the `m`-range `(A₀,A₁]` into blocks of `k = min(q, ⌈Q/2⌉)` consecutive
  integers (Lemma 4.4 proof, eq. (4.44); odd analogue Lemma 4.5, (4.57)).
* Within a block, for `m ≠ m'` the scaled angles `α m, α m'` are separated on
  `ℝ/ℤ` by `≥ 1/q − O*(k/qQ) = 1/q − O*(1/2q) ≥ 1/2q` (the `O*(1/2q)` is the
  `δ`-displacement; here `qR² < Q`).  So the well-spacing parameter is
  `δ_spacing = 1/2q`, hence the sharp term `δ_spacing⁻¹ = 2q`.
* Apply the sharp sieve per block: each block of length `≤ k ≤ ⌈Q/2⌉` gives
  `≤ ((W−W') + 2q)·∑(log p)²`, and there are `⌈(A₁−A₀)/k⌉` blocks, yielding
  the per-`d`/per-`m` bound (4.41)
  `S₂ ≤ ⌈(A₁−A₀)/min(q,⌈Q/2⌉)⌉ · (W−W'+2q) · ∑(log p)²`.

The decisive `q`-weight is therefore the `δ⁻¹ = 2q` term, made available by the
**block well-spacing `1/2q`** — which itself rests on the purely arithmetic
fact that `α m − α m' = (a/q)(m − m') + δ(m−m')/x` lands at circle distance
`≥ 1/q − (displacement)` because, for `q ∤ (m−m')` and `gcd(a,q)=1`, the
rational part `a(m−m')/q` is at circle distance `≥ 1/q` from `0`.

The further `φ(q)/q` and `1/log` gains ((4.42), (4.53), via Montgomery's
inequality + the Montgomery–Vaughan weighted sieve, eqs. (4.45)–(4.48)) are what
ultimately push the constant below the trivial `x/(2 log x)` and supply the
`K_dil = O((log)^{-A})` decay; they are a *separate, deeper* layer (the
`SieveLogDampRefinement` residual already named in `LargeSieveInequality.lean`).

## What this file delivers (sorry-free, axiom-clean)

The arithmetic atom underlying the block well-spacing: the **rational
circle-distance separation**

  `gcd(a,q)=1`, `q ∤ (m−m')`  ⟹  `circleDist (a m / q) (a m' / q) ≥ 1/q`.

This is the engine of eqs. (4.44)/(4.57): it is exactly why the `δ⁻¹` term in
the sharp sieve scales as `q` (not `1`), i.e. why the saving carries the
`q`-weight.  We prove it via the existing `circleDist` / `WellSpaced`
infrastructure of `LargeSieveInequality.lean`, and package the block-spacing
corollary `dilatedBlockWellSpaced`: an entire block of consecutive `m`'s
(width `≤ q`) of dilated frequencies is `1/q`-well-spaced.

No new `axiom`, no `sorry`, no `False.elim`/vacuous proof.  Nothing routes
through any DUBIOUS bridge.
-/

import MathExtras.NumberTheory.Analysis.LargeSieveInequality

namespace MathExtras.NumberTheory.Analysis.SharpLargeSieve

open scoped BigOperators
open Finset
open MathExtras.NumberTheory.Analysis.LargeSieve

/-! ## The rational circle-distance separation (the `q`-weight engine)

The arithmetic core of Helfgott's eq. (4.44)/(4.57).  For the *exact* rational
angle `a/q` (the `δ = 0` skeleton), distinct `m, m'` whose difference is not a
multiple of `q` give scaled angles `a m/q, a m'/q` at circle distance `≥ 1/q`.
-/

/-- **Coprime non-divisibility transfer.**  If `gcd(a,q) = 1` and `q ∤ t`, then
`q ∤ a·t`.  (The `a`-factor cannot supply the missing `q`-divisibility.)  This is
the step that makes the *rational* part of the dilated frequency non-trivial mod
`q`. -/
theorem not_dvd_mul_of_coprime {a q t : ℤ} (hcop : IsCoprime a q)
    (hndvd : ¬ (q ∣ t)) : ¬ (q ∣ a * t) := fun h =>
  hndvd (hcop.symm.dvd_of_dvd_mul_left h)

/-- **(Helfgott (4.44)/(4.57) atom) Rational circle-distance separation.**

Let `q ≥ 1`, `gcd(a, q) = 1` (as integers).  If `m ≠ m'` are integers with
`q ∤ (m − m')` (in particular, any two distinct `m, m'` in a block of `< q + 1`
consecutive integers, since then `0 < |m − m'| < q`), then the scaled rational
angles `a m / q` and `a m' / q` are separated on `ℝ/ℤ` by at least `1/q`:

  `circleDist (a m / q) (a m' / q) ≥ 1 / q`.

This is the engine of the sharp `(N + δ⁻¹)` large sieve's `q`-weight: it forces
`δ_spacing ≥ 1/q` for the *exact* Farey angle, so `δ_spacing⁻¹ ≤ q`.  The
`δ`-displacement of Helfgott (the `O*(1/2q)` in (4.44)) only relaxes this to
`1/2q`; the rational skeleton proven here is what carries the weight. -/
theorem rationalDilatedSeparation
    {a q : ℤ} {m m' : ℤ}
    (hq : 1 ≤ q) (hcop : IsCoprime a q) (hndvd : ¬ (q ∣ (m - m'))) :
    (1 : ℝ) / (q : ℝ) ≤ circleDist ((a : ℝ) * (m : ℝ) / (q : ℝ))
      ((a : ℝ) * (m' : ℝ) / (q : ℝ)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le one_pos hq)
  -- `q ∤ a·(m − m')`.
  have hndvd' : ¬ (q ∣ a * (m - m')) := not_dvd_mul_of_coprime hcop hndvd
  -- The numerator `a·(m − m') − k·q` is a nonzero integer for every `k`,
  -- hence has absolute value `≥ 1`; dividing by `q` gives the `1/q` separation.
  refine le_circleDist_of_forall_int (fun k => ?_)
  -- Rewrite the difference of scaled angles as `(a·(m − m')) / q`.
  have hdiff_eq :
      ((a : ℝ) * (m : ℝ) / (q : ℝ)) - ((a : ℝ) * (m' : ℝ) / (q : ℝ))
        = ((a : ℝ) * ((m : ℝ) - (m' : ℝ))) / (q : ℝ) := by
    rw [mul_sub, sub_div]
  rw [hdiff_eq]
  -- The integer `a·(m − m') − k·q` is nonzero.
  have hnum_ne : a * (m - m') - k * q ≠ 0 := by
    intro h
    exact hndvd' ⟨k, by linarith [h]⟩
  -- So its real absolute value is `≥ 1`.
  have habs1 : (1 : ℝ) ≤ |((a * (m - m') - k * q : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hnum_ne
  -- Identify `(a·(m−m')/q − k)` with `(a·(m−m') − k·q)/q`.
  have hgoal_eq :
      ((a : ℝ) * ((m : ℝ) - (m' : ℝ))) / (q : ℝ) - (k : ℝ)
        = (((a * (m - m') - k * q : ℤ)) : ℝ) / (q : ℝ) := by
    rw [eq_div_iff (ne_of_gt hq_pos)]
    push_cast
    field_simp
  rw [hgoal_eq, abs_div, abs_of_pos hq_pos]
  -- Goal: `1/q ≤ |num| / q`; follows from `1 ≤ |num|` since `q > 0`.
  gcongr

/-! ## Block well-spacing corollary

Helfgott's blocks (4.44): take a window `[m₀ + 1, m₀ + k]` of `k ≤ q` consecutive
integers.  Any two distinct members differ by a nonzero amount `< q`, hence are
not divisible by `q`, so the dilated frequencies are `1/q`-well-spaced. -/

/-- **(Helfgott (4.44) block).**  For `q ≥ 1`, `gcd(a, q) = 1`, and a base index
`m₀`, the family of dilated frequencies `i ↦ a·(m₀ + i)/q` over a block
`i ∈ range k` of width `k ≤ q` is `1/q`-well-spaced on `ℝ/ℤ`.

This is the precise hypothesis the *sharp* large sieve consumes per block: a
`(1/q)`-well-spaced family of size `≤ k`, fed into `ClassicalLargeSieve` with
`δ = 1/q`, yielding the `(N + q)` block bound (the `q`-weighted `δ⁻¹` term of
eqs. (4.41)/(4.44)). -/
theorem dilatedBlockWellSpaced
    {a q : ℤ} (m₀ : ℤ) {k : ℕ}
    (hq : 1 ≤ q) (hcop : IsCoprime a q) (hk : (k : ℤ) ≤ q) :
    WellSpaced ((1 : ℝ) / (q : ℝ)) (Finset.range k)
      (fun i => (a : ℝ) * ((m₀ : ℝ) + (i : ℝ)) / (q : ℝ)) := by
  intro i hi j hj hij
  simp only [Finset.mem_range] at hi hj
  -- The two block members `m = m₀ + i`, `m' = m₀ + j`.
  set m : ℤ := m₀ + (i : ℤ) with hm
  set m' : ℤ := m₀ + (j : ℤ) with hm'
  -- `m − m' = i − j`, nonzero and of absolute value `< q`, so `q ∤ (m − m')`.
  have hmm' : m - m' = (i : ℤ) - (j : ℤ) := by rw [hm, hm']; ring
  have hij_ne : (i : ℤ) - (j : ℤ) ≠ 0 := by
    intro h
    exact hij (by exact_mod_cast (sub_eq_zero.mp h))
  have habs_lt : |(i : ℤ) - (j : ℤ)| < q := by
    have hi' : (i : ℤ) < q := lt_of_lt_of_le (by exact_mod_cast hi) hk
    have hj' : (j : ℤ) < q := lt_of_lt_of_le (by exact_mod_cast hj) hk
    have hi0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    rw [abs_lt]; constructor <;> omega
  have hndvd : ¬ (q ∣ (m - m')) := by
    rw [hmm']
    intro hdvd
    have habs_ge : q ≤ |(i : ℤ) - (j : ℤ)| :=
      Int.le_of_dvd (abs_pos.mpr hij_ne) ((dvd_abs _ _).mpr hdvd)
    exact absurd habs_ge (not_le.mpr habs_lt)
  -- Apply the rational separation; rewrite the scaled angles to match.
  have hsep := rationalDilatedSeparation (a := a) (q := q) (m := m) (m' := m') hq hcop hndvd
  -- `a·m/q` with `m = m₀ + i` equals `a·(m₀ + i)/q`.
  have hcast_m : (a : ℝ) * (m : ℝ) / (q : ℝ)
      = (a : ℝ) * ((m₀ : ℝ) + (i : ℝ)) / (q : ℝ) := by
    rw [hm]; push_cast; ring
  have hcast_m' : (a : ℝ) * (m' : ℝ) / (q : ℝ)
      = (a : ℝ) * ((m₀ : ℝ) + (j : ℝ)) / (q : ℝ) := by
    rw [hm']; push_cast; ring
  rw [hcast_m, hcast_m'] at hsep
  simpa using hsep

/-! ## Sanity: the separation degenerates exactly when expected

A degenerate check confirming the lemma is non-vacuous: distinct same-block
indices `i ≠ j` (width `≤ q`) genuinely satisfy `q ∤ (m − m')`, so the family is
honestly `1/q`-separated (not separated by the trivial `0`).  We record the
`q = 1` boundary as a non-example marker: with `q = 1` a block has width `≤ 1`,
so `range k` has at most one index and `WellSpaced` is vacuously true — matching
the fact that there is no minor-arc saving at `q = 1` (the major-arc regime). -/

/-- With `q = 1`, the block has width `≤ 1`, so at most one index participates and
the well-spacing predicate is vacuous — the honest reflection of "no large-sieve
saving on the `q = 1` (major) arc". -/
theorem dilatedBlockWellSpaced_q_one_vacuous
    {a : ℤ} (m₀ : ℤ) {k : ℕ} (hk : (k : ℤ) ≤ 1) :
    WellSpaced ((1 : ℝ) / (1 : ℝ)) (Finset.range k)
      (fun i => (a : ℝ) * ((m₀ : ℝ) + (i : ℝ)) / (1 : ℝ)) := by
  intro i hi j hj hij
  simp only [Finset.mem_range] at hi hj
  -- `k ≤ 1` forces `i = j = 0`, contradicting `i ≠ j`.
  have hi1 : i = 0 := by omega
  have hj1 : j = 0 := by omega
  exact absurd (hi1.trans hj1.symm) hij

#print axioms rationalDilatedSeparation
#print axioms dilatedBlockWellSpaced
#print axioms not_dvd_mul_of_coprime

end MathExtras.NumberTheory.Analysis.SharpLargeSieve
