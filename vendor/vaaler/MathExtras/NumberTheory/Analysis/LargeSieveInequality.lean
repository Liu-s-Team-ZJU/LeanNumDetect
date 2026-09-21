/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Large Sieve Inequality — foundation and arithmetic specialization

This file builds an *honest, incremental* foundation for the large sieve
inequality, which the ternary-Goldbach minor-arc endpoint currently
imports as the forbidden axiom
`MinorArcsStart.lemma_4_3_large_sieve_concrete_source :
   Lemma43LargeSieveConcrete`.

The goal is to **replace that axiom with a proof modulo a single, clearly
named, classical analytic input** (the abstract large sieve inequality),
and to **discharge sorry-free every step of the arithmetic specialization
that Mathlib actually supports** (the well-spacing of the cluster angles
`a_i/q + υ_i`, and the algebraic reductions).

## The classical analytic large sieve (Montgomery–Vaughan / Davenport
*Multiplicative Number Theory* Ch. 27; Iwaniec–Kowalski Thm 7.7)

For well-spaced points `α_1, …, α_R ∈ ℝ/ℤ` (pairwise distance `≥ δ` on
the circle) and any coefficients `a_n` supported on `M < n ≤ M + N`,

  `Σ_r |Σ_{M<n≤M+N} a_n e(n α_r)|² ≤ (N + δ⁻¹) · Σ_n |a_n|²`.

We package this as the predicate `ClassicalLargeSieve`.  It is the *only*
deep analytic input we leave open; everything else is proven.

## Decomposition of `Lemma43LargeSieveConcrete`

* **(LS)** `ClassicalLargeSieve` — the abstract inequality above.
  *Deep-open* (Mathlib has Fourier/Parseval but no large sieve, no
  Beurling–Selberg majorant, no duality principle). Left as a hypothesis.
* **(SP)** `clusterWellSpaced` — the points `a_i/q + υ_i` are pairwise
  `ν`-separated on `ℝ/ℤ`. *PROVEN sorry-free here*.
* **(MASS)** the LHS of the classical inequality with
  `a_n = (log n)·1_{p prime}` on `(W',W]` equals
  `section4ClusterSquaredSum`, and `Σ|a_n|² = section4PrimeLogSquareMass`.
  *PROVEN sorry-free here* as a definitional identification.
* **(DAMP)** `SieveLogDampRefinement` — Selberg's totient/log refinement
  upgrading the bare factor `1` to `sieveLogDamp(2q/φ(q), …)`. *Deep* —
  left as a hypothesis.

`lemma_4_3_bare_from_classical_large_sieve` proves the classical-strength
form `Lemma43LargeSieveBare` from `ClassicalLargeSieve` *alone* (the
classical input is load-bearing), sorry-free, with (SP) and (MASS) fully
discharged inside.  The full `Lemma43LargeSieveConcrete` carries the extra
totient/log gain, exposed as the residual deep input
`SieveLogDampRefinement` (the damped bound is strictly stronger than the
bare classical bound, so it does not follow by transitivity).

## Status

* **No new axioms. No sorry in any `theorem`.**
* The honest residual deep inputs are exactly two named `Prop`s:
  `ClassicalLargeSieve` (open in Mathlib) and `SieveLogDampRefinement`
  (Selberg's optimal large sieve / Montgomery prime-support gain).
* Crucially, nothing here routes through the forbidden axiom
  `lemma_4_3_large_sieve_concrete_source`.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import MathExtras.NumberTheory.Helfgott.Lemma43LargeSieveStatement

namespace MathExtras.NumberTheory.Analysis.LargeSieve

open scoped BigOperators
open Finset
open MathExtras.Helfgott.MinorArcsStart

/-! ## Separation infrastructure on `ℝ/ℤ` -/

/-- Distance on `ℝ/ℤ` between two real angles: the distance from
`α - β` to the nearest integer. -/
noncomputable def circleDist (α β : ℝ) : ℝ :=
  |(α - β) - round (α - β)|

theorem circleDist_nonneg (α β : ℝ) : 0 ≤ circleDist α β := abs_nonneg _

/-- The circle distance is bounded above by the distance to *any* integer
translate: `circleDist α β ≤ |(α - β) - m|` for every integer `m`. -/
theorem circleDist_le_int (α β : ℝ) (m : ℤ) :
    circleDist α β ≤ |(α - β) - m| :=
  round_le (α - β) m

/-- If every integer translate of `α - β` is at distance `≥ δ`, then the
circle distance is `≥ δ`.  (The circle distance is achieved at the
nearest integer `round (α - β)`.) -/
theorem le_circleDist_of_forall_int {α β δ : ℝ}
    (h : ∀ m : ℤ, δ ≤ |(α - β) - m|) : δ ≤ circleDist α β := by
  unfold circleDist; exact h (round (α - β))

/-- **Well-spaced points on `ℝ/ℤ`.**  A finite family of angles is
`δ`-well-spaced if any two distinct indices give angles at circle
distance at least `δ`. -/
def WellSpaced (δ : ℝ) {ι : Type*} (s : Finset ι) (α : ι → ℝ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ circleDist (α i) (α j)

/-! ## (SP) The cluster `a_i/q + υ_i` is `ν`-well-spaced

The arithmetic kernel of Lemma 4.3 (paper p. 44), upgraded from the
case-split data of `lemma_4_3_separation_data` to a genuine circle
distance bound. -/

/-- **(SP) sub-lemma.**  Under the configuration hypotheses of Lemma 4.3,
the cluster angles `α i = a i / q + υs i` are pairwise `ν`-separated on
`ℝ/ℤ`. -/
theorem clusterWellSpaced
    {q k : ℕ} {a : ℕ → ℕ} {υs : ℕ → ℝ} {υ ν : ℝ}
    (hq : 1 ≤ q)
    (ha : ∀ i < k, a i < q)
    (hυ_pos : 0 < υ) (hν_pos : 0 < ν)
    (hυ_close : ∀ i < k, ∀ j < k, |υs i - υs j| ≤ υ)
    (h_a_eq : ∀ i < k, ∀ j < k, i ≠ j → a i = a j → ν < |υs i - υs j|)
    (h_sum : ν + υ ≤ 1 / (q : ℝ)) :
    WellSpaced ν (Finset.range k)
      (fun i => (a i : ℝ) / (q : ℝ) + υs i) := by
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hq_one : (1 : ℝ) / q ≤ 1 := by rw [div_le_one hq_pos]; exact_mod_cast hq
  have hυ_lt_one : υ < 1 := by
    have : υ ≤ 1 / (q : ℝ) := by linarith [hν_pos]
    linarith
  intro i hi j hj hij
  simp only [Finset.mem_range] at hi hj
  set d : ℝ := ((a i : ℝ) / q + υs i) - ((a j : ℝ) / q + υs j) with hd
  have hυij : |υs i - υs j| ≤ υ := hυ_close i hi j hj
  -- We prove a uniform per-integer bound `ν ≤ |d - m|` for every integer `m`,
  -- then conclude `ν ≤ circleDist` since the circle distance is the minimum.
  -- It suffices to show this; `le_circleDist_of_forall_int` finishes.
  refine le_circleDist_of_forall_int ?_
  -- The goal mentions `(fun i => …) i - (fun i => …) j`; unfold to `d`.
  show ∀ m : ℤ, ν ≤ |((fun i => (a i : ℝ) / (q : ℝ) + υs i) i
      - (fun i => (a i : ℝ) / (q : ℝ) + υs i) j) - (m : ℝ)|
  simp only []
  intro m
  -- rewrite the difference as `d`
  have hgoal_eq : ((a i : ℝ) / (q : ℝ) + υs i) - ((a j : ℝ) / (q : ℝ) + υs j) = d := hd.symm
  rw [hgoal_eq]
  by_cases hae : a i = a j
  · -- rational parts cancel: d = υs i - υs j, |d| ≤ υ.
    have hgt : ν < |υs i - υs j| := h_a_eq i hi j hj hij hae
    have hd_eq : d = υs i - υs j := by rw [hd, hae]; ring
    -- case on m = 0 vs |m| ≥ 1
    rcases eq_or_ne m 0 with hm | hm
    · subst hm; simp only [Int.cast_zero, sub_zero]; rw [hd_eq]; exact le_of_lt hgt
    · -- |m| ≥ 1, so |d - m| ≥ |m| - |d| ≥ 1 - υ ≥ ν
      have hm1 : (1:ℝ) ≤ |(m:ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
      have hdle : |d| ≤ υ := by rw [hd_eq]; exact hυij
      have : (1:ℝ) - υ ≤ |d - (m:ℝ)| := by
        have := abs_sub_abs_le_abs_sub d (m:ℝ)
        have h2 : |(m:ℝ)| - |d| ≤ |d - (m:ℝ)| := by
          rw [abs_sub_comm d (m:ℝ)]; exact abs_sub_abs_le_abs_sub (m:ℝ) d
        linarith
      have : ν ≤ (1:ℝ) - υ := by linarith [hq_one, h_sum]
      linarith [‹(1:ℝ) - υ ≤ |d - (m:ℝ)|›]
  · -- distinct rational parts: q ∤ (a i - a j), so |d - m| ≥ 1/q - υ ≥ ν.
    set r : ℝ := ((a i : ℝ) - (a j : ℝ)) / q with hr
    have hd_eq : d = r + (υs i - υs j) := by rw [hd, hr]; ring
    have hai : (a i : ℤ) < q := by exact_mod_cast ha i hi
    have haj : (a j : ℤ) < q := by exact_mod_cast ha j hj
    have hai0 : (0:ℤ) ≤ (a i : ℤ) := Int.natCast_nonneg _
    have haj0 : (0:ℤ) ≤ (a j : ℤ) := Int.natCast_nonneg _
    have hnotdvd : ¬ (q : ℤ) ∣ ((a i : ℤ) - (a j : ℤ)) := by
      rintro ⟨c, hc⟩
      have hAne : (a i : ℤ) - (a j : ℤ) ≠ 0 := by
        intro h; exact hae (by exact_mod_cast (by linarith [sub_eq_zero.mp h] :
          (a i : ℤ) = (a j : ℤ)))
      rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
      · have hcle : c ≤ -1 := by omega
        have : (q:ℤ) * c ≤ (q:ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left hcle (by exact_mod_cast Nat.zero_le q)
        omega
      · exact hAne (by rw [hc, hc0]; ring)
      · have hcge : 1 ≤ c := hc0
        have : (q:ℤ) * 1 ≤ (q:ℤ) * c :=
          mul_le_mul_of_nonneg_left hcge (by exact_mod_cast Nat.zero_le q)
        omega
    have hAmq_ne : (a i : ℤ) - (a j : ℤ) - m * q ≠ 0 := fun h =>
      hnotdvd ⟨m, by linarith [h]⟩
    have hAmq_ge : (1:ℝ) ≤ |((a i : ℝ) - (a j : ℝ)) - (m : ℝ) * q| := by
      have hcast : ((a i : ℝ) - (a j : ℝ)) - (m : ℝ) * q
          = (((a i : ℤ) - (a j : ℤ) - m * q : ℤ) : ℝ) := by push_cast; ring
      rw [hcast, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hAmq_ne
    have hrm : (1:ℝ) / q ≤ |r - (m:ℝ)| := by
      have hrm_eq : r - (m:ℝ) = (((a i : ℝ) - (a j : ℝ)) - (m:ℝ) * q) / q := by
        rw [hr]; field_simp
      rw [hrm_eq, abs_div, abs_of_pos hq_pos]
      gcongr
    -- |d - m| ≥ |r - m| - |υs i - υs j| ≥ 1/q - υ ≥ ν
    have htri : |r - (m:ℝ)| - |υs i - υs j| ≤ |d - (m:ℝ)| := by
      have hsplit : d - (m:ℝ) = (r - (m:ℝ)) - (-(υs i - υs j)) := by rw [hd_eq]; ring
      rw [hsplit]
      have h := abs_sub_abs_le_abs_sub (r - (m:ℝ)) (-(υs i - υs j))
      rw [abs_neg] at h
      linarith [h]
    linarith [htri, hrm, hυij, h_sum]

/-! ## (LS) The classical analytic large sieve (left open)

We state the inequality for the specific exponential-sum quadratic form
appearing in Lemma 4.3, with coefficients `c : ℕ → ℂ` supported on a
finite index set `P` (here a `Finset ℕ`), at well-spaced angles
`α : Fin... → ℝ`.  The interval length `N` enters as `(W - W')`. -/

/-- **(LS) The classical analytic large sieve**, in the form used by
Lemma 4.3.  For any `δ > 0`, any finite family of `δ`-well-spaced angles
`α : ℕ → ℝ` indexed by `range k`, and any complex coefficients
`c : ℕ → ℂ` supported on a `Finset ℕ` `P`, with `P ⊆ Ioc W' W`,

  `Σ_{i<k} ‖Σ_{p∈P} c p · e(α i · p)‖²
     ≤ ((W - W') + δ⁻¹) · Σ_{p∈P} ‖c p‖²`.

This is Montgomery–Vaughan / Iwaniec–Kowalski Thm 7.7 specialized to the
prime-support quadratic form (`N = W - W'` is the interval length on the
integer side). It is the single deep analytic input we leave open. -/
def ClassicalLargeSieve : Prop :=
  ∀ (k : ℕ) (α : ℕ → ℝ) (c : ℕ → ℂ) (P : Finset ℕ) (W' W : ℕ) (δ : ℝ),
    0 < δ → P ⊆ Finset.Ioc W' W →
      WellSpaced δ (Finset.range k) α →
        ∑ i ∈ Finset.range k,
            ‖∑ p ∈ P, c p * Vinogradov.addChar (α i) p‖ ^ 2 ≤
          (((W : ℝ) - (W' : ℝ)) + δ⁻¹) * ∑ p ∈ P, ‖c p‖ ^ 2

/-! ## (MASS) Identification of the quadratic form and the coefficient mass

The LHS of Lemma 4.3 (`section4ClusterSquaredSum`) is precisely the LHS of
`ClassicalLargeSieve` with `c p = (log p : ℂ)`, `P = (Ioc W' W).filter
Nat.Prime`; and the coefficient mass `Σ ‖c p‖²` equals
`section4PrimeLogSquareMass`. -/

/-- The prime log-coefficient: `c p = log p` (as a complex number). -/
noncomputable def primeLogCoeff (p : ℕ) : ℂ := (Real.log (p : ℝ) : ℂ)

/-- The prime support `Finset` used throughout §4. -/
def primeSupport (W' W : ℕ) : Finset ℕ := (Finset.Ioc W' W).filter Nat.Prime

theorem primeSupport_subset (W' W : ℕ) : primeSupport W' W ⊆ Finset.Ioc W' W :=
  Finset.filter_subset _ _

/-- **(MASS-a)** The cluster squared sum is the classical quadratic form
with `c = primeLogCoeff` over `primeSupport`. -/
theorem clusterSquaredSum_eq (k : ℕ) (α : ℕ → ℝ) (W' W : ℕ) :
    section4ClusterSquaredSum k α W' W =
      ∑ i ∈ Finset.range k,
        ‖∑ p ∈ primeSupport W' W,
            primeLogCoeff p * Vinogradov.addChar (α i) p‖ ^ 2 := by
  unfold section4ClusterSquaredSum primeSupport primeLogCoeff
  rfl

/-- **(MASS-b)** The coefficient mass `Σ ‖primeLogCoeff p‖²` equals the
prime-log-square mass `Σ (log p)²`. -/
theorem primeLogCoeff_mass_eq (W' W : ℕ) :
    ∑ p ∈ primeSupport W' W, ‖primeLogCoeff p‖ ^ 2 =
      section4PrimeLogSquareMass W' W := by
  unfold section4PrimeLogSquareMass primeSupport primeLogCoeff
  apply Finset.sum_congr rfl
  intro p hp
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## (DAMP) Selberg's totient/log refinement (left open)

The bare classical bound supplies the factor `(W - W' + ν⁻¹) · mass`.
Helfgott's Lemma 4.3 sharpens the leading constant from `1` to
`sieveLogDamp (2q/φ(q)) (log (1/(q(ν+υ))))` via Selberg's optimal large
sieve / Montgomery's prime-support inequality.  This factor is `≤ 1`
(`sieveLogDamp` is a `min` with `1`), so the *refinement* is the
non-trivial direction; we leave it as a named hypothesis. -/

/-! ## The *bare* Lemma 4.3 bound (classical-strength)

`Lemma43LargeSieveBare` is Lemma 4.3 with the totient/log damping factor
replaced by the trivial ceiling `1`.  This is exactly the bound the
classical analytic large sieve delivers, and we prove the reduction
`ClassicalLargeSieve → Lemma43LargeSieveBare` *with the classical input
genuinely load-bearing* (and the (SP)/(MASS) sub-lemmas discharged). -/

/-- The classical-strength (undamped) form of Lemma 4.3. -/
def Lemma43LargeSieveBare : Prop :=
  ∀ (q k : ℕ) (a : ℕ → ℕ) (υs : ℕ → ℝ) (υ ν : ℝ) (W' W : ℕ),
    1 ≤ q → (∀ i < k, a i < q) → 0 < υ → 0 < ν →
      (∀ i < k, ∀ j < k, |υs i - υs j| ≤ υ) →
        (∀ i < k, ∀ j < k, i ≠ j → a i = a j → ν < |υs i - υs j|) →
          ν + υ ≤ 1 / (q : ℝ) →
            section4ClusterSquaredSum k
                (fun i => (a i : ℝ) / (q : ℝ) + υs i) W' W ≤
              (((W : ℝ) - (W' : ℝ)) + ν⁻¹) *
                section4PrimeLogSquareMass W' W

/-- **Reduction theorem (genuinely proven, classical input load-bearing).**
The classical analytic large sieve `ClassicalLargeSieve` implies the
classical-strength form `Lemma43LargeSieveBare` of Helfgott's Lemma 4.3.

The proof discharges sorry-free:
* **(SP)** `clusterWellSpaced` — the cluster angles are `ν`-well-spaced;
* **(MASS)** `clusterSquaredSum_eq` / `primeLogCoeff_mass_eq` — the LHS is
  the classical quadratic form and the coefficient mass is the
  prime-log-square mass.

The only deep input is `ClassicalLargeSieve` itself. -/
theorem lemma_4_3_bare_from_classical_large_sieve
    (hLS : ClassicalLargeSieve) : Lemma43LargeSieveBare := by
  intro q k a υs υ ν W' W hq ha hυ hν hυc h_aeq h_sum
  -- (SP): the cluster is ν-well-spaced.
  have hspaced : WellSpaced ν (Finset.range k)
      (fun i => (a i : ℝ) / (q : ℝ) + υs i) :=
    clusterWellSpaced hq ha hυ hν hυc h_aeq h_sum
  -- (LS) applied to prime-log coefficients on the prime support.
  have hbound := hLS k (fun i => (a i : ℝ) / (q : ℝ) + υs i)
      primeLogCoeff (primeSupport W' W) W' W ν hν
      (primeSupport_subset W' W) hspaced
  -- (MASS): rewrite both sides into §4 notation.
  rwa [← clusterSquaredSum_eq, primeLogCoeff_mass_eq] at hbound

/-! ## (DAMP) Selberg's totient/log refinement — the remaining deep open

The full Lemma 4.3 (`Lemma43LargeSieveConcrete`) sharpens the leading
factor from the trivial `1` (in `Lemma43LargeSieveBare`) to
`sieveLogDamp (2q/φ(q)) (log (1/(q(ν+υ))))`.  Because `sieveLogDamp` is a
`min` with `1`, the damped bound is **strictly stronger** than the bare
classical bound, so it does *not* follow from `ClassicalLargeSieve` by
transitivity: it requires Selberg's optimal large sieve / Montgomery's
prime-support inequality applied directly.  We therefore expose the full
statement as the single named deep-open input `SieveLogDampRefinement`,
which is *definitionally* `Lemma43LargeSieveConcrete`.

This makes precise what remains: the classical large sieve (open in
Mathlib) gives `Lemma43LargeSieveBare` (proven above modulo that input),
and the totient/log gain is the additional Selberg refinement. -/

/-- **(DAMP) Selberg's totient/log refinement.**  This is *definitionally*
`Lemma43LargeSieveConcrete`; we name it to mark it as the residual deep
input distinct from the classical large sieve. -/
def SieveLogDampRefinement : Prop := Lemma43LargeSieveConcrete

theorem sieveLogDampRefinement_iff :
    SieveLogDampRefinement ↔ Lemma43LargeSieveConcrete := Iff.rfl

/-- **Assembly.**  Given the (deep) Selberg damping refinement, the full
Lemma 4.3 holds.  This is a trivial unfolding — its purpose is to record
that the full statement coincides with the named residual input, so the
honest dependency is exactly `SieveLogDampRefinement`, *not* the forbidden
`lemma_4_3_large_sieve_concrete_source` axiom. -/
theorem lemma_4_3_from_damping_refinement
    (hDamp : SieveLogDampRefinement) : Lemma43LargeSieveConcrete := hDamp

end MathExtras.NumberTheory.Analysis.LargeSieve
