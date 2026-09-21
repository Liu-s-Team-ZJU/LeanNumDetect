/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import MathExtras.NumberTheory.Vinogradov.CircleMethod

/-!
# Helfgott Lemma 4.3 — minimal statement layer

This module isolates the four finite-sum declarations used to state the
concrete large-sieve estimate (4.38).  Keeping the statement layer independent
of the full minor-arcs source map prevents large-sieve foundations from
importing the entire downstream minor-arc proof graph.
-/

noncomputable section

namespace MathExtras.Helfgott.MinorArcsStart

open scoped BigOperators

/-- The prime mass `Σ_{W' < p ≤ W} (log p)²` appearing on the right of every
large-sieve display (4.38)--(4.56). -/
noncomputable def section4PrimeLogSquareMass (W' W : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc W' W).filter Nat.Prime, Real.log (p : ℝ) ^ 2

/-- Damping factor `min(1, c/L)` with the paper's `L → 0⁺` convention.

In displays (4.38) and (4.55) the factor is `min(1, c / log Z)` where the
hypotheses only guarantee `log Z ≥ 0`; at `log Z = 0` the paper reads
`c/0 = +∞`, so the `min` picks `1`.  Lean's total division would instead
give `c/0 = 0` and falsify the bound, so the transcriptions below route
through this guard (same pattern as `MinorSection51Pieces.deltaDamp`). -/
noncomputable def sieveLogDamp (c L : ℝ) : ℝ :=
  if L ≤ 0 then 1 else min 1 (c / L)

/-- Left side of (4.38): the squared prime-support exponential sums summed
over the cluster of angles `α_0, …, α_{k-1}`. -/
noncomputable def section4ClusterSquaredSum
    (k : ℕ) (α : ℕ → ℝ) (W' W : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k,
    ‖∑ p ∈ (Finset.Ioc W' W).filter Nat.Prime,
        (Real.log (p : ℝ) : ℂ) * Vinogradov.addChar (α i) p‖ ^ 2

/-- Concrete statement of Lemma 4.3, equation (4.38): for angles
`α_i = a_i/q + υ_i` with `0 ≤ a_i < q`, the `υ_i` lying in an interval of
length `υ` (transcribed as pairwise `|υ_i - υ_j| ≤ υ`, an equivalent
condition for reals), `a_i = a_j (i ≠ j)` forcing `|υ_i - υ_j| > ν`, and
`ν + υ ≤ 1/q`, one has

`Σ_i |Σ_{W'<p≤W} (log p) e(α_i p)|² ≤
  min(1, (2q/φ(q)) / log((q(ν+υ))⁻¹)) · (W - W' + ν⁻¹) · Σ_{W'<p≤W} (log p)²`.

Source: arXiv:1205.5252v4, Lemma 4.3, eq. (4.38), pp. 44--45. -/
def Lemma43LargeSieveConcrete : Prop :=
  ∀ (q k : ℕ) (a : ℕ → ℕ) (υs : ℕ → ℝ) (υ ν : ℝ) (W' W : ℕ),
    1 ≤ q → (∀ i < k, a i < q) →
      0 < υ → 0 < ν →
        (∀ i < k, ∀ j < k, |υs i - υs j| ≤ υ) →
          (∀ i < k, ∀ j < k, i ≠ j → a i = a j → ν < |υs i - υs j|) →
            ν + υ ≤ 1 / (q : ℝ) →
              1 ≤ W → 1 ≤ W' → (W : ℝ) / 2 ≤ (W' : ℝ) →
                (8 : ℝ) * Real.exp 0.50136 ≤ (W : ℝ) / (q : ℝ) →
                1 / Real.sqrt ((ν + υ) * (q : ℝ)) < (W' : ℝ) →
                section4ClusterSquaredSum k
                    (fun i => (a i : ℝ) / (q : ℝ) + υs i) W' W ≤
                  sieveLogDamp (2 * (q : ℝ) / (Nat.totient q : ℝ))
                      (Real.log (1 / ((q : ℝ) * (ν + υ)))) *
                    (((W : ℝ) - (W' : ℝ)) + ν⁻¹) *
                    section4PrimeLogSquareMass W' W

end MathExtras.Helfgott.MinorArcsStart
