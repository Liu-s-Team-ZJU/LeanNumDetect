/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sharp large sieve: block accumulation (Helfgott eq. 4.41) — Track S

This file performs Helfgott's **block-accumulation reduction** of the dilated
minor-arc large-sieve mass to the SHARP `(N + δ⁻¹)` large sieve applied per
well-spaced block (Helfgott, *Minor arcs for Goldbach's problem*,
arXiv:1205.5252v4, §4.2, eqs. (4.41)/(4.44)/(4.57)).

## The mechanism (eq. 4.41)

The minor-arc bilinear ℓ²-mass over an `m`-range is
`S₂ = ∑_{m ∈ (A₀,A₁]} |∑_p c_p e(α m p)|²`.  The decisive step is:

1. Split the `m`-range into **blocks of `k` consecutive integers** (`k =
   min(q, ⌈Q/2⌉)`).
2. Within a block the dilated frequencies `m ↦ a m / q` are `1/q`-well-spaced
   (the proven `SharpLargeSieve.dilatedBlockWellSpaced`, since a width-`≤ q`
   window of consecutive `m` has `q ∤ (m−m')`).
3. Apply the **SHARP** large sieve per block — the optimal `(N + δ⁻¹)` form
   (Selberg / Montgomery–Vaughan), here with `N = W − W'` and `δ⁻¹ = q` — to
   get a per-block bound `((W−W') + q)·∑‖c_p‖²`.
4. Sum over the `⌈range/k⌉` blocks:
   `S₂ ≤ ⌈range/k⌉ · ((W−W') + q) · ∑‖c_p‖²`.

## What this file delivers

* **`SharpLargeSievePerBlock`** — the named `Prop` for the *single-block* sharp
  large sieve `∑_{i ∈ B} ‖∑_p c_p e(α_i p)‖² ≤ ((W−W') + δ⁻¹)·∑‖c_p‖²` for a
  `δ`-well-spaced finite family `α`.  This is the from-scratch core
  (Beurling–Selberg majorant / duality); it is the SHARP constant, strictly
  stronger than the SOFT `π(W−W')+δ⁻¹` Gallagher form.  **Left as the named
  residual.**  (It is the per-block analogue of `LargeSieve.ClassicalLargeSieve`,
  named separately to mark it as the single from-scratch atom the block
  accumulation reduces to.)

* **`blockSum_le_of_perBlock`** — *proven sorry-free*: the abstract block
  accumulation over a general `δ`-well-spaced family on `range M`.  Partition
  `range M` into `⌈M/k⌉` consecutive blocks (fibers of `i ↦ i / k`), each
  well-spaced (supplied per block), apply the per-block sharp sieve to each, and
  sum.  Yields `∑_{i<M} ‖…‖² ≤ ⌈M/k⌉ · ((W−W') + δ⁻¹) · ∑‖c_p‖²`.

* **`dilatedSharpSieve_of_perBlock`** — *proven sorry-free*: the specialization
  to the **dilated** frequencies `m ↦ a·(m₀+i)/q`, with `δ⁻¹ = q` substituted via
  `SharpLargeSieve.dilatedBlockWellSpaced`.  This is eq. (4.41) with the explicit
  `K = ⌈M/k⌉ · ((W−W') + q)`.

No new `axiom`, no `sorry`, no `False.elim`/vacuous proof.  The single residual
is `SharpLargeSievePerBlock`; the further `O((log)^{-A})` decay is the separate
`SieveLogDampRefinement` (DAMP) layer named in `LargeSieveInequality.lean`.
-/

import MathExtras.NumberTheory.Analysis.SharpLargeSieveScoping

namespace MathExtras.NumberTheory.Analysis.SharpLargeSieveBlocks

open scoped BigOperators
open Finset
open MathExtras.NumberTheory.Analysis.LargeSieve
open MathExtras.NumberTheory.Analysis.SharpLargeSieve

/-! ## The single-block SHARP large sieve (the named residual)

This is the per-block atom Helfgott invokes in eq. (4.41): the *optimal*
`(N + δ⁻¹)` large sieve for one block of `δ`-well-spaced angles.  We state it
over an **arbitrary** finite index set `B` so that the block-accumulation lemma
can feed it each fiber of the block partition.  It is the same quadratic form as
`LargeSieve.ClassicalLargeSieve`, but:

* indexed by a general `Finset ℕ` `B` (not just `range k`), and
* named separately to mark it as the **single from-scratch core** that the
  block-counting reduction below isolates — the SHARP constant `(N + δ⁻¹)`
  (Beurling–Selberg / Selberg–Montgomery–Vaughan duality), strictly stronger
  than the SOFT Gallagher mean-value form `π N + δ⁻¹`. -/
def SharpLargeSievePerBlock : Prop :=
  ∀ (B : Finset ℕ) (α : ℕ → ℝ) (c : ℕ → ℂ) (P : Finset ℕ) (W' W : ℕ) (δ : ℝ),
    0 < δ → P ⊆ Finset.Ioc W' W →
      WellSpaced δ B α →
        ∑ i ∈ B, ‖∑ p ∈ P, c p * Vinogradov.addChar (α i) p‖ ^ 2 ≤
          (((W : ℝ) - (W' : ℝ)) + δ⁻¹) * ∑ p ∈ P, ‖c p‖ ^ 2

/-! ## Nonnegativity helpers -/

theorem coeffMass_nonneg (c : ℕ → ℂ) (P : Finset ℕ) :
    0 ≤ ∑ p ∈ P, ‖c p‖ ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## The block partition: chunking `range M` by `i ↦ i / k`

The fibers of `i ↦ i / k` partition `range M`; fiber `b` is exactly the window
`[b*k, b*k + k)` of `≤ k` consecutive integers.  We index the blocks by
`range (numBlocks M k)` where `numBlocks M k = ⌈M / k⌉ = (M + k - 1) / k`. -/

/-- The number of size-`k` blocks needed to cover `range M`: `⌈M / k⌉`. -/
def numBlocks (M k : ℕ) : ℕ := (M + k - 1) / k

/-- The fiber map `i ↦ i / k` sends `range M` into `range (numBlocks M k)`. -/
theorem div_lt_numBlocks {M k : ℕ} (hk : 1 ≤ k) {i : ℕ} (hi : i < M) :
    i / k < numBlocks M k := by
  unfold numBlocks
  -- `i / k ≤ (M - 1) / k` and `(M - 1) / k < (M - 1 + k) / k = numBlocks`.
  have hM1 : 1 ≤ M := by omega
  have heq : M + k - 1 = (M - 1) + k := by omega
  rw [heq, Nat.add_div_right _ (by omega : 0 < k)]
  have h1 : i / k ≤ (M - 1) / k := Nat.div_le_div_right (by omega : i ≤ M - 1)
  omega

/-! ## (Step 2) The abstract block-accumulation lemma — proven sorry-free

Given the per-block sharp sieve and the per-block well-spacing, the total
quadratic-form mass over `range M` is bounded by `⌈M/k⌉ · ((W−W') + δ⁻¹)·mass`.
This is the block-counting core of eq. (4.41), with the per-block sharp sieve
isolated as the single hypothesis `SharpLargeSievePerBlock`. -/

/-- **(Helfgott eq. 4.41 — block accumulation, abstract).**

Assume the single-block SHARP large sieve `SharpLargeSievePerBlock`.  Let
`α : ℕ → ℝ` be a frequency family such that **each consecutive block** (each
fiber of `i ↦ i / k` inside `range M`) is `δ`-well-spaced.  Then the total
quadratic-form mass over `range M` is bounded by
`numBlocks M k · ((W − W') + δ⁻¹) · ∑‖c_p‖²`.

The proof: decompose `∑_{i<M}` fiberwise via `sum_fiberwise_of_maps_to`
(`div_lt_numBlocks` gives the `maps_to`), apply the per-block sharp sieve to
each fiber, and sum the `numBlocks M k` identical per-block bounds. -/
theorem blockSum_le_of_perBlock
    (hPB : SharpLargeSievePerBlock)
    (M k : ℕ) (hk : 1 ≤ k)
    (α : ℕ → ℝ) (c : ℕ → ℂ) (P : Finset ℕ) (W' W : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hP : P ⊆ Finset.Ioc W' W)
    (hspaced : ∀ b ∈ Finset.range (numBlocks M k),
      WellSpaced δ ((Finset.range M).filter (fun i => i / k = b)) α) :
    ∑ i ∈ Finset.range M,
        ‖∑ p ∈ P, c p * Vinogradov.addChar (α i) p‖ ^ 2 ≤
      (numBlocks M k : ℝ) * ((((W : ℝ) - (W' : ℝ)) + δ⁻¹) * ∑ p ∈ P, ‖c p‖ ^ 2) := by
  -- abbreviate the per-index summand
  set f : ℕ → ℝ := fun i => ‖∑ p ∈ P, c p * Vinogradov.addChar (α i) p‖ ^ 2 with hf
  -- fiberwise decomposition over the block index `b = i / k`
  have hmaps : ∀ i ∈ Finset.range M, i / k ∈ Finset.range (numBlocks M k) := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    exact div_lt_numBlocks hk hi
  have hfiber :
      ∑ b ∈ Finset.range (numBlocks M k),
          ∑ i ∈ (Finset.range M).filter (fun i => i / k = b), f i
        = ∑ i ∈ Finset.range M, f i :=
    Finset.sum_fiberwise_of_maps_to hmaps f
  rw [← hfiber]
  -- per-block sharp sieve bound, then sum the constant bound over the blocks
  have hperblock : ∀ b ∈ Finset.range (numBlocks M k),
      ∑ i ∈ (Finset.range M).filter (fun i => i / k = b), f i ≤
        (((W : ℝ) - (W' : ℝ)) + δ⁻¹) * ∑ p ∈ P, ‖c p‖ ^ 2 := by
    intro b hb
    exact hPB ((Finset.range M).filter (fun i => i / k = b)) α c P W' W δ hδ hP
      (hspaced b hb)
  have hsum_le := Finset.sum_le_sum hperblock
  have hconst :
      ∑ _b ∈ Finset.range (numBlocks M k),
          (((W : ℝ) - (W' : ℝ)) + δ⁻¹) * ∑ p ∈ P, ‖c p‖ ^ 2
        = (numBlocks M k : ℝ) * ((((W : ℝ) - (W' : ℝ)) + δ⁻¹) * ∑ p ∈ P, ‖c p‖ ^ 2) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact hsum_le.trans_eq hconst

/-! ## (Step 2′→3) The dilated specialization — proven sorry-free

Specialize `α i = a·(m₀ + i)/q` and substitute `δ = 1/q`, `δ⁻¹ = q`.  The
per-block well-spacing hypothesis is discharged by
`SharpLargeSieve.dilatedBlockWellSpaced`: each fiber `[b*k, b*k + k)` of width
`k ≤ q` of dilated frequencies is `1/q`-well-spaced.  This yields eq. (4.41)
with the explicit constant `K = numBlocks M k · ((W − W') + q)`. -/

/-- A fiber `(range M).filter (· / k = b)` of the dilated frequencies
`i ↦ a·i/q` is `1/q`-well-spaced (for `k ≤ q`).  Two distinct fiber members lie
in the same window `[b*k, b*k + k)` of width `k ≤ q`, so their difference is
nonzero of absolute value `< q`, hence `q ∤ (i − j)`; the separation then follows
from `rationalDilatedSeparation`. -/
theorem fiber_dilated_wellSpaced
    {a q : ℤ} (hq : 1 ≤ q) (hcop : IsCoprime a q) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : (k : ℤ) ≤ q) (M : ℕ) (b : ℕ) :
    WellSpaced ((1 : ℝ) / (q : ℝ))
      ((Finset.range M).filter (fun i => i / k = b))
      (fun i => (a : ℝ) * ((i : ℝ)) / (q : ℝ)) := by
  -- Two distinct fiber members `i, j` satisfy `i / k = j / k = b`, so they lie
  -- in the same window `[b*k, b*k+k)`, hence `|i − j| < k ≤ q`, so `q ∤ (i−j)`.
  intro i hi j hj hij
  rw [Finset.mem_filter] at hi hj
  obtain ⟨_, hib⟩ := hi
  obtain ⟨_, hjb⟩ := hj
  have hq_pos : 0 < q := lt_of_lt_of_le one_pos hq
  have hk0 : 0 < k := hk1
  -- Both `i, j ∈ [b*k, b*k + k)` via the Euclidean decomposition.
  have hdi : k * (i / k) + i % k = i := Nat.div_add_mod i k
  have hdj : k * (j / k) + j % k = j := Nat.div_add_mod j k
  have hmi : i % k < k := Nat.mod_lt i hk0
  have hmj : j % k < k := Nat.mod_lt j hk0
  -- so `|i − j| < k ≤ q`, nonzero, hence `q ∤ (i − j)`.
  have hndvd : ¬ (q ∣ ((i : ℤ) - (j : ℤ))) := by
    intro hdvd
    have hij_ne : (i : ℤ) - (j : ℤ) ≠ 0 := by
      intro h; exact hij (by exact_mod_cast sub_eq_zero.mp h)
    have hijk : (i : ℤ) - (j : ℤ) < k ∧ -(k : ℤ) < (i : ℤ) - (j : ℤ) := by
      have h1 : (i : ℤ) = k * (i / k : ℕ) + (i % k : ℕ) := by exact_mod_cast hdi.symm
      have h2 : (j : ℤ) = k * (j / k : ℕ) + (j % k : ℕ) := by exact_mod_cast hdj.symm
      have hbij : ((i / k : ℕ) : ℤ) = ((j / k : ℕ) : ℤ) := by
        rw [hib, hjb]
      have hmi' : ((i % k : ℕ) : ℤ) < k := by exact_mod_cast hmi
      have hmj' : ((j % k : ℕ) : ℤ) < k := by exact_mod_cast hmj
      have hmi0 : (0 : ℤ) ≤ ((i % k : ℕ) : ℤ) := Int.natCast_nonneg _
      have hmj0 : (0 : ℤ) ≤ ((j % k : ℕ) : ℤ) := Int.natCast_nonneg _
      constructor <;> nlinarith [h1, h2, hbij, hmi', hmj', hmi0, hmj0]
    have habs_lt : |(i : ℤ) - (j : ℤ)| < q := by
      rw [abs_lt]; exact ⟨by linarith [hijk.2, hk], by linarith [hijk.1, hk]⟩
    have habs_ge : q ≤ |(i : ℤ) - (j : ℤ)| :=
      Int.le_of_dvd (abs_pos.mpr hij_ne) ((dvd_abs _ _).mpr hdvd)
    exact absurd habs_ge (not_le.mpr habs_lt)
  have hsep := rationalDilatedSeparation (a := a) (q := q) (m := (i : ℤ)) (m' := (j : ℤ))
    hq hcop hndvd
  -- match the cast form
  have hci : (a : ℝ) * ((i : ℤ) : ℝ) / (q : ℝ) = (a : ℝ) * ((i : ℕ) : ℝ) / (q : ℝ) := by
    push_cast; ring
  have hcj : (a : ℝ) * ((j : ℤ) : ℝ) / (q : ℝ) = (a : ℝ) * ((j : ℕ) : ℝ) / (q : ℝ) := by
    push_cast; ring
  rw [hci, hcj] at hsep
  simpa using hsep

/-- **(Helfgott eq. 4.41 — the dilated per-`d` bound, `δ⁻¹ = q`).**

Assume the single-block SHARP large sieve `SharpLargeSievePerBlock`.  For the
**dilated** frequencies `α i = a·i/q`, with block size `1 ≤ k ≤ q` and coprime
`gcd(a,q)=1`, the total quadratic-form mass over `range M` satisfies

  `∑_{i<M} ‖∑_p c_p e(a·i·p/q)‖² ≤ numBlocks M k · ((W − W') + q) · ∑‖c_p‖²`.

This is eq. (4.41): the `q`-weighted `δ⁻¹ = q` term (from the `1/q`-block
well-spacing, `δ = 1/q ⟹ δ⁻¹ = q`) times the block count `⌈M/k⌉`.  The per-block
well-spacing is discharged sorry-free by `fiber_dilated_wellSpaced`; the per-block
sharp constant is the single residual `SharpLargeSievePerBlock`. -/
theorem dilatedSharpSieve_of_perBlock
    (hPB : SharpLargeSievePerBlock)
    {a q : ℤ} (hq : 1 ≤ q) (hcop : IsCoprime a q)
    (M k : ℕ) (hk1 : 1 ≤ k) (hk : (k : ℤ) ≤ q)
    (c : ℕ → ℂ) (P : Finset ℕ) (W' W : ℕ) (hP : P ⊆ Finset.Ioc W' W) :
    ∑ i ∈ Finset.range M,
        ‖∑ p ∈ P, c p * Vinogradov.addChar ((a : ℝ) * (i : ℝ) / (q : ℝ)) p‖ ^ 2 ≤
      (numBlocks M k : ℝ) *
        ((((W : ℝ) - (W' : ℝ)) + (q : ℝ)) * ∑ p ∈ P, ‖c p‖ ^ 2) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast lt_of_lt_of_le one_pos hq
  have hδ : (0 : ℝ) < (1 : ℝ) / (q : ℝ) := by positivity
  -- per-block well-spacing for every block index `b`
  have hspaced : ∀ b ∈ Finset.range (numBlocks M k),
      WellSpaced ((1 : ℝ) / (q : ℝ))
        ((Finset.range M).filter (fun i => i / k = b))
        (fun i => (a : ℝ) * (i : ℝ) / (q : ℝ)) :=
    fun b _ => fiber_dilated_wellSpaced hq hcop hk1 hk M b
  -- abstract block accumulation with `δ = 1/q`
  have hacc := blockSum_le_of_perBlock hPB M k hk1
    (fun i => (a : ℝ) * (i : ℝ) / (q : ℝ)) c P W' W ((1 : ℝ) / (q : ℝ)) hδ hP hspaced
  -- substitute `δ⁻¹ = (1/q)⁻¹ = q`
  have hinv : ((1 : ℝ) / (q : ℝ))⁻¹ = (q : ℝ) := by
    rw [one_div, inv_inv]
  rwa [hinv] at hacc

#print axioms blockSum_le_of_perBlock
#print axioms dilatedSharpSieve_of_perBlock
#print axioms fiber_dilated_wellSpaced
#print axioms div_lt_numBlocks

end MathExtras.NumberTheory.Analysis.SharpLargeSieveBlocks
