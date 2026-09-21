/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The duality principle for the sharp large sieve — Track S

This file proves, *sorry-free*, the **duality principle** for finite complex
matrices: for a matrix `M : ι → κ → ℂ` and a constant `Δ ≥ 0`, the *row form*

  `∀ a, ∑_r ‖∑_n M_{r,n} a_n‖² ≤ Δ · ∑_n ‖a_n‖²`

holds **iff** the *column (dual) form*

  `∀ b, ∑_n ‖∑_r conj(M_{r,n}) b_r‖² ≤ Δ · ∑_r ‖b_r‖²`

holds.  This is the elementary statement that a finite matrix and its conjugate
transpose have the same operator `ℓ²→ℓ²` norm (`‖M‖ = ‖Mᴴ‖`).  We prove it
directly from the adjoint pairing identity and Cauchy–Schwarz — no spectral
theory, no `EuclideanSpace`/`Matrix` operator-norm scaffolding.

This is the cleanest reachable foundation for the SHARP `(N + δ⁻¹)` large sieve:
the row form is the large sieve itself (`SharpLargeSievePerBlock`, with
`M_{r,n} = e(α_r · n)`), and the column form is the *dual large sieve*, which is
bounded by the Montgomery–Vaughan Hilbert-type inequality
`‖∑_{r≠s} x_r conj(x_s)/(α_r−α_s)‖ ≤ δ⁻¹ ∑‖x_r‖²`.  The single deep analytic
residual is therefore isolated to the *dual* statement
`DualSharpLargeSievePerBlock`, and the reduction
`DualSharpLargeSievePerBlock → SharpLargeSievePerBlock` is proven here via the
duality principle.

## What is delivered (all sorry-free)

* **`rowBound` / `colBound`** — the two finite quadratic-form bounds for a
  general matrix `M : ι → κ → ℂ` over finite index `Finset`s, constant `Δ`.
* **`adjoint_pairing`** — `∑_r conj((M a)_r)·b_r = ∑_n conj(a_n)·(Mᴴ b)_n`
  (the finite-sum adjoint identity, proven by Fubini + conj distribution).
* **`duality_principle`** — `(∀ a, rowBound) ↔ (∀ b, colBound)` for the same
  `Δ ≥ 0`.  **Proven sorry-free.**
* **`DualSharpLargeSievePerBlock`** — the named *dual* large sieve `Prop`, the
  single deep analytic residual (Montgomery–Vaughan Hilbert inequality core).
* **`sharpLargeSievePerBlock_of_dual`** — the reduction
  `DualSharpLargeSievePerBlock → SharpLargeSievePerBlock`, proven via the
  duality principle.  **Proven sorry-free.**

No new `axiom`, no `sorry`, no vacuous proof.
-/

import MathExtras.NumberTheory.Analysis.SharpLargeSieveBlocks

namespace MathExtras.NumberTheory.Analysis.SharpLargeSieveDuality

open scoped BigOperators ComplexConjugate
open Finset
open MathExtras.NumberTheory.Analysis.LargeSieve
open MathExtras.NumberTheory.Analysis.SharpLargeSieveBlocks

/-! ## Finite ℓ² quadratic forms for a general matrix -/

/-- The row image `(M a)_r = ∑_{n ∈ cols} M r n · a n`. -/
noncomputable def rowApply {ι κ : Type*} (M : ι → κ → ℂ) (cols : Finset κ)
    (a : κ → ℂ) (r : ι) : ℂ :=
  ∑ n ∈ cols, M r n * a n

/-- The column image `(Mᴴ b)_n = ∑_{r ∈ rows} conj(M r n) · b r`. -/
noncomputable def colApply {ι κ : Type*} (M : ι → κ → ℂ) (rows : Finset ι)
    (b : ι → ℂ) (n : κ) : ℂ :=
  ∑ r ∈ rows, conj (M r n) * b r

/-- **Row bound** with constant `Δ`:
`∑_r ‖(M a)_r‖² ≤ Δ · ∑_n ‖a_n‖²` for all `a` supported on `cols`. -/
def RowBound {ι κ : Type*} (M : ι → κ → ℂ) (rows : Finset ι) (cols : Finset κ)
    (Δ : ℝ) : Prop :=
  ∀ a : κ → ℂ,
    ∑ r ∈ rows, ‖rowApply M cols a r‖ ^ 2 ≤ Δ * ∑ n ∈ cols, ‖a n‖ ^ 2

/-- **Column (dual) bound** with constant `Δ`:
`∑_n ‖(Mᴴ b)_n‖² ≤ Δ · ∑_r ‖b_r‖²` for all `b` supported on `rows`. -/
def ColBound {ι κ : Type*} (M : ι → κ → ℂ) (rows : Finset ι) (cols : Finset κ)
    (Δ : ℝ) : Prop :=
  ∀ b : ι → ℂ,
    ∑ n ∈ cols, ‖colApply M rows b n‖ ^ 2 ≤ Δ * ∑ r ∈ rows, ‖b r‖ ^ 2

/-! ## The adjoint pairing identity -/

/-- The finite-sum **adjoint pairing**:
`∑_r conj((M a)_r) · b_r = ∑_n conj(a_n) · (Mᴴ b)_n`.

Both sides expand to `∑_r ∑_n conj(M r n)·conj(a n)·b r`; Fubini and the
distributivity of complex conjugation over the finite row-sum give the
identity. -/
theorem adjoint_pairing {ι κ : Type*} (M : ι → κ → ℂ) (rows : Finset ι)
    (cols : Finset κ) (a : κ → ℂ) (b : ι → ℂ) :
    ∑ r ∈ rows, conj (rowApply M cols a r) * b r
      = ∑ n ∈ cols, conj (a n) * colApply M rows b n := by
  unfold rowApply colApply
  -- LHS: distribute conj over the row sum, then the outer `* b r`.
  have hL : ∀ r ∈ rows,
      conj (∑ n ∈ cols, M r n * a n) * b r
        = ∑ n ∈ cols, conj (M r n) * conj (a n) * b r := by
    intro r _
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [map_mul]
  -- RHS: distribute the outer `conj (a n) *` over the row sum.
  have hR : ∀ n ∈ cols,
      conj (a n) * (∑ r ∈ rows, conj (M r n) * b r)
        = ∑ r ∈ rows, conj (M r n) * conj (a n) * b r := by
    intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
  -- Now both are double sums of the same term; swap order.
  exact Finset.sum_comm

/-! ## Energies and Cauchy–Schwarz on the pairing -/

/-- The discrete Cauchy–Schwarz `∑ ‖f‖‖g‖ ≤ √(∑‖f‖²)·√(∑‖g‖²)`, obtained from
`Finset.sum_mul_sq_le_sq_mul_sq` by taking square roots. -/
theorem sum_norm_mul_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    ∑ r ∈ s, ‖f r‖ * ‖g r‖
      ≤ Real.sqrt (∑ r ∈ s, ‖f r‖ ^ 2) * Real.sqrt (∑ r ∈ s, ‖g r‖ ^ 2) := by
  have hsq : (∑ r ∈ s, ‖f r‖ * ‖g r‖) ^ 2
      ≤ (∑ r ∈ s, ‖f r‖ ^ 2) * (∑ r ∈ s, ‖g r‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun r => ‖f r‖) (fun r => ‖g r‖)
  have hnn : (0 : ℝ) ≤ ∑ r ∈ s, ‖f r‖ * ‖g r‖ :=
    Finset.sum_nonneg fun r _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hrhs : Real.sqrt ((∑ r ∈ s, ‖f r‖ ^ 2) * (∑ r ∈ s, ‖g r‖ ^ 2))
      = Real.sqrt (∑ r ∈ s, ‖f r‖ ^ 2) * Real.sqrt (∑ r ∈ s, ‖g r‖ ^ 2) :=
    Real.sqrt_mul (Finset.sum_nonneg fun r _ => sq_nonneg _) _
  calc ∑ r ∈ s, ‖f r‖ * ‖g r‖
      = Real.sqrt ((∑ r ∈ s, ‖f r‖ * ‖g r‖) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((∑ r ∈ s, ‖f r‖ ^ 2) * (∑ r ∈ s, ‖g r‖ ^ 2)) :=
          Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ r ∈ s, ‖f r‖ ^ 2) * Real.sqrt (∑ r ∈ s, ‖g r‖ ^ 2) := hrhs

/-- `‖∑_r conj(f r) · g r‖ ≤ √(∑‖f‖²) · √(∑‖g‖²)`
(Cauchy–Schwarz for the finite Hermitian pairing). -/
theorem norm_pairing_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    ‖∑ r ∈ s, conj (f r) * g r‖
      ≤ Real.sqrt (∑ r ∈ s, ‖f r‖ ^ 2) * Real.sqrt (∑ r ∈ s, ‖g r‖ ^ 2) := by
  calc ‖∑ r ∈ s, conj (f r) * g r‖
      ≤ ∑ r ∈ s, ‖conj (f r) * g r‖ := norm_sum_le _ _
    _ = ∑ r ∈ s, ‖f r‖ * ‖g r‖ := by
          apply Finset.sum_congr rfl; intro r _
          rw [norm_mul, RCLike.norm_conj]
    _ ≤ Real.sqrt (∑ r ∈ s, ‖f r‖ ^ 2) * Real.sqrt (∑ r ∈ s, ‖g r‖ ^ 2) :=
          sum_norm_mul_le s f g

/-- The energy `∑ ‖f‖²` equals `‖∑ conj(f) · f‖` (a real nonnegative quantity),
giving the link between the pairing and the ℓ² energy. -/
theorem energy_eq_norm_self_pairing {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ∑ r ∈ s, ‖f r‖ ^ 2 = ‖∑ r ∈ s, conj (f r) * f r‖ := by
  have hsum : ∑ r ∈ s, conj (f r) * f r = ((∑ r ∈ s, ‖f r‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun r _ => sq_nonneg _)]

/-! ## The duality principle (the clean reusable foundation) -/

/-- **The duality principle (one direction).**

If the row form holds with constant `Δ ≥ 0`, then the column (dual) form holds
with the same `Δ`.  Proof: writing `y = Mᴴ b`, the energy `‖y‖²` equals the
pairing `∑ conj(y_n)·(Mᴴ b)_n`; by the adjoint identity this is
`∑ conj((M y)_r)·b_r`, bounded via Cauchy–Schwarz by
`√(∑‖(M y)‖²)·√(∑‖b‖²) ≤ √Δ·‖y‖·√(∑‖b‖²)` using the row bound.  Cancelling one
factor `‖y‖` and squaring gives `‖y‖² ≤ Δ·∑‖b‖²`. -/
theorem colBound_of_rowBound {ι κ : Type*} (M : ι → κ → ℂ)
    (rows : Finset ι) (cols : Finset κ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hrow : RowBound M rows cols Δ) : ColBound M rows cols Δ := by
  intro b
  set y : κ → ℂ := colApply M rows b with hy
  set Eb : ℝ := ∑ r ∈ rows, ‖b r‖ ^ 2 with hEb
  set Ey : ℝ := ∑ n ∈ cols, ‖y n‖ ^ 2 with hEy
  have hEb0 : 0 ≤ Eb := Finset.sum_nonneg fun r _ => sq_nonneg _
  have hEy0 : 0 ≤ Ey := Finset.sum_nonneg fun n _ => sq_nonneg _
  -- Energy of `y` as a self-pairing, then adjoint-swap to a pairing over rows.
  have hself : Ey = ‖∑ n ∈ cols, conj (y n) * y n‖ :=
    energy_eq_norm_self_pairing cols y
  -- `∑_n conj(y_n)·(Mᴴ b)_n = ∑_r conj((M y)_r)·b_r` (adjoint identity, reversed).
  have hadj : ∑ n ∈ cols, conj (y n) * colApply M rows b n
      = ∑ r ∈ rows, conj (rowApply M cols y r) * b r :=
    (adjoint_pairing M rows cols y b).symm
  -- Since `y = colApply M rows b`, `conj(y_n)·y_n = conj(y_n)·colApply…`.
  have hyeq : ∑ n ∈ cols, conj (y n) * y n
      = ∑ n ∈ cols, conj (y n) * colApply M rows b n := by rw [hy]
  -- Cauchy–Schwarz on the row pairing.
  have hCS : ‖∑ r ∈ rows, conj (rowApply M cols y r) * b r‖
      ≤ Real.sqrt (∑ r ∈ rows, ‖rowApply M cols y r‖ ^ 2) * Real.sqrt Eb :=
    norm_pairing_le rows (fun r => rowApply M cols y r) b
  -- Row bound: `∑_r ‖(M y)_r‖² ≤ Δ·Ey`.
  have hrowy : ∑ r ∈ rows, ‖rowApply M cols y r‖ ^ 2 ≤ Δ * Ey := hrow y
  -- Chain: Ey ≤ √(Δ·Ey)·√Eb.
  have hCS' : Ey ≤ Real.sqrt (∑ r ∈ rows, ‖rowApply M cols y r‖ ^ 2) * Real.sqrt Eb := by
    calc Ey = ‖∑ r ∈ rows, conj (rowApply M cols y r) * b r‖ := by
              rw [hself, hyeq, hadj]
      _ ≤ Real.sqrt (∑ r ∈ rows, ‖rowApply M cols y r‖ ^ 2) * Real.sqrt Eb := hCS
  have hchain : Ey ≤ Real.sqrt (Δ * Ey) * Real.sqrt Eb := by
    refine hCS'.trans ?_
    have hle : Real.sqrt (∑ r ∈ rows, ‖rowApply M cols y r‖ ^ 2) ≤ Real.sqrt (Δ * Ey) :=
      Real.sqrt_le_sqrt hrowy
    gcongr
  -- √(Δ·Ey) = √Δ·√Ey.
  have hsplit : Real.sqrt (Δ * Ey) = Real.sqrt Δ * Real.sqrt Ey :=
    Real.sqrt_mul hΔ Ey
  rw [hsplit] at hchain
  -- Conclude Ey ≤ Δ·Eb.  Two cases on Ey = 0.
  rcases eq_or_lt_of_le hEy0 with hEy_eq | hEy_pos
  · -- Ey = 0 ≤ Δ·Eb.
    rw [← hEy_eq]
    exact mul_nonneg hΔ hEb0
  · -- Ey > 0: write Ey = √Ey·√Ey, cancel one factor.
    have hsqEy : Real.sqrt Ey > 0 := Real.sqrt_pos.mpr hEy_pos
    have hEy_sq : Real.sqrt Ey * Real.sqrt Ey = Ey := Real.mul_self_sqrt hEy0
    -- from hchain: √Ey·√Ey ≤ √Δ·√Ey·√Eb, divide by √Ey > 0.
    have hchain' : Real.sqrt Ey * Real.sqrt Ey
        ≤ (Real.sqrt Δ * Real.sqrt Eb) * Real.sqrt Ey := by
      rw [hEy_sq]; nlinarith [hchain]
    have hsqEy_le : Real.sqrt Ey ≤ Real.sqrt Δ * Real.sqrt Eb :=
      le_of_mul_le_mul_right (by nlinarith [hchain']) hsqEy
    -- square both sides.
    have hsqEy_nn : 0 ≤ Real.sqrt Ey := Real.sqrt_nonneg _
    have hrhs_nn : 0 ≤ Real.sqrt Δ * Real.sqrt Eb :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq : (Real.sqrt Ey) ^ 2 ≤ (Real.sqrt Δ * Real.sqrt Eb) ^ 2 :=
      pow_le_pow_left₀ hsqEy_nn hsqEy_le 2
    rw [Real.sq_sqrt hEy0] at hsq
    have hrhs_sq : (Real.sqrt Δ * Real.sqrt Eb) ^ 2 = Δ * Eb := by
      rw [mul_pow, Real.sq_sqrt hΔ, Real.sq_sqrt hEb0]
    rwa [hrhs_sq] at hsq

/-- **The duality principle.**

For a finite complex matrix `M` and a constant `Δ ≥ 0`, the row form holds iff
the column (dual) form holds.  Both directions are `colBound_of_rowBound`,
applied to `M` and to the conjugate-transposed matrix `fun r n => conj (M r n)`
with rows/cols swapped (using `conj (conj z) = z` and that the column apply of
`Mᴴ` is the row apply of `M`). -/
theorem duality_principle {ι κ : Type*} (M : ι → κ → ℂ)
    (rows : Finset ι) (cols : Finset κ) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    RowBound M rows cols Δ ↔ ColBound M rows cols Δ := by
  constructor
  · exact colBound_of_rowBound M rows cols Δ hΔ
  · intro hcol
    -- Apply the forward direction to the transposed matrix `N r n = conj (M n r)`.
    set N : κ → ι → ℂ := fun n r => conj (M r n) with hN
    -- `RowBound N cols rows Δ` is exactly `ColBound M rows cols Δ`.
    have hNrow : RowBound N cols rows Δ := by
      intro b
      have hrowN : ∀ n, rowApply N rows b n = colApply M rows b n := by
        intro n; rfl
      simpa [hrowN] using hcol b
    have hNcol : ColBound N cols rows Δ := colBound_of_rowBound N cols rows Δ hΔ hNrow
    -- `ColBound N cols rows Δ` is `RowBound M rows cols Δ` after `conj∘conj = id`.
    intro a
    have hcolN : ∀ r, colApply N cols a r = rowApply M cols a r := by
      intro r
      unfold colApply rowApply
      apply Finset.sum_congr rfl
      intro n _
      rw [hN, Complex.conj_conj, mul_comm]
    simpa [hcolN] using hNcol a

/-! ## Reduction of `SharpLargeSievePerBlock` to the dual large sieve

The single-block SHARP large sieve `SharpLargeSievePerBlock` is exactly the
**row form** of the duality principle for the matrix `M i p = e(α_i · p)`,
indexed by `i ∈ B` (rows) and `p ∈ P` (columns), with constant
`Δ = (W − W') + δ⁻¹`.  By `duality_principle` it is therefore equivalent to the
**column (dual)** form, which is the Montgomery–Vaughan *dual* large sieve.  We
isolate that dual statement as `DualSharpLargeSievePerBlock` — the single deep
analytic residual — and prove `DualSharpLargeSievePerBlock → SharpLargeSievePerBlock`
via the duality principle, sorry-free.

The dual statement bounds
`∑_{p ∈ P} ‖∑_{i ∈ B} conj(e(α_i p))·b_i‖² ≤ ((W−W') + δ⁻¹)·∑_{i ∈ B}‖b_i‖²`.
Its standard proof is the Montgomery–Vaughan Hilbert-type inequality
`‖∑_{i≠j} x_i conj(x_j)/(α_i − α_j)‖ ≤ δ⁻¹·∑‖x_i‖²` applied after expanding the
diagonal `(W−W')` and off-diagonal `δ⁻¹` contributions — see the "REALISTIC
EFFORT" note in the file header / report. -/

/-- The exponential matrix `M i p = e(α_i · p) = addChar (α i) p`. -/
noncomputable def expMatrix (α : ℕ → ℝ) : ℕ → ℕ → ℂ :=
  fun i p => Vinogradov.addChar (α i) p

/-- **(DUAL) The dual single-block SHARP large sieve** — the single deep
analytic residual (Montgomery–Vaughan Hilbert inequality core).

For `δ`-well-spaced angles `α` indexed by a `Finset` `B`, and any coefficients
`b : ℕ → ℂ` on `B`, the dual quadratic form over the prime columns `P ⊆ Ioc W' W`
is bounded by the SHARP constant `((W−W') + δ⁻¹)`:

  `∑_{p ∈ P} ‖∑_{i ∈ B} conj(e(α_i p))·b_i‖² ≤ ((W−W') + δ⁻¹)·∑_{i ∈ B}‖b_i‖²`. -/
def DualSharpLargeSievePerBlock : Prop :=
  ∀ (B : Finset ℕ) (α : ℕ → ℝ) (b : ℕ → ℂ) (P : Finset ℕ) (W' W : ℕ) (δ : ℝ),
    0 < δ → P ⊆ Finset.Ioc W' W →
      WellSpaced δ B α →
        ∑ p ∈ P, ‖∑ i ∈ B, conj (Vinogradov.addChar (α i) p) * b i‖ ^ 2 ≤
          (((W : ℝ) - (W' : ℝ)) + δ⁻¹) * ∑ i ∈ B, ‖b i‖ ^ 2

/-- The sharp constant `(W − W') + δ⁻¹` is nonnegative when `δ > 0` and
`W' ≤ W`; for the reduction we only need it `≥ 0` in the regime the large-sieve
is applied (`P ⊆ Ioc W' W` nonempty forces `W' ≤ W`, but we prove the bound for
all configurations by handling `W < W'` separately inside). -/
theorem sharpConst_nonneg_of_subset {P : Finset ℕ} {W' W : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hP : P ⊆ Finset.Ioc W' W) (hPne : P.Nonempty) :
    0 ≤ ((W : ℝ) - (W' : ℝ)) + δ⁻¹ := by
  obtain ⟨p, hp⟩ := hPne
  have hpIoc := hP hp
  rw [Finset.mem_Ioc] at hpIoc
  have hWW : W' ≤ W := le_trans (le_of_lt hpIoc.1) hpIoc.2
  have hN : (0:ℝ) ≤ (W : ℝ) - (W' : ℝ) := by
    have : (W' : ℝ) ≤ (W : ℝ) := by exact_mod_cast hWW
    linarith
  have hδinv : (0:ℝ) ≤ δ⁻¹ := le_of_lt (inv_pos.mpr hδ)
  linarith

/-- **The reduction (proven sorry-free).**

The dual large sieve `DualSharpLargeSievePerBlock` implies the primal sharp
large sieve `SharpLargeSievePerBlock`, via the duality principle for the
exponential matrix `expMatrix α` on rows `B` and columns `P`. -/
theorem sharpLargeSievePerBlock_of_dual
    (hDual : DualSharpLargeSievePerBlock) : SharpLargeSievePerBlock := by
  intro B α c P W' W δ hδ hP hspaced
  -- Constant and nonnegativity (split on whether `P` is empty).
  rcases P.eq_empty_or_nonempty with hPe | hPne
  · -- empty support: LHS is `∑_{i∈B} ‖0‖² = 0`, RHS is `Δ·0 = 0`.
    subst hPe
    have hLHS : ∑ i ∈ B, ‖∑ p ∈ (∅ : Finset ℕ),
        c p * Vinogradov.addChar (α i) p‖ ^ 2 = 0 := by
      apply Finset.sum_eq_zero; intro i _; simp
    have hRHS : (((W : ℝ) - (W' : ℝ)) + δ⁻¹) * ∑ p ∈ (∅ : Finset ℕ), ‖c p‖ ^ 2 = 0 := by
      simp
    rw [hLHS, hRHS]
  · have hΔ : 0 ≤ ((W : ℝ) - (W' : ℝ)) + δ⁻¹ :=
      sharpConst_nonneg_of_subset hδ hP hPne
    set Δ : ℝ := ((W : ℝ) - (W' : ℝ)) + δ⁻¹ with hΔdef
    -- The dual statement IS `ColBound (expMatrix α) B P Δ`.
    have hcol : ColBound (expMatrix α) B P Δ := by
      intro b
      have hb := hDual B α b P W' W δ hδ hP hspaced
      -- `colApply (expMatrix α) B b p = ∑_{i∈B} conj(addChar (α i) p)·b i`.
      have hcolApply : ∀ p, colApply (expMatrix α) B b p
          = ∑ i ∈ B, conj (Vinogradov.addChar (α i) p) * b i := by
        intro p; rfl
      simpa [hcolApply, hΔdef] using hb
    -- Duality: `ColBound → RowBound`.
    have hrow : RowBound (expMatrix α) B P Δ :=
      (duality_principle (expMatrix α) B P Δ hΔ).mpr hcol
    -- `RowBound (expMatrix α) B P Δ` applied to `c` is the primal statement,
    -- modulo `rowApply (expMatrix α) P c i = ∑_p addChar (α i) p · c p`.
    have hrc := hrow c
    have hrowApply : ∀ i, rowApply (expMatrix α) P c i
        = ∑ p ∈ P, c p * Vinogradov.addChar (α i) p := by
      intro i
      unfold rowApply expMatrix
      apply Finset.sum_congr rfl
      intro p _
      rw [mul_comm]
    simpa [hrowApply, hΔdef] using hrc

#print axioms adjoint_pairing
#print axioms duality_principle
#print axioms sharpLargeSievePerBlock_of_dual

end MathExtras.NumberTheory.Analysis.SharpLargeSieveDuality
