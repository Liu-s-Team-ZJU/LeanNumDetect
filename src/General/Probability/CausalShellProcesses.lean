import General.Probability.WeakShellDecomposition
import General.Probability.CausalMaskChaining
import General.Probability.AtomicPrefixEntropy

/-!
# First-crossing shells and normalized clipped processes

The deterministic first-crossing shadow is expanded into disjoint masks.
Each actual mask process is bounded by its normalized arbitrary-class
supremum, and its radius weight is exactly its squared-cardinality path
weight. These identities connect the weak-shell error estimates to causal
mask chaining without discarding exceptional rows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.WeakShellDecomposition

theorem CrossingSpec_unique {ℓ : ℕ} (r : Fin ℓ → ℝ) (a : Fin ℓ → ℂ)
    {u v : Option (Fin ℓ)} (hu : CrossingSpec r a u) (hv : CrossingSpec r a v) : u = v := by
  cases u with
  | none =>
    cases v with
    | none => rfl
    | some k => exact False.elim (not_lt_of_ge hv.1 (hu k))
  | some j =>
    cases v with
    | none => exact False.elim (not_lt_of_ge hu.1 (hv j))
    | some k =>
      by_cases hjk : j = k
      · simp [hjk]
      · rcases lt_or_gt_of_ne hjk with h | h
        · exact False.elim (not_lt_of_ge hu.1 (hv.2 j h))
        · exact False.elim (not_lt_of_ge hv.1 (hu.2 k h))

theorem CrossingSpec_eq_some_iff {ℓ : ℕ} (r : Fin ℓ → ℝ) (a : Fin ℓ → ℂ)
    {u : Option (Fin ℓ)} (hu : CrossingSpec r a u) (k : Fin ℓ) :
    u = some k ↔ r k ≤ ‖a k‖ ∧ ∀ j, j < k → ‖a j‖ < r j := by
  constructor
  · intro h
    simpa only [h, CrossingSpec] using hu
  · intro h
    exact CrossingSpec_unique r a hu h

theorem clippedEnergy_eq_clippedComplexEnergy (q : ℝ) (z : ℂ) :
    clippedEnergy (16 * q ^ 2) z = BoundedRieszConcentration.clippedComplexEnergy (4 * q) z := by
  unfold clippedEnergy BoundedRieszConcentration.clippedComplexEnergy
    BoundedRieszConcentration.clippedRealSquare
  rw [show (4 * q) ^ 2 = 16 * q ^ 2 by ring]

/-- First-crossing shadow energy expands exactly into the selected masks. -/
theorem shellEnergy_sum_eq_mask_sum {m ℓ : ℕ}
    (r : Fin ℓ → ℝ) (z : Fin m → ℂ) (level : Fin m → Option (Fin ℓ))
    (σ : Fin m → Bool) :
    (∑ i, FiniteMatrixSampling.finiteBernoulliSign (σ i) * shellEnergy r (z i) (level i)) =
      ∑ k, ∑ i : Fin m, if level i = some k then
        FiniteMatrixSampling.finiteBernoulliSign (σ i) *
          BoundedRieszConcentration.clippedComplexEnergy (4 * r k) (z i) else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases h : level i with
  | none => simp [shellEnergy]
  | some k =>
    simp only [shellEnergy, Option.some.injEq]
    rw [clippedEnergy_eq_clippedComplexEnergy]
    simp

/-- The shell weight is exactly the sum of the radius-squared mask masses. -/
theorem shellWeight_sum_eq_mask_card {m ℓ : ℕ}
    (r : Fin ℓ → ℝ) (level : Fin m → Option (Fin ℓ)) :
    (∑ i, shellWeight r (level i)) =
      ∑ k, r k ^ 2 * ((Finset.univ.filter fun i => level i = some k).card : ℝ) := by
  classical
  have hcard (k : Fin ℓ) : r k ^ 2 *
      ((Finset.univ.filter fun i => level i = some k).card : ℝ) =
        ∑ i : Fin m, if level i = some k then r k ^ 2 else 0 := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases h : level i with
  | none => simp [shellWeight]
  | some k => simp [shellWeight]

/-- A bounded total shadow error also bounds every signed error. -/
theorem signed_shell_residual_le {m ℓ : ℕ}
    (r : Fin ℓ → ℝ) (z : Fin m → ℂ) (level : Fin m → Option (Fin ℓ)) {ε : ℝ}
    (hres : ∑ i, (‖z i‖ ^ 2 - shellEnergy r (z i) (level i)) ≤ ε)
    (σ : Fin m → Bool) :
    |∑ i, FiniteMatrixSampling.finiteBernoulliSign (σ i) *
      (‖z i‖ ^ 2 - shellEnergy r (z i) (level i))| ≤ ε := by
  calc
    _ ≤ ∑ i, |FiniteMatrixSampling.finiteBernoulliSign (σ i) *
        (‖z i‖ ^ 2 - shellEnergy r (z i) (level i))| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, (‖z i‖ ^ 2 - shellEnergy r (z i) (level i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (shellEnergy_le r (z i) (level i)))]
      have h : |FiniteMatrixSampling.finiteBernoulliSign (σ i)| = 1 := by
        cases σ i <;> norm_num [FiniteMatrixSampling.finiteBernoulliSign]
      rw [h, one_mul]
    _ ≤ ε := hres

end LeanNumDetect.WeakShellDecomposition

namespace LeanNumDetect.BoundedRieszConcentration

open LeanNumDetect.FiniteMatrixSampling LeanNumDetect.WeakShellDecomposition

/-- The actual clipped signal on one mask is dominated by the normalized
mask process times the square root of its cardinality. -/
theorem masked_clipped_signal_le_normalizedProcess
    {N m : ℕ} {T : Type*} [Nonempty T] (f : T → ComplexVector N)
    (rows : Fin m → ComplexVector N) (E : Finset (Fin m)) (R : ℝ)
    (t : T) (σ : Fin m → Bool) :
    |∑ i : Fin m, if i ∈ E then finiteBernoulliSign (σ i) *
      clippedComplexEnergy R (rowPairing (f t) (rows i)) else 0| ≤
      Real.sqrt (E.card : ℝ) * normalizedClippedMaskProcess f rows E R σ := by
  classical
  let z := fun t (i : Fin m) => clippedComplexEnergy R
    (rowPairing (f t) (if i ∈ E then rows i else 0))
  have henv : ∀ i, BddAbove (Set.range fun t => |z t i|) := by
    intro i
    refine ⟨2 * R ^ 2, ?_⟩
    rintro _ ⟨t, rfl⟩
    dsimp only [z]
    rw [abs_of_nonneg (clippedComplexEnergy_nonneg _ _)]
    exact clippedComplexEnergy_le_radius _ _
  have hid : (∑ i : Fin m, if i ∈ E then finiteBernoulliSign (σ i) *
      clippedComplexEnergy R (rowPairing (f t) (rows i)) else 0) =
        ∑ i, finiteBernoulliSign (σ i) * z t i := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [z]
    split_ifs <;> simp [rowPairing]
  by_cases hc : E.card = 0
  · have hE : E = ∅ := Finset.card_eq_zero.mp hc
    simp [hE]
  · have hcard : (0 : ℝ) < E.card := by exact_mod_cast Nat.pos_of_ne_zero hc
    have h := le_csSup (bddAbove_range_abs_linear_combination z
      (fun i => finiteBernoulliSign (σ i)) henv) (Set.mem_range_self t)
    change _ ≤ bernoulliAbsoluteSupremum z σ at h
    rw [hid, normalizedClippedMaskProcess, ← mul_assoc,
      mul_inv_cancel₀ (Real.sqrt_pos.mpr hcard).ne', one_mul]
    exact h

/-- The actual shell energy has a causal-mask chaining bound. The two
deterministic shadow hypotheses are supplied by weak-shell approximation;
the stochastic budgets are proved here from the original row and ℓ¹ bounds. -/
theorem causal_shell_energy_expectation_le
    {N m ℓ : ℕ} (hN : 0 < N) {T : Type*} [Nonempty T]
    {J : Fin ℓ → Type*} [∀ k, Fintype (J k)] [∀ k, Nonempty (J k)]
    (f : T → ComplexVector N) (rows : Fin m → ComplexVector N)
    (E : ∀ k, J k → Finset (Fin m)) (choose : ∀ k, T → J k)
    (r : Fin ℓ → ℝ) (hr : ∀ k, 0 < r k)
    (level : T → Fin m → Option (Fin ℓ))
    (hmask : ∀ k t, E k (choose k t) = Finset.univ.filter (fun i => level t i = some k))
    {s K ε W : ℝ} (hK : 0 ≤ K)
    (hf : ∀ t, coefficientL1Norm (f t) ≤ Real.sqrt s)
    (hrows : ∀ i j, ‖rows i j‖ ≤ K) (t₀ : T) (hfzero : f t₀ = 0)
    (hresidual : ∀ t, ∑ i, (rowEnergy (f t) (rows i) -
      shellEnergy r (rowPairing (f t) (rows i)) (level t i)) ≤ ε)
    (hweight : ∀ t, ∑ i, shellWeight r (level t i) ≤ W) :
    finiteAverage (bernoulliAbsoluteSupremum (fun t i => rowEnergy (f t) (rows i))) ≤
      ε + Real.sqrt W * Real.sqrt (∑ k,
        (2 * (16 * (4 * r k) * Real.sqrt s *
            Real.sqrt (2 * K ^ 2 * Real.log (2 * (N : ℝ)))) ^ 2 +
          160 * (4 * r k) ^ 4 * Real.log (2 * (Fintype.card (J k) : ℝ))) / r k ^ 2) := by
  classical
  let A := fun t k => Real.sqrt ((E k (choose k t)).card : ℝ)
  let H := fun k (σ : Fin m → Bool) => finiteProcessAbsoluteMaximum
    (fun j => normalizedClippedMaskProcess f rows (E k j) (4 * r k)) σ
  let V := fun k => 2 * (16 * (4 * r k) * Real.sqrt s *
      Real.sqrt (2 * K ^ 2 * Real.log (2 * (N : ℝ)))) ^ 2 +
    160 * (4 * r k) ^ 4 * Real.log (2 * (Fintype.card (J k) : ℝ))
  have hpathWeight (t : T) : ∑ k, (r k * A t k) ^ 2 ≤ W := by
    have heq : (∑ k, (r k * A t k) ^ 2) = ∑ i, shellWeight r (level t i) := by
      rw [shellWeight_sum_eq_mask_card]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [A]
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), hmask]
    rw [heq]
    exact hweight t
  have hdecomp (t : T) (σ : Fin m → Bool) :
      |∑ i, finiteBernoulliSign (σ i) * rowEnergy (f t) (rows i)| ≤
        ε + ∑ k, A t k * H k σ := by
    let z := fun i => rowPairing (f t) (rows i)
    have hrbound := signed_shell_residual_le r z (level t) (hresidual t) σ
    have hid : (∑ i, finiteBernoulliSign (σ i) * rowEnergy (f t) (rows i)) =
        (∑ i, finiteBernoulliSign (σ i) * (‖z i‖ ^ 2 - shellEnergy r (z i) (level t i))) +
          ∑ k, ∑ i : Fin m, if level t i = some k then finiteBernoulliSign (σ i) *
            clippedComplexEnergy (4 * r k) (z i) else 0 := by
      rw [← shellEnergy_sum_eq_mask_sum]
      simp only [mul_sub, Finset.sum_sub_distrib, rowEnergy, z]
      ring
    rw [hid]
    apply (abs_add_le _ _).trans
    apply add_le_add hrbound
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro k _
    have hsignal := masked_clipped_signal_le_normalizedProcess f rows
      (E k (choose k t)) (4 * r k) t σ
    have hmem (i : Fin m) : i ∈ E k (choose k t) ↔ level t i = some k := by
      rw [hmask]
      simp
    simp_rw [hmem] at hsignal
    apply hsignal.trans
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact (le_abs_self _).trans (abs_process_le_absoluteMaximum
      (fun j => normalizedClippedMaskProcess f rows (E k j) (4 * r k)) (choose k t) σ)
  have hsecond (k : Fin ℓ) : finiteAverage (fun σ : Fin m → Bool => H k σ ^ 2) ≤ V k :=
    normalizedClippedMask_family_square_expectation_le hN f rows (E k) hK
      (by have h := hr k; positivity) hf hrows t₀ hfzero
  exact bernoulli_path_chaining_expectation_le (fun t i => rowEnergy (f t) (rows i)) A r H
    (fun k => (hr k).ne') V hpathWeight hdecomp hsecond

end LeanNumDetect.BoundedRieszConcentration
