import General.Probability.FiniteBernoulliProcess

/-!
# Finite multiscale chains for Bernoulli processes

An arbitrary, possibly infinite process class is approximated by the sum of
finitely many finite families of increments. A uniform coordinatewise ℓ¹
residual bound and the Euclidean variance of each finite increment family
give the expected Bernoulli supremum. All hypotheses are deterministic
properties of the proposed approximation; no concentration theorem is
assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

/-- Bernoulli absolute supremum over an arbitrary index class. -/
noncomputable def bernoulliAbsoluteSupremum {T : Type*} {m : ℕ}
    (z : T → Fin m → ℝ) (σ : Fin m → Bool) : ℝ :=
  sSup (Set.range fun t => |∑ i, finiteBernoulliSign (σ i) * z t i|)

/-- Deterministic chaining: each finite increment family contributes its
maximum, while the residual contributes its uniform ℓ¹ error. -/
theorem bernoulliAbsoluteSupremum_le_finiteChain
    {T L : Type*} [Nonempty T] [Fintype L] {m : ℕ}
    {J : L → Type*} [∀ l, Fintype (J l)] [∀ l, Nonempty (J l)]
    (z : T → Fin m → ℝ) (a : ∀ l, J l → Fin m → ℝ)
    (choose : ∀ l, T → J l) {ε : ℝ}
    (happrox : ∀ t, ∑ i, |z t i - ∑ l, a l (choose l t) i| ≤ ε)
    (σ : Fin m → Bool) :
    bernoulliAbsoluteSupremum z σ ≤ ε +
      ∑ l, finiteProcessAbsoluteMaximum
        (fun j (σ : Fin m → Bool) => ∑ i, finiteBernoulliSign (σ i) * a l j i) σ := by
  classical
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨t, rfl⟩
  dsimp only
  have hres : |∑ i, finiteBernoulliSign (σ i) *
      (z t i - ∑ l, a l (choose l t) i)| ≤ ε := by
    calc
      _ ≤ ∑ i, |finiteBernoulliSign (σ i) *
          (z t i - ∑ l, a l (choose l t) i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |z t i - ∑ l, a l (choose l t) i| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul]
        have hs : |finiteBernoulliSign (σ i)| = 1 := by
          cases σ i <;> norm_num [finiteBernoulliSign]
        rw [hs, one_mul]
      _ ≤ ε := happrox t
  have hdecomp : (∑ i, finiteBernoulliSign (σ i) * z t i) =
      (∑ i, finiteBernoulliSign (σ i) * (z t i - ∑ l, a l (choose l t) i)) +
      ∑ l, ∑ i, finiteBernoulliSign (σ i) * a l (choose l t) i := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    ring
  rw [hdecomp]
  calc
    _ ≤ |∑ i, finiteBernoulliSign (σ i) *
        (z t i - ∑ l, a l (choose l t) i)| +
        |∑ l, ∑ i, finiteBernoulliSign (σ i) * a l (choose l t) i| :=
      abs_add_le _ _
    _ ≤ ε + ∑ l, |∑ i, finiteBernoulliSign (σ i) * a l (choose l t) i| :=
      add_le_add hres (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := add_le_add le_rfl (Finset.sum_le_sum fun l _ =>
      abs_process_le_absoluteMaximum
        (fun j (τ : Fin m → Bool) => ∑ i, finiteBernoulliSign (τ i) * a l j i)
        (choose l t) σ)

/-- A finite multiscale approximation gives the square-root entropy sum for
the expected supremum of an arbitrary Bernoulli class. -/
theorem finiteBernoulli_chaining_expectation_le
    {T L : Type*} [Nonempty T] [Fintype L] {m : ℕ}
    {J : L → Type*} [∀ l, Fintype (J l)] [∀ l, Nonempty (J l)]
    (z : T → Fin m → ℝ) (a : ∀ l, J l → Fin m → ℝ)
    (choose : ∀ l, T → J l) {ε : ℝ} (V : L → ℝ)
    (happrox : ∀ t, ∑ i, |z t i - ∑ l, a l (choose l t) i| ≤ ε)
    (hvariance : ∀ l j, ∑ i, a l j i ^ 2 ≤ V l) :
    finiteAverage (bernoulliAbsoluteSupremum z) ≤ ε +
      ∑ l, Real.sqrt (2 * V l * Real.log (2 * (Fintype.card (J l) : ℝ))) := by
  calc
    _ ≤ finiteAverage (fun σ : Fin m → Bool => ε +
        ∑ l, finiteProcessAbsoluteMaximum
          (fun j (σ : Fin m → Bool) => ∑ i, finiteBernoulliSign (σ i) * a l j i) σ) :=
      finiteAverage_mono (bernoulliAbsoluteSupremum_le_finiteChain z a choose happrox)
    _ = ε + ∑ l, finiteAverage (finiteProcessAbsoluteMaximum
        (fun j (σ : Fin m → Bool) => ∑ i, finiteBernoulliSign (σ i) * a l j i)) := by
      rw [finiteAverage_add, finiteAverage_const, finiteAverage_sum]
    _ ≤ _ := add_le_add le_rfl (Finset.sum_le_sum fun l _ =>
      finiteBernoulli_absoluteMaximum_expectation_sqrt_bound (a l) (hvariance l))

end LeanNumDetect.FiniteMatrixSampling
