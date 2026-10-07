import General.Probability.RestrictedQuadraticMoments

/-! Finite-law symmetrization for arbitrary bounded families of real linear
tests. The target index class can be infinite. No probabilistic concentration
or entropy estimate is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

section AbsoluteSup

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Nonempty ι]

theorem restrictedAbsoluteSup_add_le (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|)) (x y : E) :
    restrictedAbsoluteSup φ (x + y) ≤
      restrictedAbsoluteSup φ x + restrictedAbsoluteSup φ y := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨i, rfl⟩
  change |φ i (x + y)| ≤ _
  rw [map_add]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_linearTest_le_restrictedAbsoluteSup φ hbounded i x)
    (abs_linearTest_le_restrictedAbsoluteSup φ hbounded i y))

omit [Nonempty ι] in
theorem restrictedAbsoluteSup_neg (φ : ι → E →ₗ[ℝ] ℝ) (x : E) :
    restrictedAbsoluteSup φ (-x) = restrictedAbsoluteSup φ x := by
  simp only [restrictedAbsoluteSup, map_neg, abs_neg]

theorem restrictedAbsoluteSup_sub_le (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|)) (x y : E) :
    restrictedAbsoluteSup φ (x - y) ≤
      restrictedAbsoluteSup φ x + restrictedAbsoluteSup φ y := by
  simpa only [sub_eq_add_neg, restrictedAbsoluteSup_neg] using
    restrictedAbsoluteSup_add_le φ hbounded x (-y)

end AbsoluteSup

theorem finiteAverage_add {α E : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E]
    (f g : α → E) :
    finiteAverage (fun x => f x + g x) = finiteAverage f + finiteAverage g := by
  simp only [finiteAverage, Finset.sum_add_distrib, smul_add]

theorem finiteAverage_sub {α E : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E]
    (f g : α → E) :
    finiteAverage (fun x => f x - g x) = finiteAverage f - finiteAverage g := by
  simp only [finiteAverage, Finset.sum_sub_distrib, smul_sub]

/-- Jensen introduces an independent copy of any finite random vector,
retaining an arbitrary bounded infinite family of linear tests. -/
theorem finiteAverage_centered_restrictedSup_le_copy
    {α E ι : Type*} [Fintype α] [Nonempty α]
    [AddCommGroup E] [Module ℝ E] [Nonempty ι]
    (Y : α → E) (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|)) :
    finiteAverage (fun ω => restrictedAbsoluteSup φ (Y ω - finiteAverage Y)) ≤
      finiteAverage (fun ω => finiteAverage (fun ω' =>
        restrictedAbsoluteSup φ (Y ω - Y ω'))) := by
  apply finiteAverage_mono
  intro ω
  have h := convex_finiteAverage_le (convexOn_restrictedAbsoluteSup φ hbounded)
    (fun ω' => Y ω - Y ω')
  simpa only [finiteAverage_sub, finiteAverage_const] using h

/-- The sign attached to one symmetric Bernoulli outcome. -/
def finiteBernoulliSign (b : Bool) : ℝ := if b then 1 else -1

/-- Swapping the members of each sampled pair is a permutation of the
product probability space. This is the exact finite-law exchangeability step. -/
def finiteSamplePairSwap {α : Type*} {m : ℕ} (σ : Fin m → Bool) :
    ((Fin m → α) × (Fin m → α)) ≃ ((Fin m → α) × (Fin m → α)) where
  toFun p := (fun i => if σ i then p.1 i else p.2 i,
    fun i => if σ i then p.2 i else p.1 i)
  invFun p := (fun i => if σ i then p.1 i else p.2 i,
    fun i => if σ i then p.2 i else p.1 i)
  left_inv p := by
    apply Prod.ext <;> funext i <;> cases h : σ i <;> simp [h]
  right_inv p := by
    apply Prod.ext <;> funext i <;> cases h : σ i <;> simp [h]

theorem finiteSamplePairSwap_sum_sub {α E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℕ} (X : α → E) (σ : Fin m → Bool)
    (p : (Fin m → α) × (Fin m → α)) :
    (∑ i, X ((finiteSamplePairSwap σ p).1 i)) -
        (∑ i, X ((finiteSamplePairSwap σ p).2 i)) =
      (∑ i, finiteBernoulliSign (σ i) • X (p.1 i)) -
        (∑ i, finiteBernoulliSign (σ i) • X (p.2 i)) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases h : σ i <;> simp [finiteSamplePairSwap, finiteBernoulliSign, h,
    sub_eq_add_neg, add_comm]

/-- Each fixed sign vector leaves the law of the independent-copy
difference unchanged, even though its distribution changes pointwise. -/
theorem finiteAverage_copyDifference_eq_signedDifference
    {α E : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E]
    {m : ℕ} (X : α → E) (f : E → ℝ) (r : ℝ) (σ : Fin m → Bool) :
    finiteAverage (fun p : (Fin m → α) × (Fin m → α) =>
      f (r • ((∑ i, X (p.1 i)) - ∑ i, X (p.2 i)))) =
    finiteAverage (fun p : (Fin m → α) × (Fin m → α) =>
      f (r • ((∑ i, finiteBernoulliSign (σ i) • X (p.1 i)) -
        ∑ i, finiteBernoulliSign (σ i) • X (p.2 i)))) := by
  rw [← finiteAverage_comp_equiv (finiteSamplePairSwap σ)
    (fun p : (Fin m → α) × (Fin m → α) =>
      f (r • ((∑ i, X (p.1 i)) - ∑ i, X (p.2 i))))]
  apply finiteAverage_congr
  intro p
  rw [finiteSamplePairSwap_sum_sub]

/-- Finite iid symmetrization for an arbitrary bounded linear-test class.
The same normalization `r` appears before and after symmetrization. -/
theorem finiteIid_restrictedSup_symmetrization
    {α E ι : Type*} [Fintype α] [Nonempty α]
    [AddCommGroup E] [Module ℝ E] [Nonempty ι] {m : ℕ}
    (X : α → E) (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|)) (r : ℝ) :
    finiteAverage (fun ω : Fin m → α => restrictedAbsoluteSup φ
      (r • (∑ i, X (ω i)) -
        finiteAverage (fun ω' : Fin m → α => r • (∑ i, X (ω' i))))) ≤
      2 * finiteAverage (fun σ : Fin m → Bool =>
        finiteAverage (fun ω : Fin m → α => restrictedAbsoluteSup φ
          (r • (∑ i, finiteBernoulliSign (σ i) • X (ω i))))) := by
  let Y := fun ω : Fin m → α => r • ∑ i, X (ω i)
  have hcopy := finiteAverage_centered_restrictedSup_le_copy Y φ hbounded
  have hghost : finiteAverage (fun ω : Fin m → α =>
      finiteAverage (fun ω' : Fin m → α => restrictedAbsoluteSup φ (Y ω - Y ω'))) =
      finiteAverage (fun p : (Fin m → α) × (Fin m → α) =>
        restrictedAbsoluteSup φ (r • ((∑ i, X (p.1 i)) - ∑ i, X (p.2 i)))) := by
    rw [finiteAverage_prod (fun (ω ω' : Fin m → α) =>
      restrictedAbsoluteSup φ (r • ((∑ i, X (ω i)) - ∑ i, X (ω' i))))]
    apply finiteAverage_congr
    intro ω
    apply finiteAverage_congr
    intro ω'
    simp only [Y, smul_sub]
  rw [hghost] at hcopy
  apply hcopy.trans
  calc
    _ = finiteAverage (fun σ : Fin m → Bool =>
        finiteAverage (fun p : (Fin m → α) × (Fin m → α) =>
          restrictedAbsoluteSup φ (r • ((∑ i, finiteBernoulliSign (σ i) • X (p.1 i)) -
            ∑ i, finiteBernoulliSign (σ i) • X (p.2 i))))) := by
      symm
      calc
        _ = finiteAverage (fun _σ : Fin m → Bool =>
            finiteAverage (fun p : (Fin m → α) × (Fin m → α) =>
              restrictedAbsoluteSup φ (r • ((∑ i, X (p.1 i)) - ∑ i, X (p.2 i))))) := by
          apply finiteAverage_congr
          intro σ
          exact (finiteAverage_copyDifference_eq_signedDifference X
            (restrictedAbsoluteSup φ) r σ).symm
        _ = _ := finiteAverage_const _
    _ ≤ finiteAverage (fun σ : Fin m → Bool =>
        finiteAverage (fun p : (Fin m → α) × (Fin m → α) =>
          restrictedAbsoluteSup φ (r • (∑ i, finiteBernoulliSign (σ i) • X (p.1 i))) +
            restrictedAbsoluteSup φ (r • (∑ i, finiteBernoulliSign (σ i) • X (p.2 i))))) := by
      apply finiteAverage_mono
      intro σ
      apply finiteAverage_mono
      intro p
      rw [smul_sub]
      exact restrictedAbsoluteSup_sub_le φ hbounded _ _
    _ = _ := by
      have heq (σ : Fin m → Bool) :
          finiteAverage (fun p : (Fin m → α) × (Fin m → α) =>
            restrictedAbsoluteSup φ (r • (∑ i, finiteBernoulliSign (σ i) • X (p.1 i))) +
              restrictedAbsoluteSup φ (r • (∑ i, finiteBernoulliSign (σ i) • X (p.2 i)))) =
          2 * finiteAverage (fun ω : Fin m → α => restrictedAbsoluteSup φ
            (r • (∑ i, finiteBernoulliSign (σ i) • X (ω i)))) := by
        rw [finiteAverage_prod (fun (ω ω' : Fin m → α) =>
          restrictedAbsoluteSup φ (r • (∑ i, finiteBernoulliSign (σ i) • X (ω i))) +
            restrictedAbsoluteSup φ (r • (∑ i, finiteBernoulliSign (σ i) • X (ω' i))))]
        simp only [finiteAverage_add, finiteAverage_const]
        ring
      simp_rw [heq]
      simpa only [smul_eq_mul] using finiteAverage_smul (α := Fin m → Bool) 2
        (fun σ => finiteAverage (fun ω : Fin m → α => restrictedAbsoluteSup φ
          (r • (∑ i, finiteBernoulliSign (σ i) • X (ω i)))))

end LeanNumDetect.FiniteMatrixSampling
