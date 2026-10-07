import General.Probability.FiniteSymmetrization
import General.Probability.FiniteEntropy

/-! Symmetrization under an arbitrary finite probability law. The independent
samples use product weights, while the Bernoulli signs are uniform. The family
of bounded real linear tests is allowed to be infinite. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

open FiniteEntropy

/-- The expectation of a vector under finite real weights. -/
noncomputable def weightedVectorMean {α E : Type*} [Fintype α]
    [AddCommGroup E] [Module ℝ E] (q : α → ℝ) (Y : α → E) : E :=
  ∑ a, q a • Y a

theorem weightedVectorMean_const {α E : Type*} [Fintype α]
    [AddCommGroup E] [Module ℝ E] (q : α → ℝ) (hqs : ∑ a, q a = 1) (v : E) :
    weightedVectorMean q (fun _ => v) = v := by
  rw [weightedVectorMean, ← Finset.sum_smul, hqs, one_smul]

theorem weightedVectorMean_sub {α E : Type*} [Fintype α]
    [AddCommGroup E] [Module ℝ E] (q : α → ℝ) (Y Z : α → E) :
    weightedVectorMean q (fun a => Y a - Z a) =
      weightedVectorMean q Y - weightedVectorMean q Z := by
  simp only [weightedVectorMean, smul_sub, Finset.sum_sub_distrib]

theorem weightedVectorMean_smul {α E : Type*} [Fintype α]
    [AddCommGroup E] [Module ℝ E] (q : α → ℝ) (r : ℝ) (Y : α → E) :
    weightedVectorMean q (fun a => r • Y a) = r • weightedVectorMean q Y := by
  unfold weightedVectorMean
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact smul_comm (q a) r (Y a)

theorem linearMap_weightedVectorMean {α E : Type*} [Fintype α]
    [AddCommGroup E] [Module ℝ E] (q : α → ℝ) (Y : α → E) (φ : E →ₗ[ℝ] ℝ) :
    φ (weightedVectorMean q Y) = weightedMean q (fun a => φ (Y a)) := by
  simp only [weightedVectorMean, map_sum, map_smul, weightedMean, smul_eq_mul]

theorem weightedVectorMean_add {α E : Type*} [Fintype α]
    [AddCommGroup E] [Module ℝ E] (q : α → ℝ) (Y Z : α → E) :
    weightedVectorMean q (fun a => Y a + Z a) =
      weightedVectorMean q Y + weightedVectorMean q Z := by
  simp only [weightedVectorMean, smul_add, Finset.sum_add_distrib]

theorem weightedVectorMean_sum {α J E : Type*} [Fintype α] [Fintype J]
    [AddCommGroup E] [Module ℝ E] (q : α → ℝ) (Y : J → α → E) :
    weightedVectorMean q (fun a => ∑ j, Y j a) = ∑ j, weightedVectorMean q (Y j) := by
  simp only [weightedVectorMean, Finset.smul_sum]
  rw [Finset.sum_comm]

/-- Product-law conditioning at the first coordinate, for vector expectations. -/
theorem weightedVectorMean_product_succ {α E : Type*} [Fintype α]
    [AddCommGroup E] [Module ℝ E] (q : α → ℝ) {m : ℕ}
    (Y : (Fin (m + 1) → α) → E) :
    weightedVectorMean (productWeight q) Y =
      weightedVectorMean q (fun a => weightedVectorMean (productWeight q)
        (fun x => Y (Fin.cons a x))) := by
  let e := Fin.consEquiv (fun _ : Fin (m + 1) => α)
  unfold weightedVectorMean
  rw [← e.sum_comp (fun x => productWeight q x • Y x), Fintype.sum_prod_type]
  simp only [e, Fin.consEquiv_apply, productWeight, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.smul_sum, mul_smul]
  rfl

/-- The mean of an iid sum equals the number of samples times the one-sample mean. -/
theorem weightedVectorMean_iid_sum {α E : Type*} [Fintype α]
    [AddCommGroup E] [Module ℝ E] (q : α → ℝ) (hqs : ∑ a, q a = 1)
    (X : α → E) (m : ℕ) :
    weightedVectorMean (productWeight q) (fun ω : Fin m → α => ∑ i, X (ω i)) =
      (m : ℝ) • weightedVectorMean q X := by
  induction m with
  | zero => simp [weightedVectorMean]
  | succ m ih =>
    rw [weightedVectorMean_product_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      weightedVectorMean_add, weightedVectorMean_const _ (productWeight_sum q hqs m),
      ih, weightedVectorMean_const q hqs]
    rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_comm]

/-- Uniform sign averaging commutes with an arbitrary finite weighted mean. -/
theorem finiteAverage_weightedMean_comm {α β : Type*} [Fintype α] [Fintype β]
    (q : β → ℝ) (f : α → β → ℝ) :
    finiteAverage (fun a => weightedMean q (f a)) =
      weightedMean q (fun b => finiteAverage (fun a => f a b)) := by
  simp only [finiteAverage, weightedMean, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Jensen's inequality with finite probability weights. -/
theorem convex_weightedVectorMean_le {α E : Type*} [Fintype α]
    [AddCommGroup E] [Module ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (q : α → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) (Y : α → E) :
    f (weightedVectorMean q Y) ≤ weightedMean q (fun a => f (Y a)) := by
  exact hf.map_sum_le (t := Finset.univ) (w := q) (p := Y)
    (fun a _ => hq a) hqs (fun _ _ => Set.mem_univ _)

/-- Averaging over a weighted product is iterated averaging. -/
theorem weightedMean_pair {α β : Type*} [Fintype α] [Fintype β]
    (q : α → ℝ) (r : β → ℝ) (f : α → β → ℝ) :
    weightedMean (fun p : α × β => q p.1 * r p.2) (fun p => f p.1 p.2) =
      weightedMean q (fun a => weightedMean r (f a)) := by
  simp only [weightedMean, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem weightedMean_add {α : Type*} [Fintype α] (q f g : α → ℝ) :
    weightedMean q (fun a => f a + g a) = weightedMean q f + weightedMean q g := by
  simp only [weightedMean, mul_add, Finset.sum_add_distrib]

/-- A weight-preserving permutation leaves a finite expectation unchanged. -/
theorem weightedMean_comp_equiv {α : Type*} [Fintype α]
    (q : α → ℝ) (e : α ≃ α) (hweight : ∀ a, q (e a) = q a) (f : α → ℝ) :
    weightedMean q (fun a => f (e a)) = weightedMean q f := by
  unfold weightedMean
  have h := e.sum_comp (fun a => q a * f a)
  simpa only [hweight] using h

/-- Independent-copy Jensen for a bounded, possibly infinite test family. -/
theorem weightedMean_centered_restrictedSup_le_copy
    {α E ι : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E] [Nonempty ι]
    (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    (Y : α → E) (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|)) :
    weightedMean q (fun ω => restrictedAbsoluteSup φ (Y ω - weightedVectorMean q Y)) ≤
      weightedMean q (fun ω => weightedMean q (fun ω' =>
        restrictedAbsoluteSup φ (Y ω - Y ω'))) := by
  apply weightedMean_mono hq
  intro ω
  have h := convex_weightedVectorMean_le
    (convexOn_restrictedAbsoluteSup φ hbounded) q hq hqs (fun ω' => Y ω - Y ω')
  simpa only [weightedVectorMean_sub, weightedVectorMean_const q hqs] using h

/-- Swapping either member of each iid pair preserves the product weight. -/
theorem finiteSamplePairSwap_productWeight {α : Type*} (q : α → ℝ)
    {m : ℕ} (σ : Fin m → Bool) (p : (Fin m → α) × (Fin m → α)) :
    productWeight q (finiteSamplePairSwap σ p).1 *
        productWeight q (finiteSamplePairSwap σ p).2 =
      productWeight q p.1 * productWeight q p.2 := by
  unfold productWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases h : σ i <;> simp [finiteSamplePairSwap, h, mul_comm]

/-- Fixed signs leave the law of the weighted independent-copy difference
unchanged. Zero weights are allowed. -/
theorem weightedMean_copyDifference_eq_signedDifference
    {α E : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E]
    (q : α → ℝ) {m : ℕ} (X : α → E) (f : E → ℝ) (r : ℝ) (σ : Fin m → Bool) :
    weightedMean (fun p : (Fin m → α) × (Fin m → α) =>
      productWeight q p.1 * productWeight q p.2)
      (fun p => f (r • ((∑ i, X (p.1 i)) - ∑ i, X (p.2 i)))) =
    weightedMean (fun p : (Fin m → α) × (Fin m → α) =>
      productWeight q p.1 * productWeight q p.2)
      (fun p => f (r • ((∑ i, finiteBernoulliSign (σ i) • X (p.1 i)) -
        ∑ i, finiteBernoulliSign (σ i) • X (p.2 i)))) := by
  rw [← weightedMean_comp_equiv
    (fun p : (Fin m → α) × (Fin m → α) => productWeight q p.1 * productWeight q p.2)
    (finiteSamplePairSwap σ) (finiteSamplePairSwap_productWeight q σ)
    (fun p : (Fin m → α) × (Fin m → α) =>
      f (r • ((∑ i, X (p.1 i)) - ∑ i, X (p.2 i))))]
  unfold weightedMean
  apply Finset.sum_congr rfl
  intro p _
  change _ * f (r • ((∑ i, X ((finiteSamplePairSwap σ p).1 i)) -
    ∑ i, X ((finiteSamplePairSwap σ p).2 i))) = _
  rw [finiteSamplePairSwap_sum_sub]

/-- Finite iid symmetrization under arbitrary nonnegative probability weights.
The test family can be infinite; the factor and normalization are exactly the
usual `2` and the original `r`. -/
theorem weightedIid_restrictedSup_symmetrization
    {α E ι : Type*} [Fintype α] [AddCommGroup E] [Module ℝ E] [Nonempty ι] {m : ℕ}
    (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    (X : α → E) (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|)) (r : ℝ) :
    weightedMean (productWeight q) (fun ω : Fin m → α => restrictedAbsoluteSup φ
      (r • (∑ i, X (ω i)) -
        weightedVectorMean (productWeight q) (fun ω' : Fin m → α =>
          r • (∑ i, X (ω' i))))) ≤
      2 * finiteAverage (fun σ : Fin m → Bool =>
        weightedMean (productWeight q) (fun ω : Fin m → α => restrictedAbsoluteSup φ
          (r • (∑ i, finiteBernoulliSign (σ i) • X (ω i))))) := by
  let Q : (Fin m → α) → ℝ := productWeight q
  have hQ : ∀ ω, 0 ≤ Q ω := productWeight_nonneg q hq
  have hQs : ∑ ω, Q ω = 1 := productWeight_sum q hqs m
  let Y := fun ω : Fin m → α => r • ∑ i, X (ω i)
  have hcopy := weightedMean_centered_restrictedSup_le_copy Q hQ hQs Y φ hbounded
  have hghost : weightedMean Q (fun ω : Fin m → α =>
      weightedMean Q (fun ω' : Fin m → α => restrictedAbsoluteSup φ (Y ω - Y ω'))) =
      weightedMean (fun p : (Fin m → α) × (Fin m → α) => Q p.1 * Q p.2)
        (fun p => restrictedAbsoluteSup φ
          (r • ((∑ i, X (p.1 i)) - ∑ i, X (p.2 i)))) := by
    rw [weightedMean_pair Q Q (fun ω ω' : Fin m → α =>
      restrictedAbsoluteSup φ (r • ((∑ i, X (ω i)) - ∑ i, X (ω' i))))]
    congr 1
    funext ω
    congr 1
    funext ω'
    simp only [Y, smul_sub]
  rw [hghost] at hcopy
  apply hcopy.trans
  calc
    _ = finiteAverage (fun σ : Fin m → Bool =>
        weightedMean (fun p : (Fin m → α) × (Fin m → α) => Q p.1 * Q p.2)
          (fun p => restrictedAbsoluteSup φ (r •
            ((∑ i, finiteBernoulliSign (σ i) • X (p.1 i)) -
              ∑ i, finiteBernoulliSign (σ i) • X (p.2 i))))) := by
      symm
      calc
        _ = finiteAverage (fun _σ : Fin m → Bool =>
            weightedMean (fun p : (Fin m → α) × (Fin m → α) => Q p.1 * Q p.2)
              (fun p => restrictedAbsoluteSup φ
                (r • ((∑ i, X (p.1 i)) - ∑ i, X (p.2 i))))) := by
          apply finiteAverage_congr
          intro σ
          exact (weightedMean_copyDifference_eq_signedDifference q X
            (restrictedAbsoluteSup φ) r σ).symm
        _ = _ := finiteAverage_const _
    _ ≤ finiteAverage (fun σ : Fin m → Bool =>
        weightedMean (fun p : (Fin m → α) × (Fin m → α) => Q p.1 * Q p.2)
          (fun p =>
            restrictedAbsoluteSup φ (r • (∑ i, finiteBernoulliSign (σ i) • X (p.1 i))) +
              restrictedAbsoluteSup φ (r • (∑ i, finiteBernoulliSign (σ i) • X (p.2 i))))) := by
      apply finiteAverage_mono
      intro σ
      apply weightedMean_mono (fun p : (Fin m → α) × (Fin m → α) =>
        mul_nonneg (hQ p.1) (hQ p.2))
      intro p
      rw [smul_sub]
      exact restrictedAbsoluteSup_sub_le φ hbounded _ _
    _ = _ := by
      have heq (σ : Fin m → Bool) :
          weightedMean (fun p : (Fin m → α) × (Fin m → α) => Q p.1 * Q p.2)
            (fun p =>
              restrictedAbsoluteSup φ (r • (∑ i, finiteBernoulliSign (σ i) • X (p.1 i))) +
                restrictedAbsoluteSup φ (r • (∑ i, finiteBernoulliSign (σ i) • X (p.2 i)))) =
          2 * weightedMean Q (fun ω : Fin m → α => restrictedAbsoluteSup φ
            (r • (∑ i, finiteBernoulliSign (σ i) • X (ω i)))) := by
        rw [weightedMean_pair Q Q (fun ω ω' : Fin m → α =>
          restrictedAbsoluteSup φ (r • (∑ i, finiteBernoulliSign (σ i) • X (ω i))) +
            restrictedAbsoluteSup φ (r • (∑ i, finiteBernoulliSign (σ i) • X (ω' i))))]
        simp only [weightedMean_add, weightedMean_const Q hQs]
        ring
      simp_rw [heq]
      simpa only [smul_eq_mul] using finiteAverage_smul (α := Fin m → Bool) 2
        (fun σ => weightedMean Q (fun ω : Fin m → α => restrictedAbsoluteSup φ
          (r • (∑ i, finiteBernoulliSign (σ i) • X (ω i)))))

end LeanNumDetect.FiniteMatrixSampling
