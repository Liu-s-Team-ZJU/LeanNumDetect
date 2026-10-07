import General.Probability.FiniteBernoulliProcess

/-! Deterministic variance ingredients for concentration of empirical-process
suprema. The nonnegative summands have a linear delete-one variance bound;
the lower-deviation supremum has a population replacement variance bound.
These statements do not assume a concentration theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.EmpiricalProcessReplacementVariance

/-- Maximum of a real-valued function on a nonempty finite set. -/
noncomputable def finiteMaximum {J : Type*} [Fintype J] (z : J → ℝ) : ℝ :=
  sSup (Set.range z)

theorem le_finiteMaximum {J : Type*} [Fintype J] (z : J → ℝ) (j : J) :
    z j ≤ finiteMaximum z :=
  le_csSup (Set.finite_range _).bddAbove ⟨j, rfl⟩

theorem finiteMaximum_attained {J : Type*} [Fintype J] [Nonempty J]
    (z : J → ℝ) : ∃ j, z j = finiteMaximum z := by
  exact (Set.range_nonempty z).csSup_mem (Set.finite_range z)

theorem finiteMaximum_mono {J : Type*} [Fintype J] [Nonempty J]
    {z w : J → ℝ} (h : ∀ j, z j ≤ w j) : finiteMaximum z ≤ finiteMaximum w := by
  obtain ⟨j, hj⟩ := finiteMaximum_attained z
  rw [← hj]
  exact (h j).trans (le_finiteMaximum w j)

/-- The unnormalized upper empirical-process supremum. The center may be any
fixed vector; probabilistic applications use the population means. -/
noncomputable def upperMaximum {J α : Type*} [Fintype J] {m : ℕ}
    (h : J → α → ℝ) (μ : J → ℝ) (x : Fin m → α) : ℝ :=
  finiteMaximum (fun j => (∑ i, h j (x i)) - (m : ℝ) * μ j)

/-- Delete one summand, while retaining the original population center. -/
noncomputable def upperDelete {J α : Type*} [Fintype J] {m : ℕ}
    (h : J → α → ℝ) (μ : J → ℝ) (x : Fin m → α) (i : Fin m) : ℝ :=
  finiteMaximum (fun j => (∑ k, h j (x k)) - (m : ℝ) * μ j - h j (x i))

/-- The unnormalized lower empirical-process supremum. -/
noncomputable def lowerMaximum {J α : Type*} [Fintype J] {m : ℕ}
    (h : J → α → ℝ) (μ : J → ℝ) (x : Fin m → α) : ℝ :=
  finiteMaximum (fun j => (m : ℝ) * μ j - ∑ i, h j (x i))

theorem upper_delete_difference_nonneg {J α : Type*} [Fintype J] [Nonempty J]
    {m : ℕ} (h : J → α → ℝ) (μ : J → ℝ) (x : Fin m → α)
    (h_nonneg : ∀ j y, 0 ≤ h j y) (i : Fin m) :
    0 ≤ upperMaximum h μ x - upperDelete h μ x i := by
  apply sub_nonneg.mpr
  apply finiteMaximum_mono
  intro j
  exact sub_le_self _ (h_nonneg j (x i))

/-- A single maximizing index bounds every delete-one difference at once. -/
theorem upper_delete_difference_le_maximizer {J α : Type*}
    [Fintype J] {m : ℕ} (h : J → α → ℝ) (μ : J → ℝ)
    (x : Fin m → α) (j : J)
    (hj : (∑ i, h j (x i)) - (m : ℝ) * μ j = upperMaximum h μ x)
    (i : Fin m) :
    upperMaximum h μ x - upperDelete h μ x i ≤ h j (x i) := by
  have hle := le_finiteMaximum
    (fun j => (∑ k, h j (x k)) - (m : ℝ) * μ j - h j (x i)) j
  change _ ≤ upperDelete h μ x i at hle
  linarith

/-- Weak self-bounding for nonnegative bounded empirical summands. In
particular the variance proxy scales with the row envelope `p`, not `p²`. -/
theorem upper_delete_variance_bound {J α : Type*} [Fintype J] [Nonempty J]
    {m : ℕ} (h : J → α → ℝ) (μ : J → ℝ) (x : Fin m → α)
    {p S : ℝ} (hp : 0 ≤ p) (h_nonneg : ∀ j y, 0 ≤ h j y)
    (h_bound : ∀ j y, h j y ≤ p) (h_mean : ∀ j, μ j ≤ S) :
    (∀ i, 0 ≤ upperMaximum h μ x - upperDelete h μ x i ∧
      upperMaximum h μ x - upperDelete h μ x i ≤ p) ∧
    (∑ i, (upperMaximum h μ x - upperDelete h μ x i)) ≤
      upperMaximum h μ x + (m : ℝ) * S ∧
    (∑ i, (upperMaximum h μ x - upperDelete h μ x i) ^ 2) ≤
      p * (upperMaximum h μ x + (m : ℝ) * S) := by
  obtain ⟨j, hj⟩ := finiteMaximum_attained
    (fun j => (∑ i, h j (x i)) - (m : ℝ) * μ j)
  change _ = upperMaximum h μ x at hj
  have hdiff (i : Fin m) :
      upperMaximum h μ x - upperDelete h μ x i ≤ h j (x i) :=
    upper_delete_difference_le_maximizer h μ x j hj i
  have hsum : (∑ i, (upperMaximum h μ x - upperDelete h μ x i)) ≤
      upperMaximum h μ x + (m : ℝ) * S := by
    calc
      _ ≤ ∑ i, h j (x i) := Finset.sum_le_sum fun i _ => hdiff i
      _ = upperMaximum h μ x + (m : ℝ) * μ j := by linarith [hj]
      _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
        (h_mean j) (Nat.cast_nonneg m))
  constructor
  · intro i
    exact ⟨upper_delete_difference_nonneg h μ x h_nonneg i,
      (hdiff i).trans (h_bound j (x i))⟩
  constructor
  · exact hsum
  calc
    _ ≤ ∑ i, p * (upperMaximum h μ x - upperDelete h μ x i) := by
      apply Finset.sum_le_sum
      intro i _
      have h0 := upper_delete_difference_nonneg h μ x h_nonneg i
      have h1 := (hdiff i).trans (h_bound j (x i))
      nlinarith
    _ = p * ∑ i, (upperMaximum h μ x - upperDelete h μ x i) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hp

theorem sum_after_coordinate_replacement {α : Type*} {m : ℕ}
    (f : α → ℝ) (x : Fin m → α) (i : Fin m) (y : α) :
    (∑ k, f (Function.update x i y k)) =
      (∑ k, f (x k)) - f (x i) + f y := by
  have hupdate : (fun k => f (Function.update x i y k)) =
      Function.update (fun k => f (x k)) i (f y) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk]
  rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hsum := Finset.sum_sdiff (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
    (f := fun k => f (x k))
  simp only [Finset.sum_singleton] at hsum
  linarith

/-- The same maximizing index can be used for every independent replacement.
For lower deviations, the positive difference is controlled by the new
nonnegative summand, which is independent of the original sample. -/
theorem lower_replacement_difference_le {J α : Type*} [Fintype J]
    {m : ℕ} (h : J → α → ℝ) (μ : J → ℝ) (x : Fin m → α)
    (j : J) (hj : (m : ℝ) * μ j - (∑ k, h j (x k)) = lowerMaximum h μ x)
    (i : Fin m) (y : α) :
    lowerMaximum h μ x - lowerMaximum h μ (Function.update x i y) ≤
      h j y - h j (x i) := by
  have hle := le_finiteMaximum
    (fun j => (m : ℝ) * μ j - ∑ k, h j (Function.update x i y k)) j
  change _ ≤ lowerMaximum h μ (Function.update x i y) at hle
  rw [sum_after_coordinate_replacement] at hle
  linarith

theorem lower_replacement_positive_difference_sq_le {J α : Type*} [Fintype J]
    {m : ℕ} (h : J → α → ℝ) (μ : J → ℝ) (x : Fin m → α)
    (h_nonneg : ∀ j y, 0 ≤ h j y)
    (j : J) (hj : (m : ℝ) * μ j - (∑ k, h j (x k)) = lowerMaximum h μ x)
    (i : Fin m) (y : α) :
    (max (lowerMaximum h μ x - lowerMaximum h μ (Function.update x i y)) 0) ^ 2 ≤
      h j y ^ 2 := by
  have hle := lower_replacement_difference_le h μ x j hj i y
  have hmax : max (lowerMaximum h μ x - lowerMaximum h μ (Function.update x i y)) 0 ≤
      h j y := max_le (by linarith [h_nonneg j (x i)]) (h_nonneg j y)
  have hn : 0 ≤ max (lowerMaximum h μ x -
      lowerMaximum h μ (Function.update x i y)) 0 := le_max_right _ _
  nlinarith [h_nonneg j y]

/-- Conditional replacement variance for a finite weighted population. No
cardinality of the class occurs in the bound. -/
theorem lower_replacement_variance_bound {J α : Type*}
    [Fintype J] [Nonempty J] [Fintype α] {m : ℕ}
    (h : J → α → ℝ) (μ : J → ℝ) (x : Fin m → α) (q : α → ℝ)
    {p S : ℝ} (hp : 0 ≤ p) (hq : ∀ y, 0 ≤ q y)
    (h_nonneg : ∀ j y, 0 ≤ h j y) (h_bound : ∀ j y, h j y ≤ p)
    (h_population : ∀ j, (∑ y, q y * h j y) ≤ S) :
    (∑ i, ∑ y, q y *
      (max (lowerMaximum h μ x - lowerMaximum h μ (Function.update x i y)) 0) ^ 2) ≤
      (m : ℝ) * p * S := by
  obtain ⟨j, hj⟩ := finiteMaximum_attained
    (fun j => (m : ℝ) * μ j - ∑ k, h j (x k))
  change _ = lowerMaximum h μ x at hj
  have hi (i : Fin m) : (∑ y, q y *
      (max (lowerMaximum h μ x - lowerMaximum h μ (Function.update x i y)) 0) ^ 2) ≤
      p * S := by
    calc
      _ ≤ ∑ y, q y * h j y ^ 2 := Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left
          (lower_replacement_positive_difference_sq_le h μ x h_nonneg j hj i y) (hq y)
      _ ≤ ∑ y, q y * (p * h j y) := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_mul_of_nonneg_left _ (hq y)
        nlinarith [h_nonneg j y, h_bound j y]
      _ = p * ∑ y, q y * h j y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ p * S := mul_le_mul_of_nonneg_left (h_population j) hp
  calc
    _ ≤ ∑ _i : Fin m, p * S := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp [mul_assoc]

/-- Maximum absolute centered empirical deviation. -/
noncomputable def absoluteMaximum {J α : Type*} [Fintype J] {m : ℕ}
    (h : J → α → ℝ) (μ : J → ℝ) (x : Fin m → α) : ℝ :=
  finiteMaximum (fun j => |(∑ i, h j (x i)) - (m : ℝ) * μ j|)

theorem absoluteMaximum_nonneg {J α : Type*} [Fintype J] [Nonempty J]
    {m : ℕ} (h : J → α → ℝ) (μ : J → ℝ) (x : Fin m → α) :
    0 ≤ absoluteMaximum h μ x := by
  obtain ⟨j, hj⟩ := finiteMaximum_attained
    (fun j => |(∑ i, h j (x i)) - (m : ℝ) * μ j|)
  change _ = absoluteMaximum h μ x at hj
  rw [← hj]
  exact abs_nonneg _

/-- A fixed maximizer and its sign determine all positive replacement
differences. This is the empirical-process counterpart of a one-sided
Efron--Stein variance proxy. -/
theorem absolute_replacement_positive_difference_sq_le {J α : Type*}
    [Fintype J] {m : ℕ} (h : J → α → ℝ) (μ : J → ℝ) (x : Fin m → α)
    (h_nonneg : ∀ j y, 0 ≤ h j y)
    (j : J) (hj : |(∑ k, h j (x k)) - (m : ℝ) * μ j| = absoluteMaximum h μ x)
    (i : Fin m) (y : α) :
    (max (absoluteMaximum h μ x - absoluteMaximum h μ (Function.update x i y)) 0)^2 ≤
      if 0 ≤ (∑ k, h j (x k)) - (m : ℝ) * μ j then h j (x i)^2 else h j y^2 := by
  have hle := le_finiteMaximum
    (fun j => |(∑ k, h j (Function.update x i y k)) - (m : ℝ) * μ j|) j
  change _ ≤ absoluteMaximum h μ (Function.update x i y) at hle
  rw [sum_after_coordinate_replacement] at hle
  have hmax0 : 0 ≤ max (absoluteMaximum h μ x -
      absoluteMaximum h μ (Function.update x i y)) 0 := le_max_right _ _
  by_cases hs : 0 ≤ (∑ k, h j (x k)) - (m : ℝ) * μ j
  · rw [if_pos hs]
    rw [abs_of_nonneg hs] at hj
    have hp := (le_abs_self ((∑ k, h j (x k)) - h j (x i) + h j y -
      (m : ℝ) * μ j)).trans hle
    have hdiff : absoluteMaximum h μ x -
        absoluteMaximum h μ (Function.update x i y) ≤ h j (x i) := by
      linarith [h_nonneg j y]
    have hmax := max_le hdiff (h_nonneg j (x i))
    nlinarith [h_nonneg j (x i)]
  · rw [if_neg hs]
    rw [abs_of_neg (lt_of_not_ge hs)] at hj
    have hm := (neg_le_abs ((∑ k, h j (x k)) - h j (x i) + h j y -
      (m : ℝ) * μ j)).trans hle
    have hdiff : absoluteMaximum h μ x -
        absoluteMaximum h μ (Function.update x i y) ≤ h j y := by
      linarith [h_nonneg j (x i)]
    have hmax := max_le hdiff (h_nonneg j y)
    nlinarith [h_nonneg j y]

/-- The variance proxy for the absolute empirical-process supremum has no
class-cardinality factor. The finite weights need only sum to one; zero
weights are allowed. -/
theorem absolute_replacement_variance_bound {J α : Type*}
    [Fintype J] [Nonempty J] [Fintype α] {m : ℕ}
    (h : J → α → ℝ) (μ : J → ℝ) (x : Fin m → α) (q : α → ℝ)
    {p S : ℝ} (hp : 0 ≤ p) (hq : ∀ y, 0 ≤ q y)
    (hqsum : ∑ y, q y = 1)
    (h_nonneg : ∀ j y, 0 ≤ h j y) (h_bound : ∀ j y, h j y ≤ p)
    (h_mean : ∀ j, μ j ≤ S) (h_population : ∀ j, (∑ y, q y * h j y) ≤ S) :
    (∑ i, ∑ y, q y *
      (max (absoluteMaximum h μ x - absoluteMaximum h μ (Function.update x i y)) 0)^2) ≤
      p * (absoluteMaximum h μ x + (m : ℝ) * S) := by
  obtain ⟨j, hj⟩ := finiteMaximum_attained
    (fun j => |(∑ k, h j (x k)) - (m : ℝ) * μ j|)
  change _ = absoluteMaximum h μ x at hj
  by_cases hs : 0 ≤ (∑ k, h j (x k)) - (m : ℝ) * μ j
  · have hi (i : Fin m) : (∑ y, q y *
        (max (absoluteMaximum h μ x -
          absoluteMaximum h μ (Function.update x i y)) 0)^2) ≤ p * h j (x i) := by
      calc
        _ ≤ ∑ y, q y * h j (x i)^2 := Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (by
            simpa only [if_pos hs] using
              absolute_replacement_positive_difference_sq_le h μ x h_nonneg j hj i y) (hq y)
        _ = h j (x i)^2 := by rw [← Finset.sum_mul, hqsum, one_mul]
        _ ≤ _ := by nlinarith [h_nonneg j (x i), h_bound j (x i)]
    rw [abs_of_nonneg hs] at hj
    have hsum : (∑ i, h j (x i)) ≤ absoluteMaximum h μ x + (m : ℝ) * S := by
      nlinarith [mul_le_mul_of_nonneg_left (h_mean j) (Nat.cast_nonneg m)]
    calc
      _ ≤ ∑ i, p * h j (x i) := Finset.sum_le_sum fun i _ => hi i
      _ = p * ∑ i, h j (x i) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hp
  · have hi (i : Fin m) : (∑ y, q y *
        (max (absoluteMaximum h μ x -
          absoluteMaximum h μ (Function.update x i y)) 0)^2) ≤ p * S := by
      calc
        _ ≤ ∑ y, q y * h j y^2 := Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (by
            simpa only [if_neg hs] using
              absolute_replacement_positive_difference_sq_le h μ x h_nonneg j hj i y) (hq y)
        _ ≤ ∑ y, q y * (p * h j y) := by
          apply Finset.sum_le_sum
          intro y _
          apply mul_le_mul_of_nonneg_left _ (hq y)
          nlinarith [h_nonneg j y, h_bound j y]
        _ = p * ∑ y, q y * h j y := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ ≤ p * S := mul_le_mul_of_nonneg_left (h_population j) hp
    calc
      _ ≤ ∑ _i : Fin m, p * S := Finset.sum_le_sum fun i _ => hi i
      _ = p * ((m : ℝ) * S) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        linarith [absoluteMaximum_nonneg h μ x]) hp

end LeanNumDetect.EmpiricalProcessReplacementVariance
