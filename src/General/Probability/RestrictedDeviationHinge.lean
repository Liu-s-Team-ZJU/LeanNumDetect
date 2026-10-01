import General.Probability.RestrictedQuadraticMoments

/-!
# Convex hinge transfer of restricted-deviation tails

A convex hinge, `max 0 (Z - t)`, transfers a bounded independent-sampling
tail estimate through finite-population convex order. This needs only one
expectation comparison: the tail for distinct samples at threshold `2t`
is at most `(B/t)` times the independent-sampling tail at threshold `t`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

/-- The nonnegative excess of a scalar deviation over a threshold. -/
def positiveDeviationHinge (t z : ℝ) : ℝ := max 0 (z - t)

theorem positiveDeviationHinge_nonneg (t z : ℝ) : 0 ≤ positiveDeviationHinge t z :=
  le_max_left _ _

/-- Applying a hinge to any convex real function preserves convexity. -/
theorem convexOn_positiveDeviationHinge {E : Type*} [AddCommGroup E] [Module ℝ E]
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (t : ℝ) :
    ConvexOn ℝ Set.univ (fun v => positiveDeviationHinge t (f v)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hfxy := hf.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hfxy
  simp only [positiveDeviationHinge, smul_eq_mul]
  apply max_le
  · exact add_nonneg (mul_nonneg ha (le_max_left _ _))
      (mul_nonneg hb (le_max_left _ _))
  · calc
      f (a • x + b • y) - t ≤ a * f x + b * f y - t := sub_le_sub_right hfxy t
      _ = a * (f x - t) + b * (f y - t) := by
        have ht : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
        linarith
      _ ≤ a * max 0 (f x - t) + b * max 0 (f y - t) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)

/-- The hinge of an affine restricted linear-test supremum is convex. -/
theorem convexOn_affine_restrictedDeviationHinge {E F ι : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] [Nonempty ι]
    (φ : ι → F →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|))
    (T : E →ᵃ[ℝ] F) (t : ℝ) :
    ConvexOn ℝ Set.univ
      (fun v => positiveDeviationHinge t (restrictedAbsoluteSup φ (T v))) := by
  apply convexOn_positiveDeviationHinge
  simpa only [pow_one] using convexOn_affine_restrictedAbsoluteSup_pow φ hbounded T 1

/-- Fixed-size sampling decreases the mean hinge of every affine
restricted linear-test deviation on the original population labels. -/
theorem finiteSample_restrictedDeviationHinge_le {κ E F ι : Type*} [Fintype κ]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] [Nonempty ι]
    {m : ℕ} (hm : m ≤ Fintype.card κ) (X : κ → E) (φ : ι → F →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|))
    (T : E →ᵃ[ℝ] F) (t : ℝ) :
    finiteAverage (fun Ω : FiniteSample κ m =>
      positiveDeviationHinge t (restrictedAbsoluteSup φ (T (∑ k ∈ Ω.val, X k)))) ≤
    finiteAverage (fun ω : Fin m → κ =>
      positiveDeviationHinge t (restrictedAbsoluteSup φ (T (∑ i, X (ω i))))) :=
  finiteSampling_withoutReplacement_convex_le hm X
    (convexOn_affine_restrictedDeviationHinge φ hbounded T t)

/-- A bounded scalar deviation has expected hinge at most its bound
times the upper-tail probability. -/
theorem finiteAverage_hinge_le_bound_mul_probability {α : Type*} [Fintype α]
    (Z : α → ℝ) {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B) (hbound : ∀ ω, Z ω ≤ B) :
    finiteAverage (fun ω => positiveDeviationHinge t (Z ω)) ≤
      B * probability (fun ω => t < Z ω) := by
  classical
  have hpoint (ω : α) : positiveDeviationHinge t (Z ω) ≤
      if t < Z ω then B else 0 := by
    by_cases hω : t < Z ω
    · simp only [if_pos hω, positiveDeviationHinge]
      exact max_le hB (by linarith [hbound ω])
    · simp only [if_neg hω, positiveDeviationHinge]
      exact max_le le_rfl (sub_nonpos.mpr (le_of_not_gt hω))
  calc
    finiteAverage (fun ω => positiveDeviationHinge t (Z ω)) ≤
        finiteAverage (fun ω => if t < Z ω then B else 0) := finiteAverage_mono hpoint
    _ = B * probability (fun ω => t < Z ω) := by
      unfold finiteAverage probability
      simp only [smul_eq_mul, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      ring

/-- A comparison of expected hinges transfers a bounded upper-tail
estimate between arbitrary finite outcome spaces. Only the independent
deviation needs an upper bound. -/
theorem probability_upperTail_le_of_hinge_comparison
    {α β : Type*} [Fintype α] [Fintype β]
    (Z : α → ℝ) (W : β → ℝ) {t B ε : ℝ} (ht : 0 < t) (hB : 0 ≤ B)
    (hbound : ∀ ω, W ω ≤ B)
    (hcompare : finiteAverage (fun ω => positiveDeviationHinge t (Z ω)) ≤
      finiteAverage (fun ω => positiveDeviationHinge t (W ω)))
    (htail : probability (fun ω => t < W ω) ≤ ε) :
    probability (fun ω => 2 * t < Z ω) ≤ (B / t) * ε := by
  have hmean : finiteAverage (fun ω => positiveDeviationHinge t (Z ω)) ≤ B * ε := by
    calc
      _ ≤ finiteAverage (fun ω => positiveDeviationHinge t (W ω)) := hcompare
      _ ≤ B * probability (fun ω => t < W ω) :=
        finiteAverage_hinge_le_bound_mul_probability W ht.le hB hbound
      _ ≤ B * ε := mul_le_mul_of_nonneg_left htail hB
  calc
    probability (fun ω => 2 * t < Z ω) ≤
        finiteAverage (fun ω => positiveDeviationHinge t (Z ω)) / t :=
      probability_le_finiteAverage_div (fun ω => 2 * t < Z ω)
        (fun ω => positiveDeviationHinge t (Z ω)) ht
        (fun ω => positiveDeviationHinge_nonneg t (Z ω)) (by
          intro ω hω
          exact (by linarith : t ≤ Z ω - t).trans (le_max_right _ _))
    _ ≤ (B * ε) / t := div_le_div_of_nonneg_right hmean ht.le
    _ = (B / t) * ε := by ring

/-- The hinge transfer in the equivalent success-probability form. -/
theorem probability_ge_one_sub_of_hinge_comparison
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (Z : α → ℝ) (W : β → ℝ) {t B ε : ℝ} (ht : 0 < t) (hB : 0 ≤ B)
    (hbound : ∀ ω, W ω ≤ B)
    (hcompare : finiteAverage (fun ω => positiveDeviationHinge t (Z ω)) ≤
      finiteAverage (fun ω => positiveDeviationHinge t (W ω)))
    (htail : probability (fun ω => t < W ω) ≤ ε) :
    1 - (B / t) * ε ≤ probability (fun ω => Z ω ≤ 2 * t) := by
  have htail' := probability_upperTail_le_of_hinge_comparison
    Z W ht hB hbound hcompare htail
  have hcomp := probability_not (fun ω => Z ω ≤ 2 * t)
  simp only [not_le] at hcomp
  linarith

/-- An independent restricted-deviation tail bound transfers to uniform
subsets of exactly `m` distinct population labels. -/
theorem finiteSample_restrictedDeviation_probability_le
    {κ E F ι : Type*} [Fintype κ] [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [Nonempty ι] {m : ℕ}
    (hm : m ≤ Fintype.card κ) (X : κ → E) (φ : ι → F →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|))
    (T : E →ᵃ[ℝ] F) {t B ε : ℝ} (ht : 0 < t) (hB : 0 ≤ B)
    (hbound : ∀ ω : Fin m → κ, restrictedAbsoluteSup φ (T (∑ i, X (ω i))) ≤ B)
    (htail : probability (fun ω : Fin m → κ =>
      t < restrictedAbsoluteSup φ (T (∑ i, X (ω i)))) ≤ ε) :
    probability (fun Ω : FiniteSample κ m =>
      2 * t < restrictedAbsoluteSup φ (T (∑ k ∈ Ω.val, X k))) ≤ (B / t) * ε :=
  probability_upperTail_le_of_hinge_comparison
    (fun Ω : FiniteSample κ m => restrictedAbsoluteSup φ (T (∑ k ∈ Ω.val, X k)))
    (fun ω : Fin m → κ => restrictedAbsoluteSup φ (T (∑ i, X (ω i))))
    ht hB hbound (finiteSample_restrictedDeviationHinge_le hm X φ hbounded T t) htail

/-- Success probability for the same restricted deviation under sampling
of exactly `m` distinct labels. Admissibility supplies a nonempty sample space. -/
theorem finiteSample_restrictedDeviation_probability_ge
    {κ E F ι : Type*} [Fintype κ] [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [Nonempty ι] {m : ℕ}
    (hm : m ≤ Fintype.card κ) (X : κ → E) (φ : ι → F →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|))
    (T : E →ᵃ[ℝ] F) {t B ε : ℝ} (ht : 0 < t) (hB : 0 ≤ B)
    (hbound : ∀ ω : Fin m → κ, restrictedAbsoluteSup φ (T (∑ i, X (ω i))) ≤ B)
    (htail : probability (fun ω : Fin m → κ =>
      t < restrictedAbsoluteSup φ (T (∑ i, X (ω i)))) ≤ ε) :
    1 - (B / t) * ε ≤ probability (fun Ω : FiniteSample κ m =>
      restrictedAbsoluteSup φ (T (∑ k ∈ Ω.val, X k)) ≤ 2 * t) := by
  letI : Nonempty (FiniteSample κ m) := finiteSample_nonempty hm
  exact probability_ge_one_sub_of_hinge_comparison
    (fun Ω : FiniteSample κ m => restrictedAbsoluteSup φ (T (∑ k ∈ Ω.val, X k)))
    (fun ω : Fin m → κ => restrictedAbsoluteSup φ (T (∑ i, X (ω i))))
    ht hB hbound (finiteSample_restrictedDeviationHinge_le hm X φ hbounded T t) htail

end LeanNumDetect.FiniteMatrixSampling
