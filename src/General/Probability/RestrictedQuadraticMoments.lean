import General.Probability.SamplingConvexOrder
import General.Probability.FiniteLaplace
import General.Probability.FinitePopulationReindex
import Mathlib.Analysis.Convex.Mul

/-!
# Restricted quadratic moments under finite-population sampling

The absolute supremum of a bounded family of real linear tests is convex.
Its natural powers remain convex, including after affine centering and
normalization. Applying finite-population convex order therefore compares
every such moment for sampling without replacement with the corresponding
moment for independent sampling with replacement.

For matrices, the tests are the real quadratic forms `H ↦ ⟪x, H x⟫` for
vectors in a prescribed restricted class. Linearity here is in `H`, not in
`x`; the test class can be infinite. Pointwise boundedness is the only
assumption needed on that class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators InnerProductSpace
open Matrix

namespace LeanNumDetect.FiniteMatrixSampling

section RestrictedSupremum

variable {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [Nonempty ι]

/-- The absolute supremum of a family of real linear tests. Its useful
properties require the family to be bounded on each vector. -/
noncomputable def restrictedAbsoluteSup (φ : ι → E →ₗ[ℝ] ℝ) (v : E) : ℝ :=
  sSup (Set.range fun i => |φ i v|)

omit [Nonempty ι] in
theorem abs_linearTest_le_restrictedAbsoluteSup (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|)) (i : ι) (v : E) :
    |φ i v| ≤ restrictedAbsoluteSup φ v :=
  le_csSup (hbounded v) ⟨i, rfl⟩

theorem restrictedAbsoluteSup_nonneg (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|)) (v : E) :
    0 ≤ restrictedAbsoluteSup φ v := by
  let i : ι := Classical.choice inferInstance
  exact (abs_nonneg (φ i v)).trans
    (abs_linearTest_le_restrictedAbsoluteSup φ hbounded i v)

/-- A possibly infinite bounded family of linear tests defines a convex
absolute supremum. No topological compactness or finiteness is required. -/
theorem convexOn_restrictedAbsoluteSup (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|)) :
    ConvexOn ℝ Set.univ (restrictedAbsoluteSup φ) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨i, rfl⟩
  simp only [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
  calc
    |a * φ i x + b * φ i y| ≤ |a * φ i x| + |b * φ i y| := abs_add_le _ _
    _ = a * |φ i x| + b * |φ i y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * restrictedAbsoluteSup φ x + b * restrictedAbsoluteSup φ y :=
      add_le_add (mul_le_mul_of_nonneg_left
        (abs_linearTest_le_restrictedAbsoluteSup φ hbounded i x) ha)
        (mul_le_mul_of_nonneg_left
        (abs_linearTest_le_restrictedAbsoluteSup φ hbounded i y) hb)

/-- Every natural moment of the restricted absolute supremum is convex. -/
theorem convexOn_restrictedAbsoluteSup_pow (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|)) (p : ℕ) :
    ConvexOn ℝ Set.univ (fun v => restrictedAbsoluteSup φ v ^ p) := by
  exact (convexOn_restrictedAbsoluteSup φ hbounded).pow
    (fun v _ => restrictedAbsoluteSup_nonneg φ hbounded v) p

/-- Affine centering and normalization preserve convexity of restricted
moments. The affine map can have an arbitrary source real vector space. -/
theorem convexOn_affine_restrictedAbsoluteSup_pow (φ : ι → F →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|))
    (T : E →ᵃ[ℝ] F) (p : ℕ) :
    ConvexOn ℝ Set.univ (fun v => restrictedAbsoluteSup φ (T v) ^ p) := by
  simpa only [Set.preimage_univ, Function.comp_def] using
    (convexOn_restrictedAbsoluteSup_pow φ hbounded p).comp_affineMap T

end RestrictedSupremum

section MomentComparison

variable {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [Nonempty ι]

/-- The moment of any affine image of a restricted linear-test supremum
under uniform fixed-size sampling is at most its independent-sampling
counterpart. The result includes the empty-sample case. -/
theorem sampling_withoutReplacement_affine_restrictedMoment_le {N m : ℕ}
    (hmN : m ≤ N) (X : Fin N → E) (φ : ι → F →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|))
    (T : E →ᵃ[ℝ] F) (p : ℕ) :
    finiteAverage (fun Ω : Sample N m =>
      restrictedAbsoluteSup φ (T (∑ k ∈ Ω.val, X k)) ^ p) ≤
    finiteAverage (fun ω : Fin m → Fin N =>
      restrictedAbsoluteSup φ (T (∑ i, X (ω i))) ^ p) :=
  sampling_withoutReplacement_convex_le hmN X
    (convexOn_affine_restrictedAbsoluteSup_pow φ hbounded T p)

/-- Sampling without replacement decreases every natural moment of the
restricted deviation of a normalized sample sum from a fixed center. -/
theorem sampling_withoutReplacement_centered_restrictedMoment_le {N m : ℕ}
    (hmN : m ≤ N) (X : Fin N → E) (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|))
    (r : ℝ) (center : E) (p : ℕ) :
    finiteAverage (fun Ω : Sample N m =>
      restrictedAbsoluteSup φ (r • (∑ k ∈ Ω.val, X k) - center) ^ p) ≤
    finiteAverage (fun ω : Fin m → Fin N =>
      restrictedAbsoluteSup φ (r • (∑ i, X (ω i)) - center) ^ p) := by
  let T : E →ᵃ[ℝ] E :=
    r • (LinearMap.id : E →ₗ[ℝ] E).toAffineMap - AffineMap.const ℝ E center
  exact sampling_withoutReplacement_affine_restrictedMoment_le
    hmN X φ hbounded T p

/-- Fixed-size sample-average deviations have no larger natural moments
than the deviations of independent sample averages, for any bounded
family of real linear tests. -/
theorem sampling_withoutReplacement_restrictedMoment_le {N m : ℕ}
    (hmN : m ≤ N) (X : Fin N → E) (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|))
    (center : E) (p : ℕ) :
    finiteAverage (fun Ω : Sample N m =>
      restrictedAbsoluteSup φ ((m : ℝ)⁻¹ • (∑ k ∈ Ω.val, X k) - center) ^ p) ≤
    finiteAverage (fun ω : Fin m → Fin N =>
      restrictedAbsoluteSup φ ((m : ℝ)⁻¹ • (∑ i, X (ω i)) - center) ^ p) :=
  sampling_withoutReplacement_centered_restrictedMoment_le
    hmN X φ hbounded (m : ℝ)⁻¹ center p

end MomentComparison

section FiniteLabels

variable {κ E F ι : Type*} [Fintype κ]
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Finite-population convex comparison for the actual labels of an
arbitrary finite population, obtained by relabelling both sample laws. -/
theorem finiteSampling_withoutReplacement_convex_le {m : ℕ}
    (hm : m ≤ Fintype.card κ) (X : κ → E) {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) :
    finiteAverage (fun Ω : FiniteSample κ m => f (∑ k ∈ Ω.val, X k)) ≤
    finiteAverage (fun ω : Fin m → κ => f (∑ i, X (ω i))) := by
  let e := (Fintype.equivFin κ).symm
  have hleft :
      finiteAverage (fun Ω : Sample (Fintype.card κ) m =>
        f (∑ k ∈ Ω.val, X (e k))) =
      finiteAverage (fun Ω : FiniteSample κ m => f (∑ k ∈ Ω.val, X k)) := by
    calc
      _ = finiteAverage (fun Ω : Sample (Fintype.card κ) m =>
          f (∑ k ∈ (finiteSampleEquiv e m Ω).val, X k)) := by
        apply finiteAverage_congr
        intro Ω
        simp only [finiteSampleEquiv_val, Finset.sum_map, Equiv.toEmbedding_apply]
      _ = _ := finiteAverage_comp_equiv (finiteSampleEquiv e m)
        (fun Ω : FiniteSample κ m => f (∑ k ∈ Ω.val, X k))
  have hright :
      finiteAverage (fun ω : Fin m → Fin (Fintype.card κ) =>
        f (∑ i, X (e (ω i)))) =
      finiteAverage (fun ω : Fin m → κ => f (∑ i, X (ω i))) := by
    exact finiteAverage_comp_equiv (Equiv.piCongrRight fun _ : Fin m => e)
      (fun ω : Fin m → κ => f (∑ i, X (ω i)))
  rw [← hleft, ← hright]
  exact sampling_withoutReplacement_convex_le hm (fun k => X (e k)) hf

/-- Relabelling preserves the affine restricted-moment comparison. -/
theorem finiteSample_affine_restrictedMoment_le {m : ℕ} [Nonempty ι]
    (hm : m ≤ Fintype.card κ) (X : κ → E) (φ : ι → F →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|))
    (T : E →ᵃ[ℝ] F) (p : ℕ) :
    finiteAverage (fun Ω : FiniteSample κ m =>
      restrictedAbsoluteSup φ (T (∑ k ∈ Ω.val, X k)) ^ p) ≤
    finiteAverage (fun ω : Fin m → κ =>
      restrictedAbsoluteSup φ (T (∑ i, X (ω i))) ^ p) :=
  finiteSampling_withoutReplacement_convex_le hm X
    (convexOn_affine_restrictedAbsoluteSup_pow φ hbounded T p)

/-- Restricted sample-average moments for arbitrary finite population
labels, with the actual uniformly sampled subsets as outcomes. -/
theorem finiteSample_restrictedMoment_le {m : ℕ} [Nonempty ι]
    (hm : m ≤ Fintype.card κ) (X : κ → E) (φ : ι → E →ₗ[ℝ] ℝ)
    (hbounded : ∀ v, BddAbove (Set.range fun i => |φ i v|))
    (center : E) (p : ℕ) :
    finiteAverage (fun Ω : FiniteSample κ m =>
      restrictedAbsoluteSup φ ((m : ℝ)⁻¹ • (∑ k ∈ Ω.val, X k) - center) ^ p) ≤
    finiteAverage (fun ω : Fin m → κ =>
      restrictedAbsoluteSup φ ((m : ℝ)⁻¹ • (∑ i, X (ω i)) - center) ^ p) := by
  let T : E →ᵃ[ℝ] E :=
    (m : ℝ)⁻¹ • (LinearMap.id : E →ₗ[ℝ] E).toAffineMap - AffineMap.const ℝ E center
  exact finiteSample_affine_restrictedMoment_le hm X φ hbounded T p

end FiniteLabels

section MomentProbability

variable {α : Type*} [Fintype α]

/-- A natural moment bound controls the strict upper tail in the finite
uniform counting model. The zeroth moment is also included. -/
theorem probability_upperTail_le_of_finiteMoment (Z : α → ℝ)
    (hZ : ∀ ω, 0 ≤ Z ω) (p : ℕ) {ρ η : ℝ} (hρ : 0 < ρ)
    (hmoment : finiteAverage (fun ω => Z ω ^ p) ≤ η * ρ ^ p) :
    probability (fun ω => ρ < Z ω) ≤ η := by
  have hp : 0 < ρ ^ p := pow_pos hρ p
  calc
    probability (fun ω => ρ < Z ω) ≤
        finiteAverage (fun ω => Z ω ^ p) / ρ ^ p :=
      probability_le_finiteAverage_div (fun ω => ρ < Z ω)
        (fun ω => Z ω ^ p) hp (fun ω => pow_nonneg (hZ ω) p)
        (fun ω hω => pow_le_pow_left₀ hρ.le hω.le p)
    _ ≤ (η * ρ ^ p) / ρ ^ p := div_le_div_of_nonneg_right hmoment hp.le
    _ = η := mul_div_cancel_right₀ η hp.ne'

/-- Markov's inequality turns a finite natural-moment estimate into the
success probability `Z ≤ ρ`, with the threshold boundary retained. -/
theorem probability_ge_one_sub_of_finiteMoment [Nonempty α] (Z : α → ℝ)
    (hZ : ∀ ω, 0 ≤ Z ω) (p : ℕ) {ρ η : ℝ} (hρ : 0 < ρ)
    (hmoment : finiteAverage (fun ω => Z ω ^ p) ≤ η * ρ ^ p) :
    1 - η ≤ probability (fun ω => Z ω ≤ ρ) := by
  have htail := probability_upperTail_le_of_finiteMoment Z hZ p hρ hmoment
  have hcomp := probability_not (fun ω => Z ω ≤ ρ)
  simp only [not_le] at hcomp
  linarith

end MomentProbability

section QuadraticTests

variable {d : ℕ} {ι : Type*}

/-- A real quadratic form at a fixed complex vector is a real linear test
on the matrix variable. The matrix need not be Hermitian. -/
noncomputable def quadraticTestLinearMap (x : EuclideanSpace ℂ (Fin d)) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ where
  toFun A := quadratic A x
  map_add' A B := by
    unfold quadratic
    have he : (A + B).toEuclideanLin x = A.toEuclideanLin x + B.toEuclideanLin x := by
      change WithLp.toLp 2 ((A + B) *ᵥ WithLp.ofLp x) = _
      rw [Matrix.add_mulVec, WithLp.toLp_add]
      rfl
    rw [he, inner_add_right, Complex.add_re]
  map_smul' r A := by
    change quadratic ((r : ℂ) • A) x = r * quadratic A x
    exact quadratic_smul_matrix A r x

@[simp] theorem quadraticTestLinearMap_apply (x : EuclideanSpace ℂ (Fin d))
    (A : Matrix (Fin d) (Fin d) ℂ) : quadraticTestLinearMap x A = quadratic A x := rfl

/-- An arbitrary family in the Euclidean unit ball gives a pointwise
bounded family of quadratic tests, even when its index set is infinite. -/
theorem quadraticTests_bddAbove (x : ι → EuclideanSpace ℂ (Fin d))
    (hx : ∀ i, ‖x i‖ ≤ 1) (A : Matrix (Fin d) (Fin d) ℂ) :
    BddAbove (Set.range fun i => |quadraticTestLinearMap (x i) A|) := by
  have hc : Continuous (fun z : EuclideanSpace ℂ (Fin d) => |quadratic A z|) := by
    unfold quadratic
    fun_prop
  apply ((isCompact_closedBall (0 : EuclideanSpace ℂ (Fin d)) 1).bddAbove_image
    hc.continuousOn).mono
  rintro _ ⟨i, rfl⟩
  exact ⟨x i, by simpa using hx i, rfl⟩

/-- Absolute restricted quadratic deviation for an indexed vector class. -/
noncomputable def restrictedQuadraticSup (x : ι → EuclideanSpace ℂ (Fin d))
    (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  restrictedAbsoluteSup (fun i => quadraticTestLinearMap (x i)) A

/-- The complete moment comparison for arbitrary restricted unit-ball
quadratic forms and uniform samples of exactly `m` distinct matrices. -/
theorem sampling_withoutReplacement_restrictedQuadraticMoment_le {N m : ℕ}
    [Nonempty ι] (hmN : m ≤ N) (X : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (x : ι → EuclideanSpace ℂ (Fin d)) (hx : ∀ i, ‖x i‖ ≤ 1)
    (center : Matrix (Fin d) (Fin d) ℂ) (p : ℕ) :
    finiteAverage (fun Ω : Sample N m =>
      restrictedQuadraticSup x ((m : ℝ)⁻¹ • (∑ k ∈ Ω.val, X k) - center) ^ p) ≤
    finiteAverage (fun ω : Fin m → Fin N =>
      restrictedQuadraticSup x ((m : ℝ)⁻¹ • (∑ i, X (ω i)) - center) ^ p) :=
  sampling_withoutReplacement_restrictedMoment_le hmN X
    (fun i => quadraticTestLinearMap (x i)) (quadraticTests_bddAbove x hx) center p

/-- The restricted quadratic moment comparison on the original finite
population labels, without choosing an enumeration in the statement. -/
theorem finiteSample_restrictedQuadraticMoment_le {κ : Type*} [Fintype κ]
    {m : ℕ} [Nonempty ι] (hm : m ≤ Fintype.card κ)
    (X : κ → Matrix (Fin d) (Fin d) ℂ)
    (x : ι → EuclideanSpace ℂ (Fin d)) (hx : ∀ i, ‖x i‖ ≤ 1)
    (center : Matrix (Fin d) (Fin d) ℂ) (p : ℕ) :
    finiteAverage (fun Ω : FiniteSample κ m =>
      restrictedQuadraticSup x ((m : ℝ)⁻¹ • (∑ k ∈ Ω.val, X k) - center) ^ p) ≤
    finiteAverage (fun ω : Fin m → κ =>
      restrictedQuadraticSup x ((m : ℝ)⁻¹ • (∑ i, X (ω i)) - center) ^ p) :=
  finiteSample_restrictedMoment_le hm X
    (fun i => quadraticTestLinearMap (x i)) (quadraticTests_bddAbove x hx) center p

end QuadraticTests

end LeanNumDetect.FiniteMatrixSampling
