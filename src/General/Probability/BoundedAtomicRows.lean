import General.Probability.RestrictedQuadraticMoments

/-!
# Finite bounded dictionaries and their restricted Gram deviations

Rows may be redundant and their full covariance need not be the identity.
The coefficient class combines a bounded `ℓ¹` mass with full mean energy at
most one. Its quadratic tests are pointwise bounded on every matrix, and its
empirical deviations are bounded by the coefficient radius squared plus one.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section

/-- Squared evaluation of one row of a finite complex dictionary. -/
def atomicRowEnergy {N Q : ℕ} (row : Fin N → Fin Q → ℂ) (k : Fin N)
    (x : EuclideanSpace ℂ (Fin Q)) : ℝ :=
  ‖∑ j, row k j * ofLp x j‖ ^ 2

/-- The rank-one Gram matrix associated with one dictionary row. -/
def atomicRowGram {N Q : ℕ} (row : Fin N → Fin Q → ℂ) (k : Fin N) :
    Matrix (Fin Q) (Fin Q) ℂ := fun i j => star (row k i) * row k j

/-- The Euclidean random vector representing the row in inner-product form. -/
def atomicRowVector {N Q : ℕ} (row : Fin N → Fin Q → ℂ) (k : Fin N) :
    EuclideanSpace ℂ (Fin Q) := toLp 2 (fun j => star (row k j))

@[simp] theorem atomicRowEnergy_zero {N Q : ℕ}
    (row : Fin N → Fin Q → ℂ) (k : Fin N) : atomicRowEnergy row k 0 = 0 := by
  simp [atomicRowEnergy]

theorem atomicRowEnergy_nonneg {N Q : ℕ} (row : Fin N → Fin Q → ℂ)
    (k : Fin N) (x : EuclideanSpace ℂ (Fin Q)) : 0 ≤ atomicRowEnergy row k x :=
  sq_nonneg _

/-- The external empirical-process normalization is exactly the row energy. -/
theorem norm_inner_atomicRowVector_sq {N Q : ℕ} (row : Fin N → Fin Q → ℂ)
    (k : Fin N) (x : EuclideanSpace ℂ (Fin Q)) :
    ‖⟪x, atomicRowVector row k⟫_ℂ‖ ^ 2 = atomicRowEnergy row k x := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change ‖∑ j, star (row k j) * star (ofLp x j)‖ ^ 2 = _
  rw [show (∑ j, star (row k j) * star (ofLp x j)) =
      star (∑ j, row k j * ofLp x j) by simp only [star_sum, star_mul, mul_comm]]
  simp only [norm_star, atomicRowEnergy]

@[simp] theorem norm_atomicRowVector_apply {N Q : ℕ}
    (row : Fin N → Fin Q → ℂ) (k : Fin N) (j : Fin Q) :
    ‖atomicRowVector row k j‖ = ‖row k j‖ := by
  change ‖star (row k j)‖ = _
  exact norm_star _

/-- The real quadratic form of the row Gram is exactly its squared evaluation. -/
theorem quadratic_atomicRowGram {N Q : ℕ} (row : Fin N → Fin Q → ℂ)
    (k : Fin N) (x : EuclideanSpace ℂ (Fin Q)) :
    quadratic (atomicRowGram row k) x = atomicRowEnergy row k x := by
  have he : star (ofLp x) ⬝ᵥ ((atomicRowGram row k) *ᵥ ofLp x) =
      star (∑ j, row k j * ofLp x j) * (∑ j, row k j * ofLp x j) := by
    simp only [dotProduct, Matrix.mulVec, atomicRowGram, Pi.star_apply,
      star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [quadratic, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change (star (ofLp x) ⬝ᵥ ((atomicRowGram row k) *ᵥ ofLp x)).re = _
  rw [he, RCLike.star_def, Complex.conj_mul']
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, atomicRowEnergy]

/-- Full mean energy, including the algebraic empty-population convention. -/
def atomicMeanEnergy {N Q : ℕ} (row : Fin N → Fin Q → ℂ)
    (x : EuclideanSpace ℂ (Fin Q)) : ℝ := finiteAverage (fun k => atomicRowEnergy row k x)

theorem atomicMeanEnergy_nonneg {N Q : ℕ} (row : Fin N → Fin Q → ℂ)
    (x : EuclideanSpace ℂ (Fin Q)) : 0 ≤ atomicMeanEnergy row x := by
  unfold atomicMeanEnergy finiteAverage
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun k _ => atomicRowEnergy_nonneg row k x)

@[simp] theorem atomicMeanEnergy_zero {N Q : ℕ} (row : Fin N → Fin Q → ℂ) :
    atomicMeanEnergy row 0 = 0 := by simp [atomicMeanEnergy, finiteAverage]

/-- Coefficients with bounded mass and full mean energy at most one. -/
def atomicCoefficientClass {N Q : ℕ} (S : ℝ) (row : Fin N → Fin Q → ℂ) :
    Set (EuclideanSpace ℂ (Fin Q)) :=
  {x | (∑ j, ‖ofLp x j‖) ≤ Real.sqrt S ∧ atomicMeanEnergy row x ≤ 1}

theorem zero_mem_atomicCoefficientClass {N Q : ℕ} (S : ℝ)
    (row : Fin N → Fin Q → ℂ) : 0 ∈ atomicCoefficientClass S row := by
  constructor
  · simp [Real.sqrt_nonneg S]
  · simp

/-- The coefficient class has a canonical witness at zero. -/
instance atomicCoefficientClass_nonempty {N Q : ℕ} (S : ℝ)
    (row : Fin N → Fin Q → ℂ) : Nonempty (atomicCoefficientClass S row) :=
  ⟨⟨0, zero_mem_atomicCoefficientClass S row⟩⟩

/-- A unit-bounded dictionary evaluates any member of the coefficient class
with energy at most its squared mass radius. -/
theorem atomicRowEnergy_le {N Q : ℕ} {S : ℝ} (hS : 0 ≤ S)
    (row : Fin N → Fin Q → ℂ) (hrow : ∀ k j, ‖row k j‖ ≤ 1)
    (k : Fin N) (x : atomicCoefficientClass S row) :
    atomicRowEnergy row k x.val ≤ S := by
  have hnorm : ‖∑ j, row k j * ofLp x.val j‖ ≤ Real.sqrt S := by
    calc
      _ ≤ ∑ j, ‖row k j * ofLp x.val j‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖ofLp x.val j‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (hrow k j) (norm_nonneg _)).trans_eq (one_mul _)
      _ ≤ _ := x.property.1
  exact ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg S)).2 hnorm).trans_eq
    (Real.sq_sqrt hS)

/-- The coefficient class is contained in the Euclidean ball of its mass radius. -/
theorem norm_mem_atomicCoefficientClass_le {N Q : ℕ} {S : ℝ}
    (row : Fin N → Fin Q → ℂ) (x : atomicCoefficientClass S row) :
    ‖x.val‖ ≤ Real.sqrt S := by
  have hsq : ‖x.val‖ ^ 2 ≤ (∑ j, ‖ofLp x.val j‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
  have hm : ‖x.val‖ ≤ ∑ j, ‖ofLp x.val j‖ :=
    (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).1 hsq
  exact hm.trans x.property.1

/-- Real linear quadratic tests indexed by the bounded coefficient class. -/
def atomicCoefficientTests {N Q : ℕ} (S : ℝ) (row : Fin N → Fin Q → ℂ)
    (x : atomicCoefficientClass S row) : Matrix (Fin Q) (Fin Q) ℂ →ₗ[ℝ] ℝ :=
  quadraticTestLinearMap x.val

/-- These tests are pointwise bounded on every matrix, with no assumption
on the dictionary's covariance or rank. -/
theorem atomicCoefficientTests_bddAbove {N Q : ℕ} (S : ℝ)
    (row : Fin N → Fin Q → ℂ) (A : Matrix (Fin Q) (Fin Q) ℂ) :
    BddAbove (Set.range fun x => |atomicCoefficientTests S row x A|) := by
  have hc : Continuous (fun z : EuclideanSpace ℂ (Fin Q) => |quadratic A z|) := by
    unfold quadratic
    fun_prop
  apply ((isCompact_closedBall (0 : EuclideanSpace ℂ (Fin Q)) (Real.sqrt S)).bddAbove_image
    hc.continuousOn).mono
  rintro _ ⟨x, rfl⟩
  exact ⟨x.val, by simpa using norm_mem_atomicCoefficientClass_le row x, rfl⟩

theorem atomicMeanGram_eq_finiteAverage {N Q : ℕ}
    (row : Fin N → Fin Q → ℂ) : mean (atomicRowGram row) = finiteAverage (atomicRowGram row) := by
  simp only [mean, finiteAverage, Fintype.card_fin, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv]
  rfl

/-- The full Gram quadratic form is the full mean row energy. -/
theorem quadratic_atomicMeanGram {N Q : ℕ} (row : Fin N → Fin Q → ℂ)
    (x : EuclideanSpace ℂ (Fin Q)) :
    quadratic (mean (atomicRowGram row)) x = atomicMeanEnergy row x := by
  rw [atomicMeanGram_eq_finiteAverage]
  change quadraticTestLinearMap x (finiteAverage (atomicRowGram row)) = _
  simp only [finiteAverage, map_smul, map_sum, smul_eq_mul,
    quadraticTestLinearMap_apply, quadratic_atomicRowGram, atomicMeanEnergy]

/-- The Gram average associated with independent row labels. -/
def atomicIidMeanGram {N Q m : ℕ} (row : Fin N → Fin Q → ℂ)
    (ω : Fin m → Fin N) : Matrix (Fin Q) (Fin Q) ℂ :=
  (m : ℝ)⁻¹ • ∑ i, atomicRowGram row (ω i)

theorem quadratic_atomicIidMeanGram {N Q m : ℕ} (row : Fin N → Fin Q → ℂ)
    (ω : Fin m → Fin N) (x : EuclideanSpace ℂ (Fin Q)) :
    quadratic (atomicIidMeanGram row ω) x = finiteAverage (fun i => atomicRowEnergy row (ω i) x) := by
  change quadraticTestLinearMap x ((m : ℝ)⁻¹ • ∑ i, atomicRowGram row (ω i)) = _
  simp only [map_smul, map_sum, smul_eq_mul, quadraticTestLinearMap_apply,
    quadratic_atomicRowGram, finiteAverage, Fintype.card_fin]

theorem quadratic_atomicSampleMean {N Q m : ℕ} (row : Fin N → Fin Q → ℂ)
    (Ω : Sample N m) (x : EuclideanSpace ℂ (Fin Q)) :
    quadratic (sampleMean (atomicRowGram row) Ω) x =
      (m : ℝ)⁻¹ * ∑ k ∈ Ω.val, atomicRowEnergy row k x := by
  have he : sampleMean (atomicRowGram row) Ω =
      (m : ℝ)⁻¹ • ∑ k ∈ Ω.val, atomicRowGram row k := by
    simp only [sampleMean, sampleSum, ← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    rfl
  rw [he]
  change quadraticTestLinearMap x ((m : ℝ)⁻¹ • ∑ k ∈ Ω.val, atomicRowGram row k) = _
  simp only [map_smul, map_sum, smul_eq_mul, quadraticTestLinearMap_apply,
    quadratic_atomicRowGram]

/-- Restricted absolute deviation of a centered Gram matrix. -/
def atomicGramDeviation {N Q : ℕ} (S : ℝ) (row : Fin N → Fin Q → ℂ)
    (A : Matrix (Fin Q) (Fin Q) ℂ) : ℝ :=
  restrictedAbsoluteSup (atomicCoefficientTests S row) (A - mean (atomicRowGram row))

theorem atomicGramDeviation_nonneg {N Q : ℕ} (S : ℝ)
    (row : Fin N → Fin Q → ℂ) (A : Matrix (Fin Q) (Fin Q) ℂ) :
    0 ≤ atomicGramDeviation S row A :=
  restrictedAbsoluteSup_nonneg (atomicCoefficientTests S row)
    (atomicCoefficientTests_bddAbove S row) _

theorem atomicCoefficientTest_centered {N Q : ℕ} (S : ℝ)
    (row : Fin N → Fin Q → ℂ) (x : atomicCoefficientClass S row)
    (A : Matrix (Fin Q) (Fin Q) ℂ) :
    atomicCoefficientTests S row x (A - mean (atomicRowGram row)) =
      quadratic A x.val - atomicMeanEnergy row x.val := by
  rw [map_sub]
  change quadratic A x.val - quadratic (mean (atomicRowGram row)) x.val = _
  rw [quadratic_atomicMeanGram]

/-- Every coefficient vector's centered error is bounded by the restricted
deviation. This is the deterministic step used to recover uniform estimates. -/
theorem abs_quadratic_sub_atomicMeanEnergy_le_deviation {N Q : ℕ} (S : ℝ)
    (row : Fin N → Fin Q → ℂ) (x : atomicCoefficientClass S row)
    (A : Matrix (Fin Q) (Fin Q) ℂ) :
    |quadratic A x.val - atomicMeanEnergy row x.val| ≤ atomicGramDeviation S row A := by
  rw [← atomicCoefficientTest_centered S row x A]
  exact abs_linearTest_le_restrictedAbsoluteSup (atomicCoefficientTests S row)
    (atomicCoefficientTests_bddAbove S row) x _

/-- A bounded restricted deviation is equivalent to all of its pointwise
coefficient estimates. -/
theorem atomicGramDeviation_le_iff {N Q : ℕ} (S : ℝ)
    (row : Fin N → Fin Q → ℂ) (A : Matrix (Fin Q) (Fin Q) ℂ) (ρ : ℝ) :
    atomicGramDeviation S row A ≤ ρ ↔
      ∀ x : atomicCoefficientClass S row,
        |quadratic A x.val - atomicMeanEnergy row x.val| ≤ ρ := by
  constructor
  · intro h x
    exact (abs_quadratic_sub_atomicMeanEnergy_le_deviation S row x A).trans h
  · intro h
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    change |atomicCoefficientTests S row x (A - mean (atomicRowGram row))| ≤ ρ
    rw [atomicCoefficientTest_centered]
    exact h x

/-- The independent Gram deviation is the supremum of the original empirical
row-energy errors over the coefficient class. -/
theorem atomicIidGramDeviation_eq {N Q m : ℕ} (S : ℝ)
    (row : Fin N → Fin Q → ℂ) (ω : Fin m → Fin N) :
    atomicGramDeviation S row (atomicIidMeanGram row ω) =
      sSup (Set.range fun x : atomicCoefficientClass S row =>
        |finiteAverage (fun i => atomicRowEnergy row (ω i) x.val) -
          atomicMeanEnergy row x.val|) := by
  unfold atomicGramDeviation restrictedAbsoluteSup
  simp_rw [atomicCoefficientTest_centered, quadratic_atomicIidMeanGram]

/-- The fixed-size Gram deviation uses exactly the sample's normalized energy. -/
theorem atomicSampleGramDeviation_eq {N Q m : ℕ} (S : ℝ)
    (row : Fin N → Fin Q → ℂ) (Ω : Sample N m) :
    atomicGramDeviation S row (sampleMean (atomicRowGram row) Ω) =
      sSup (Set.range fun x : atomicCoefficientClass S row =>
        |(m : ℝ)⁻¹ * ∑ k ∈ Ω.val, atomicRowEnergy row k x.val -
          atomicMeanEnergy row x.val|) := by
  unfold atomicGramDeviation restrictedAbsoluteSup
  simp_rw [atomicCoefficientTest_centered, quadratic_atomicSampleMean]

/-- Any Gram average whose quadratic values lie between zero and `S` has
restricted deviation at most `S+1`. -/
theorem atomicGramDeviation_le {N Q : ℕ} {S : ℝ} (hS : 0 ≤ S)
    (row : Fin N → Fin Q → ℂ) (A : Matrix (Fin Q) (Fin Q) ℂ)
    (hA : ∀ x : atomicCoefficientClass S row, 0 ≤ quadratic A x.val ∧ quadratic A x.val ≤ S) :
    atomicGramDeviation S row A ≤ S + 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  change |atomicCoefficientTests S row x (A - mean (atomicRowGram row))| ≤ S + 1
  rw [atomicCoefficientTest_centered]
  have hm := atomicMeanEnergy_nonneg row x.val
  have hmean := x.property.2
  rcases hA x with ⟨hlo, hhi⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem atomicIidGramDeviation_le {N Q m : ℕ} {S : ℝ} (hS : 0 ≤ S)
    (row : Fin N → Fin Q → ℂ) (hrow : ∀ k j, ‖row k j‖ ≤ 1)
    (ω : Fin m → Fin N) : atomicGramDeviation S row (atomicIidMeanGram row ω) ≤ S + 1 := by
  apply atomicGramDeviation_le hS row
  intro x
  rw [quadratic_atomicIidMeanGram]
  constructor
  · unfold finiteAverage
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => atomicRowEnergy_nonneg _ _ _)
  · by_cases hm : m = 0
    · subst m
      simpa [finiteAverage] using hS
    · letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hm)
      exact (finiteAverage_mono (fun i => atomicRowEnergy_le hS row hrow (ω i) x)).trans_eq
        (finiteAverage_const S)

theorem atomicSampleGramDeviation_le {N Q m : ℕ} {S : ℝ} (hS : 0 ≤ S)
    (row : Fin N → Fin Q → ℂ) (hrow : ∀ k j, ‖row k j‖ ≤ 1)
    (Ω : Sample N m) : atomicGramDeviation S row (sampleMean (atomicRowGram row) Ω) ≤ S + 1 := by
  apply atomicGramDeviation_le hS row
  intro x
  rw [quadratic_atomicSampleMean]
  constructor
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => atomicRowEnergy_nonneg _ _ _)
  · have hsum : (∑ k ∈ Ω.val, atomicRowEnergy row k x.val) ≤ m * S := by
      calc
        _ ≤ ∑ _k ∈ Ω.val, S := Finset.sum_le_sum fun k _ => atomicRowEnergy_le hS row hrow k x
        _ = _ := by simp [Ω.property]
    have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg m))
    by_cases hm : m = 0
    · simpa [hm] using hS
    · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      simpa only [← mul_assoc, inv_mul_cancel₀ hm', one_mul] using h

end

end LeanNumDetect.FiniteMatrixSampling
