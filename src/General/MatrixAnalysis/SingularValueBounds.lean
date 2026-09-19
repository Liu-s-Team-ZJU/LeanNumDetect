import General.MatrixAnalysis.HermitianVariational
import General.MatrixAnalysis.RowDeletion
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
Variational bounds for singular values and the Euclidean matrix operator norm.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace LeanNumDetect

noncomputable section

section SingularValueVariational

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

private theorem norm_sq_apply_eq_re_inner_adjoint_comp_self
    (T : E →ₗ[ℂ] F) (x : E) :
    ‖T x‖ ^ 2 = RCLike.re ⟪x, (T.adjoint ∘ₗ T) x⟫_ℂ := by
  rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  exact (@RCLike.re_ofReal_pow ℂ _ ‖T x‖ 2).symm

/-- The first `i + 1` right singular directions form a subspace on which the
`i`-th singular value is a uniform lower bound. -/
theorem singularValues_lower_subspace_exists
    (T : E →ₗ[ℂ] F) {i : ℕ} (hi : i < Module.finrank ℂ E) :
    ∃ S : Submodule ℂ E,
      Module.finrank ℂ S = i + 1 ∧
      ∀ x ∈ S, T.singularValues i * ‖x‖ ≤ ‖T x‖ := by
  classical
  let H := T.adjoint ∘ₗ T
  let hH := T.isSymmetric_adjoint_comp_self
  let b := hH.eigenvectorBasis rfl
  let fi : Fin (Module.finrank ℂ E) := ⟨i, hi⟩
  let S := Submodule.span ℂ (b '' (Finset.Iic fi : Set (Fin (Module.finrank ℂ E))))
  refine ⟨S, ?_, ?_⟩
  · simpa [S, fi] using finrank_orthonormal_span b (Finset.Iic fi)
  · intro x hx
    apply (sq_le_sq₀
      (mul_nonneg (T.singularValues_nonneg i) (norm_nonneg x))
      (norm_nonneg (T x))).1
    rw [mul_pow, T.sq_singularValues_of_lt rfl hi]
    calc
      hH.eigenvalues rfl fi * ‖x‖ ^ 2
          ≤ RCLike.re ⟪x, H x⟫_ℂ := by
            apply rayleigh_lower_of_support H hH x
            intro j hj
            have hji : j ≤ fi := by
              by_contra hji
              exact hj (orthonormal_inner_eq_zero_of_mem_span b (Finset.Iic fi) hx
                (by simpa using hji))
            exact hH.eigenvalues_antitone rfl hji
      _ = ‖T x‖ ^ 2 := by
        symm
        exact norm_sq_apply_eq_re_inner_adjoint_comp_self T x

/-- Every `i + 1` dimensional subspace contains a unit vector on which the
`i`-th singular value is an upper bound. -/
theorem singularValues_upper_vector_exists
    (T : E →ₗ[ℂ] F) {i : ℕ} (hi : i < Module.finrank ℂ E)
    (S : Submodule ℂ E) (hS : Module.finrank ℂ S = i + 1) :
    ∃ x : E, x ∈ S ∧ ‖x‖ = 1 ∧ ‖T x‖ ≤ T.singularValues i := by
  classical
  let H := T.adjoint ∘ₗ T
  let hH := T.isSymmetric_adjoint_comp_self
  let b := hH.eigenvectorBasis rfl
  let fi : Fin (Module.finrank ℂ E) := ⟨i, hi⟩
  obtain ⟨x, hx, hnorm, hzero⟩ :=
    exists_unit_mem_coord_zero b S (Finset.Iio fi) (by simpa [hS, fi])
  refine ⟨x, hx, hnorm, ?_⟩
  apply (sq_le_sq₀ (norm_nonneg (T x)) (T.singularValues_nonneg i)).1
  rw [T.sq_singularValues_of_lt rfl hi,
    norm_sq_apply_eq_re_inner_adjoint_comp_self T x]
  have hupper := rayleigh_upper_of_support H hH x
    (c := hH.eigenvalues rfl fi) (by
      intro j hj
      have hij : fi ≤ j := by
        by_contra hij
        exact hj (hzero j (Finset.mem_Iio.mpr (lt_of_not_ge hij)))
      exact hH.eigenvalues_antitone rfl hij)
  simpa only [hnorm, one_pow, mul_one] using hupper

/-- A uniform lower bound on one `i + 1` dimensional subspace bounds the
`i`-th singular value. -/
theorem le_singularValues_of_subspace
    (T : E →ₗ[ℂ] F) {i : ℕ} (hi : i < Module.finrank ℂ E)
    (S : Submodule ℂ E) (hS : Module.finrank ℂ S = i + 1)
    {c : ℝ} (hbound : ∀ x ∈ S, c * ‖x‖ ≤ ‖T x‖) :
    c ≤ T.singularValues i := by
  obtain ⟨x, hx, hnorm, hupper⟩ :=
    singularValues_upper_vector_exists T hi S hS
  simpa only [hnorm, mul_one] using (hbound x hx).trans hupper

/-- One-sided operator-norm perturbation bound for singular values. -/
theorem singularValues_sub_operatorNorm_le
    (A B : E →ₗ[ℂ] F) {i : ℕ} (hi : i < Module.finrank ℂ E) :
    A.singularValues i - ‖(A - B).toContinuousLinearMap‖ ≤
      B.singularValues i := by
  obtain ⟨S, hS, hA⟩ := singularValues_lower_subspace_exists A hi
  obtain ⟨x, hx, hnorm, hB⟩ :=
    singularValues_upper_vector_exists B hi S hS
  have hdiff :
      ‖(A - B) x‖ ≤ ‖(A - B).toContinuousLinearMap‖ := by
    change ‖(A - B).toContinuousLinearMap x‖ ≤ _
    simpa only [hnorm, mul_one] using (A - B).toContinuousLinearMap.le_opNorm x
  have htriangle : ‖A x‖ ≤ ‖B x‖ + ‖(A - B) x‖ := by
    calc
      ‖A x‖ = ‖B x + (A - B) x‖ := by simp
      _ ≤ _ := norm_add_le _ _
  have hlower : A.singularValues i ≤ ‖A x‖ := by
    simpa only [hnorm, mul_one] using hA x hx
  linarith

/-- Weyl's operator-norm perturbation bound for finite-dimensional singular values. -/
theorem abs_singularValues_sub_le_operatorNorm
    (A B : E →ₗ[ℂ] F) {i : ℕ} (hi : i < Module.finrank ℂ E) :
    |A.singularValues i - B.singularValues i| ≤
      ‖(A - B).toContinuousLinearMap‖ := by
  rw [abs_le]
  constructor
  · have h := singularValues_sub_operatorNorm_le B A hi
    have hnorm :
        ‖(B - A).toContinuousLinearMap‖ =
          ‖(A - B).toContinuousLinearMap‖ := by
      rw [show B - A = -(A - B) by abel]
      change ‖-(A - B).toContinuousLinearMap‖ =
        ‖(A - B).toContinuousLinearMap‖
      exact norm_neg _
    rw [hnorm] at h
    linarith
  · have h := singularValues_sub_operatorNorm_le A B hi
    linarith

end SingularValueVariational

/-- Matrix form of the singular-value Weyl bound in Euclidean operator norm. -/
theorem abs_matrixSingularValue_sub_le_l2OpNorm
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A B : Matrix m n ℂ) {i : ℕ} (hi : i < Fintype.card n) :
    |matrixSingularValue A i - matrixSingularValue B i| ≤ ‖A - B‖ := by
  rw [matrixSingularValue, matrixSingularValue, Matrix.l2_opNorm_def]
  convert abs_singularValues_sub_le_operatorNorm
    A.toEuclideanLin B.toEuclideanLin (by simpa using hi) using 1 <;> simp

/-- The last singular value bounds a matrix below on every vector. -/
theorem lastMatrixSingularValue_mul_norm_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hn : 0 < Fintype.card n)
    (x : EuclideanSpace ℂ n) :
    matrixSingularValue A (Fintype.card n - 1) * ‖x‖ ≤
      ‖A.toEuclideanLin x‖ := by
  obtain ⟨S, hS, hbound⟩ :=
    singularValues_lower_subspace_exists A.toEuclideanLin
      (i := Fintype.card n - 1)
      (by simpa using Nat.sub_lt hn Nat.zero_lt_one)
  have htop : S = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [finrank_euclideanSpace, Nat.sub_add_cancel hn] using hS
  exact hbound x (by simp [htop])

/-- A pointwise lower bound on a diagonal gives the same lower bound on its action. -/
theorem diagonalToEuclideanLin_lower
    {n : Type*} [Fintype n] [DecidableEq n]
    (a : n → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (ha : ∀ j, c ≤ ‖a j‖) (x : EuclideanSpace ℂ n) :
    c * ‖x‖ ≤ ‖(Matrix.diagonal a).toEuclideanLin x‖ := by
  change c * ‖x‖ ≤ ‖toLp 2 (Matrix.diagonal a *ᵥ ofLp x)‖
  rw [← sq_le_sq₀ (mul_nonneg hc (norm_nonneg x)) (norm_nonneg _)]
  rw [mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum,
    EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro j _
  change c ^ 2 * ‖ofLp x j‖ ^ 2 ≤
    ‖(Matrix.diagonal a *ᵥ ofLp x) j‖ ^ 2
  rw [Matrix.mulVec_diagonal, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ hc (norm_nonneg _)).2 (ha j)) (sq_nonneg ‖x j‖)

/-- Product lower bound at the last singular value of the middle dimension. -/
theorem matrixSingularValue_threeFactor_lower
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℂ) (a : n → ℂ) (B : Matrix n p ℂ)
    (hn : 0 < Fintype.card n) (hnp : Fintype.card n ≤ Fintype.card p)
    {c : ℝ} (hc : 0 ≤ c) (ha : ∀ j, c ≤ ‖a j‖) :
    matrixSingularValue A (Fintype.card n - 1) * c *
        matrixSingularValue B (Fintype.card n - 1) ≤
      matrixSingularValue (A * Matrix.diagonal a * B)
        (Fintype.card n - 1) := by
  let i := Fintype.card n - 1
  have hi : i < Fintype.card p := (Nat.sub_lt hn Nat.zero_lt_one).trans_le hnp
  obtain ⟨S, hS, hB⟩ := singularValues_lower_subspace_exists B.toEuclideanLin
    (i := i) (by simpa using hi)
  apply le_singularValues_of_subspace
    (A * Matrix.diagonal a * B).toEuclideanLin (i := i) (by simpa using hi) S
  · simpa [i, Nat.sub_add_cancel hn] using hS
  · intro x hx
    have hBx := hB x hx
    have hDx := diagonalToEuclideanLin_lower a hc ha (B.toEuclideanLin x)
    have hAx := lastMatrixSingularValue_mul_norm_le A hn
      ((Matrix.diagonal a).toEuclideanLin (B.toEuclideanLin x))
    calc
      matrixSingularValue A i * c * matrixSingularValue B i * ‖x‖
          = matrixSingularValue A i *
              (c * (matrixSingularValue B i * ‖x‖)) := by ring
      _ ≤ matrixSingularValue A i * (c * ‖B.toEuclideanLin x‖) := by
        change matrixSingularValue A i *
            (c * (B.toEuclideanLin.singularValues i * ‖x‖)) ≤ _
        gcongr
        exact A.toEuclideanLin.singularValues_nonneg i
      _ ≤ matrixSingularValue A i *
            ‖(Matrix.diagonal a).toEuclideanLin (B.toEuclideanLin x)‖ := by
        gcongr
        exact A.toEuclideanLin.singularValues_nonneg i
      _ ≤ ‖A.toEuclideanLin
            ((Matrix.diagonal a).toEuclideanLin (B.toEuclideanLin x))‖ := hAx
      _ = ‖(A * Matrix.diagonal a * B).toEuclideanLin x‖ := by
        rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same]
        rfl

/-- A coercive map's adjoint has the same lower bound on the map's range. -/
theorem adjoint_mul_norm_le_on_range
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F]
    (B : E →ₗ[ℂ] F) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ x, c * ‖x‖ ≤ ‖B x‖) {w : F} (hw : w ∈ B.range) :
    c * ‖w‖ ≤ ‖B.adjoint w‖ := by
  obtain ⟨x, rfl⟩ := hw
  by_cases hx : B x = 0
  · simp [hx]
  have hp : 0 < ‖B x‖ := norm_pos_iff.mpr hx
  have hcs : ‖B x‖ ^ 2 ≤ ‖x‖ * ‖B.adjoint (B x)‖ := by
    have h := re_inner_le_norm (𝕜 := ℂ) x (B.adjoint (B x))
    simpa only [LinearMap.adjoint_inner_right, inner_self_eq_norm_sq,
      RCLike.ofReal_re] using h
  have h₁ := mul_le_mul_of_nonneg_left hcs hc
  have h₂ := mul_le_mul_of_nonneg_right (hB x) (norm_nonneg (B.adjoint (B x)))
  apply (mul_le_mul_iff_left₀ hp).mp
  nlinarith

/-- Entrywise conjugation preserves the least-column coercivity bound. -/
theorem lastMatrixSingularValue_conjugate_mul_norm_le
    {m : Type*} [Fintype m] {n : ℕ}
    (B : Matrix m (Fin n) ℂ) (hn : 0 < n)
    (x : EuclideanSpace ℂ (Fin n)) :
    matrixSingularValue B (n - 1) * ‖x‖ ≤
      ‖(B.map star).toEuclideanLin x‖ := by
  have h := lastMatrixSingularValue_mul_norm_le B (by simpa using hn)
    (toLp 2 (star (ofLp x)))
  have hnorm : ‖toLp 2 (star (ofLp x))‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq]
  rw [hnorm] at h
  have he : (B.map star).toEuclideanLin x =
      toLp 2 (star (ofLp (B.toEuclideanLin
        (toLp 2 (star (ofLp x)))))) := by
    ext i
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, star_sum,
      star_mul, mul_comm]
  rw [he]
  have hout :
      ‖toLp 2 (star (ofLp (B.toEuclideanLin
        (toLp 2 (star (ofLp x))))))‖ =
        ‖B.toEuclideanLin (toLp 2 (star (ofLp x)))‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq]
  rw [hout]
  simpa only [Fintype.card_fin] using h

/-- On the conjugate column range, a transpose has the least-column lower
bound of the original matrix. -/
theorem transpose_mul_norm_le_on_conjugateColumnRange
    {m : Type*} [Fintype m] [DecidableEq m] {n : ℕ}
    (B : Matrix m (Fin n) ℂ) (hn : 0 < n)
    {w : EuclideanSpace ℂ m}
    (hw : w ∈ (B.map star).toEuclideanLin.range) :
    matrixSingularValue B (n - 1) * ‖w‖ ≤ ‖Bᵀ.toEuclideanLin w‖ := by
  have h := adjoint_mul_norm_le_on_range
    (B.map star).toEuclideanLin
    (B.toEuclideanLin.singularValues_nonneg (n - 1))
    (lastMatrixSingularValue_conjugate_mul_norm_le B hn) hw
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h
  have he : (B.map star)ᴴ = Bᵀ := by ext i j; simp
  rwa [he] at h

/-- Minimum-singular-value bound for `V₁ * diagonal a * V₂ᵀ`.
Injectivity of `V₂` supplies the `n`-dimensional subspace on which its
transpose has the required lower bound. -/
theorem matrixSingularValue_diagonal_transpose_lower
    {m p : Type*} [Fintype m] [Fintype p] [DecidableEq p] {n : ℕ}
    (V₁ : Matrix m (Fin n) ℂ) (a : Fin n → ℂ)
    (V₂ : Matrix p (Fin n) ℂ)
    (hn : 0 < n) (hnp : n ≤ Fintype.card p)
    (hV₂ : Function.Injective V₂.toEuclideanLin)
    {amin : ℝ} (hamin : 0 ≤ amin) (ha : ∀ j, amin ≤ ‖a j‖) :
    amin * matrixSingularValue V₁ (n - 1) *
        matrixSingularValue V₂ (n - 1) ≤
      matrixSingularValue (V₁ * Matrix.diagonal a * V₂ᵀ) (n - 1) := by
  let S := (V₂.map star).toEuclideanLin.range
  have hV₂pos : 0 < matrixSingularValue V₂ (n - 1) := by
    apply V₂.toEuclideanLin.injective_iff_forall_lt_finrank_singularValues_pos.mp hV₂
    simpa using (Nat.sub_lt hn Nat.zero_lt_one)
  have hconjInj : Function.Injective (V₂.map star).toEuclideanLin := by
    intro x y hxy
    have hcoer := lastMatrixSingularValue_conjugate_mul_norm_le V₂ hn (x - y)
    have hz : (V₂.map star).toEuclideanLin (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    rw [hz, norm_zero] at hcoer
    have hnorm : ‖x - y‖ = 0 := by
      nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hdim : Module.finrank ℂ S = n - 1 + 1 := by
    rw [LinearMap.finrank_range_of_inj hconjInj]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    omega
  apply le_singularValues_of_subspace
    (V₁ * Matrix.diagonal a * V₂ᵀ).toEuclideanLin
    (i := n - 1) (by simpa using (Nat.sub_lt hn Nat.zero_lt_one).trans_le hnp) S hdim
  intro x hx
  have hright := transpose_mul_norm_le_on_conjugateColumnRange V₂ hn hx
  have hdiag := diagonalToEuclideanLin_lower a hamin ha (V₂ᵀ.toEuclideanLin x)
  have hleft :
      matrixSingularValue V₁ (n - 1) *
          ‖(Matrix.diagonal a).toEuclideanLin (V₂ᵀ.toEuclideanLin x)‖ ≤
        ‖V₁.toEuclideanLin
          ((Matrix.diagonal a).toEuclideanLin (V₂ᵀ.toEuclideanLin x))‖ := by
    simpa only [Fintype.card_fin] using
      lastMatrixSingularValue_mul_norm_le V₁ (by simpa using hn)
        ((Matrix.diagonal a).toEuclideanLin (V₂ᵀ.toEuclideanLin x))
  calc
    amin * matrixSingularValue V₁ (n - 1) *
          matrixSingularValue V₂ (n - 1) * ‖x‖
        = matrixSingularValue V₁ (n - 1) *
            (amin * (matrixSingularValue V₂ (n - 1) * ‖x‖)) := by ring
    _ ≤ matrixSingularValue V₁ (n - 1) *
          (amin * ‖V₂ᵀ.toEuclideanLin x‖) := by
      gcongr
      exact V₁.toEuclideanLin.singularValues_nonneg (n - 1)
    _ ≤ matrixSingularValue V₁ (n - 1) *
          ‖(Matrix.diagonal a).toEuclideanLin (V₂ᵀ.toEuclideanLin x)‖ := by
      gcongr
      exact V₁.toEuclideanLin.singularValues_nonneg (n - 1)
    _ ≤ ‖V₁.toEuclideanLin
          ((Matrix.diagonal a).toEuclideanLin (V₂ᵀ.toEuclideanLin x))‖ := hleft
    _ = ‖(V₁ * Matrix.diagonal a * V₂ᵀ).toEuclideanLin x‖ := by
      rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same]
      rfl

/-- Sum of squared entry norms of a finite complex matrix. -/
def matrixEntryNormSq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem matrixEntryNormSq_nonneg
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    0 ≤ matrixEntryNormSq A :=
  Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem dotProduct_norm_sq_le
    {n : Type*} [Fintype n] (c v : n → ℂ) :
    ‖c ⬝ᵥ v‖ ^ 2 ≤ (∑ j, ‖c j‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := by
  have h := norm_sum_le Finset.univ (fun j => c j * v j)
  simp only [norm_mul] at h
  exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
    (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).2 h).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖c j‖) (fun j => ‖v j‖))

/-- The Euclidean operator norm is bounded by the square root of squared entry mass. -/
theorem matrix_l2OpNorm_le_sqrt_entryNormSq
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) :
    ‖A‖ ≤ Real.sqrt (matrixEntryNormSq A) := by
  rw [Matrix.l2_opNorm_def, LinearEquiv.trans_apply]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).1
  rw [mul_pow, Real.sq_sqrt (matrixEntryNormSq_nonneg A),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    ∑ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2
        ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => dotProduct_norm_sq_le (A i) x.ofLp
    _ = matrixEntryNormSq A * ∑ j, ‖x.ofLp j‖ ^ 2 := by
      change (∑ i : m, (∑ j : n, ‖A i j‖ ^ 2) *
        ∑ j, ‖x.ofLp j‖ ^ 2) =
        (∑ i : m, ∑ j : n, ‖A i j‖ ^ 2) *
          ∑ j, ‖x.ofLp j‖ ^ 2
      rw [Finset.sum_mul]

/-- A uniform pointwise entry bound gives the standard Frobenius-size
operator-norm bound. -/
theorem matrix_l2OpNorm_le_card_sqrt_mul
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hentry : ∀ i j, ‖A i j‖ ≤ c) :
    ‖A‖ ≤ Real.sqrt (Fintype.card m * Fintype.card n) * c := by
  have hsq (i : m) (j : n) : ‖A i j‖ ^ 2 ≤ c ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hc).2 (hentry i j)
  have henergy :
      matrixEntryNormSq A ≤
        (Fintype.card m : ℝ) * (Fintype.card n : ℝ) * c ^ 2 := by
    calc
      matrixEntryNormSq A
          ≤ ∑ _i : m, ∑ _j : n, c ^ 2 :=
            Finset.sum_le_sum fun i _ =>
              Finset.sum_le_sum fun j _ => hsq i j
      _ = _ := by simp; ring
  have hcard : 0 ≤ (Fintype.card m * Fintype.card n : ℝ) := by positivity
  have hthreshold :
      0 ≤ Real.sqrt (Fintype.card m * Fintype.card n) * c := by positivity
  calc
    ‖A‖ ≤ Real.sqrt (matrixEntryNormSq A) :=
      matrix_l2OpNorm_le_sqrt_entryNormSq A
    _ ≤ Real.sqrt (Fintype.card m * Fintype.card n) * c := by
      rw [Real.sqrt_le_iff]
      constructor
      · exact hthreshold
      · rw [mul_pow, Real.sq_sqrt hcard]
        nlinarith

end

end LeanNumDetect
