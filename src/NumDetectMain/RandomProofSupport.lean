import NumDetectMain.ProofSupport

/-!
Deterministic matrix estimates used by the realized-frequency random GHM theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace LeanNumDetect
namespace NumDetect

noncomputable section

section SingularValueVariational

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

private theorem norm_sq_eq_re_inner_adjoint_comp_self
    (T : E →ₗ[ℂ] F) (x : E) :
    ‖T x‖ ^ 2 = RCLike.re ⟪x, (T.adjoint ∘ₗ T) x⟫_ℂ := by
  rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The first `i+1` right singular directions give a subspace on which the
`i`-th singular value is a uniform lower bound. -/
theorem singularValues_lower_subspace
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
        exact norm_sq_eq_re_inner_adjoint_comp_self T x

/-- Every `i+1` dimensional subspace contains a unit vector on which the
`i`-th singular value is an upper bound. -/
theorem exists_unit_norm_image_le_singularValue
    (T : E →ₗ[ℂ] F) {i : ℕ} (hi : i < Module.finrank ℂ E)
    (S : Submodule ℂ E) (hS : Module.finrank ℂ S = i + 1) :
    ∃ x : E, x ∈ S ∧ ‖x‖ = 1 ∧ ‖T x‖ ≤ T.singularValues i := by
  classical
  let H := T.adjoint ∘ₗ T
  let hH := T.isSymmetric_adjoint_comp_self
  let b := hH.eigenvectorBasis rfl
  let fi : Fin (Module.finrank ℂ E) := ⟨i, hi⟩
  obtain ⟨x, hx, hnorm, hzero⟩ :=
    exists_unit_mem_coord_zero b S (Finset.Iio fi) (by simp [hS, fi])
  refine ⟨x, hx, hnorm, ?_⟩
  apply (sq_le_sq₀ (norm_nonneg (T x)) (T.singularValues_nonneg i)).1
  rw [T.sq_singularValues_of_lt rfl hi,
    norm_sq_eq_re_inner_adjoint_comp_self T x]
  have hupper := rayleigh_upper_of_support H hH x
    (c := hH.eigenvalues rfl fi) (by
      intro j hj
      have hij : fi ≤ j := by
        by_contra hij
        exact hj (hzero j (Finset.mem_Iio.mpr (lt_of_not_ge hij)))
      exact hH.eigenvalues_antitone rfl hij)
  simpa only [hnorm, one_pow, mul_one] using hupper

/-- A lower bound on one `i+1` dimensional subspace bounds the `i`-th
singular value. -/
theorem le_singularValue_of_subspace_lower
    (T : E →ₗ[ℂ] F) {i : ℕ} (hi : i < Module.finrank ℂ E)
    (S : Submodule ℂ E) (hS : Module.finrank ℂ S = i + 1)
    {c : ℝ} (hbound : ∀ x ∈ S, c * ‖x‖ ≤ ‖T x‖) :
    c ≤ T.singularValues i := by
  obtain ⟨x, hx, hnorm, hupper⟩ :=
    exists_unit_norm_image_le_singularValue T hi S hS
  simpa only [hnorm, mul_one] using (hbound x hx).trans hupper

/-- Weyl's operator-norm perturbation bound for finite-dimensional singular values. -/
theorem singularValues_sub_opNorm_le
    (A B : E →ₗ[ℂ] F) {i : ℕ} (hi : i < Module.finrank ℂ E) :
    A.singularValues i - ‖(A - B).toContinuousLinearMap‖ ≤
      B.singularValues i := by
  obtain ⟨S, hS, hA⟩ := singularValues_lower_subspace A hi
  obtain ⟨x, hx, hnorm, hB⟩ :=
    exists_unit_norm_image_le_singularValue B hi S hS
  have hdiff :
      ‖(A - B) x‖ ≤ ‖(A - B).toContinuousLinearMap‖ := by
    change ‖(A - B).toContinuousLinearMap x‖ ≤ ‖(A - B).toContinuousLinearMap‖
    simpa only [hnorm, mul_one] using (A - B).toContinuousLinearMap.le_opNorm x
  have htriangle : ‖A x‖ ≤ ‖B x‖ + ‖(A - B) x‖ := by
    calc
      ‖A x‖ = ‖B x + (A - B) x‖ := by simp
      _ ≤ _ := norm_add_le _ _
  have hlower : A.singularValues i ≤ ‖A x‖ := by
    simpa only [hnorm, mul_one] using hA x hx
  linarith

end SingularValueVariational

/-- Matrix form of the singular-value perturbation bound. -/
theorem matrixSingularValue_sub_spectralNorm_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A B : Matrix m n ℂ) {i : ℕ} (hi : i < Fintype.card n) :
    matrixSingularValue A i - matrixSpectralNorm (A - B) ≤
      matrixSingularValue B i := by
  change
    A.toEuclideanLin.singularValues i -
        ‖(A - B).toEuclideanLin.toContinuousLinearMap‖ ≤
      B.toEuclideanLin.singularValues i
  simpa only [map_sub] using
    (singularValues_sub_opNorm_le A.toEuclideanLin B.toEuclideanLin
      (by simpa using hi))

/-- The `i`-th singular value changes by at most the spectral norm of a perturbation. -/
theorem matrixSingularValue_le_add_spectralNorm_sub
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A B : Matrix m n ℂ) {i : ℕ} (hi : i < Fintype.card n) :
    matrixSingularValue A i ≤
      matrixSingularValue B i + matrixSpectralNorm (A - B) := by
  have h := matrixSingularValue_sub_spectralNorm_le A B hi
  linarith

/-- The last singular value of a map bounds it below on every vector. -/
theorem matrix_lastSingularValue_mul_norm_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hn : 0 < Fintype.card n)
    (x : EuclideanSpace ℂ n) :
    matrixSingularValue A (Fintype.card n - 1) * ‖x‖ ≤
      ‖A.toEuclideanLin x‖ := by
  obtain ⟨S, hS, hbound⟩ :=
    singularValues_lower_subspace A.toEuclideanLin (i := Fintype.card n - 1)
      (by simpa using Nat.sub_lt hn Nat.zero_lt_one)
  have htop : S = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hS]
    rw [finrank_euclideanSpace]
    omega
  exact hbound x (by simp [htop])

/-- A lower bound on the entries of a diagonal matrix bounds its action. -/
theorem diagonal_toEuclideanLin_lower
    {n : Type*} [Fintype n] [DecidableEq n]
    (a : n → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (ha : ∀ j, c ≤ ‖a j‖) (x : EuclideanSpace ℂ n) :
    c * ‖x‖ ≤ ‖(Matrix.diagonal a).toEuclideanLin x‖ := by
  change c * ‖x‖ ≤
    ‖(EuclideanSpace.equiv n ℂ).symm (Matrix.diagonal a *ᵥ x.ofLp)‖
  exact norm_diagonal_mulVec_lower a hc ha x

/-- Product lower bound at the last singular value of the middle dimension. -/
theorem matrixSingularValue_three_mul_lower
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℂ) (a : n → ℂ) (B : Matrix n p ℂ)
    (hn : 0 < Fintype.card n) (hnp : Fintype.card n ≤ Fintype.card p)
    {c : ℝ} (hc : 0 ≤ c) (ha : ∀ j, c ≤ ‖a j‖) :
    matrixSingularValue A (Fintype.card n - 1) * c *
        matrixSingularValue B (Fintype.card n - 1) ≤
      matrixSingularValue (A * Matrix.diagonal a * B) (Fintype.card n - 1) := by
  let i := Fintype.card n - 1
  have hi : i < Fintype.card p := (Nat.sub_lt hn Nat.zero_lt_one).trans_le hnp
  obtain ⟨S, hS, hB⟩ := singularValues_lower_subspace B.toEuclideanLin
    (by simpa using hi)
  apply le_singularValue_of_subspace_lower
    (A * Matrix.diagonal a * B).toEuclideanLin
    (i := Fintype.card n - 1) (by simpa using hi) S
  · simpa [i, Nat.sub_add_cancel hn] using hS
  · intro x hx
    have hBx := hB x hx
    change matrixSingularValue B i * ‖x‖ ≤ ‖B.toEuclideanLin x‖ at hBx
    have hDx := diagonal_toEuclideanLin_lower a hc ha (B.toEuclideanLin x)
    have hAx := matrix_lastSingularValue_mul_norm_le A hn
      ((Matrix.diagonal a).toEuclideanLin (B.toEuclideanLin x))
    calc
      matrixSingularValue A i * c * matrixSingularValue B i * ‖x‖
          = matrixSingularValue A i *
              (c * (matrixSingularValue B i * ‖x‖)) := by ring
      _ ≤ matrixSingularValue A i * (c * ‖B.toEuclideanLin x‖) := by
        gcongr
        exact matrixSingularValue_nonneg A i
      _ ≤ matrixSingularValue A i *
            ‖(Matrix.diagonal a).toEuclideanLin (B.toEuclideanLin x)‖ := by
        gcongr
        exact matrixSingularValue_nonneg A i
      _ ≤ ‖A.toEuclideanLin
            ((Matrix.diagonal a).toEuclideanLin (B.toEuclideanLin x))‖ := hAx
      _ = ‖(A * Matrix.diagonal a * B).toEuclideanLin x‖ := by
        rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same]
        rfl

/-- Squared entry mass of a finite complex matrix. -/
def matrixEntryEnergy {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem matrixEntryEnergy_nonneg
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    0 ≤ matrixEntryEnergy A :=
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

/-- The Euclidean operator norm is bounded by the square root of entry energy. -/
theorem matrixSpectralNorm_le_sqrt_entryEnergy
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) :
    matrixSpectralNorm A ≤ Real.sqrt (matrixEntryEnergy A) := by
  rw [matrixSpectralNorm, LinearEquiv.trans_apply]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).1
  rw [mul_pow, Real.sq_sqrt (matrixEntryEnergy_nonneg A),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    ∑ i, ‖(A *ᵥ x.ofLp) i‖ ^ 2
        ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => dotProduct_norm_sq_le (A i) x.ofLp
    _ = matrixEntryEnergy A * ∑ j, ‖x.ofLp j‖ ^ 2 := by
      change
        (∑ i, (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2) =
          (∑ i, ∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖x.ofLp j‖ ^ 2
      rw [Finset.sum_mul]

/-- Strict pointwise control gives the strict Frobenius-size operator bound
used in the manuscript. -/
theorem matrixSpectralNorm_lt_card_sqrt
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    [Nonempty m] [Nonempty n]
    (A : Matrix m n ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hentry : ∀ i j, ‖A i j‖ < σ) :
    matrixSpectralNorm A <
      σ * Real.sqrt (Fintype.card m * Fintype.card n) := by
  have hsq (i : m) (j : n) : ‖A i j‖ ^ 2 < σ ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hσ.le).2 (hentry i j)
  have henergy :
      matrixEntryEnergy A <
        (Fintype.card m : ℝ) * (Fintype.card n : ℝ) * σ ^ 2 := by
    calc
      matrixEntryEnergy A
          < ∑ _i : m, ∑ _j : n, σ ^ 2 := by
            apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
            intro i _
            exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
              (fun j _ => hsq i j)
      _ = _ := by simp; ring
  have hcard : 0 ≤ (Fintype.card m * Fintype.card n : ℝ) := by positivity
  have hthreshold : 0 ≤ σ * Real.sqrt (Fintype.card m * Fintype.card n) := by
    positivity
  calc
    matrixSpectralNorm A ≤ Real.sqrt (matrixEntryEnergy A) :=
      matrixSpectralNorm_le_sqrt_entryEnergy A
    _ < σ * Real.sqrt (Fintype.card m * Fintype.card n) := by
      rw [Real.sqrt_lt (matrixEntryEnergy_nonneg A) hthreshold]
      rw [mul_pow, Real.sq_sqrt hcard]
      nlinarith

end

end NumDetect
end LeanNumDetect
