import NumDetect.MatrixFacts

/-! Centering the contiguous Vandermonde frequency grid. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- The centered contiguous frequency grid of the manuscript. -/
def centeredUniformFrequency (d s : ℕ) (Ω : ℝ)
    (α : UniformIndex d s) : Point d :=
  fun k => Ω / s * ((α k : ℝ) - (s : ℝ) / 2)

/-- The Vandermonde matrix on the centered contiguous grid. -/
def centeredUniformVandermonde {d n : ℕ} (s : ℕ) (Ω : ℝ)
    (node : Fin n → Point d) : Matrix (UniformIndex d s) (Fin n) ℂ :=
  generalizedVandermonde (centeredUniformFrequency d s Ω) node

/-- The diagonal phase relating the two contiguous frequency grids. -/
def uniformCenteringPhase {d n : ℕ} (Ω : ℝ)
    (node : Fin n → Point d) (j : Fin n) : ℂ :=
  Complex.exp (Complex.I * ((Ω / 2 * ∑ k, node j k : ℝ) : ℂ))

def uniformCenteringUnitary {d n : ℕ} (Ω : ℝ)
    (node : Fin n → Point d) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (uniformCenteringPhase Ω node)

theorem uniformVandermonde_eq_centered_mul_unitary
    {d n s : ℕ} (Ω : ℝ) (node : Fin n → Point d)
    (hs : 0 < s) :
    uniformVandermonde s Ω node =
      centeredUniformVandermonde s Ω node * uniformCenteringUnitary Ω node := by
  classical
  ext α j
  rw [uniformCenteringUnitary, Matrix.mul_diagonal]
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hscale : Ω / s * ((s : ℝ) / 2) = Ω / 2 := by
    field_simp
  have hdot :
      dot (uniformFrequency d s Ω α) (node j) =
        dot (centeredUniformFrequency d s Ω α) (node j) +
          Ω / 2 * ∑ k, node j k := by
    simp only [dot, uniformFrequency, centeredUniformFrequency]
    simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    simp_rw [hscale]
    ring
  simp only [uniformVandermonde, centeredUniformVandermonde,
    generalizedVandermonde, steeringVector, uniformCenteringPhase]
  rw [← Complex.exp_add]
  congr 1
  calc
    Complex.I * (dot (uniformFrequency d s Ω α) (node j) : ℂ) =
        Complex.I * ((dot (centeredUniformFrequency d s Ω α) (node j) +
          Ω / 2 * ∑ k, node j k : ℝ) : ℂ) :=
      congrArg (fun t : ℝ => Complex.I * (t : ℂ)) hdot
    _ = _ := by push_cast; ring

theorem uniformCenteringPhase_mul_star {d n : ℕ} (Ω : ℝ)
    (node : Fin n → Point d) (j : Fin n) :
    uniformCenteringPhase Ω node j * star (uniformCenteringPhase Ω node j) = 1 := by
  let t : ℝ := Ω / 2 * ∑ k, node j k
  have ht : (starRingEnd ℂ) (Complex.I * (t : ℂ)) = -Complex.I * (t : ℂ) := by
    simp
  change Complex.exp (Complex.I * (t : ℂ)) *
    (starRingEnd ℂ) (Complex.exp (Complex.I * (t : ℂ))) = 1
  rw [← Complex.exp_conj, ht, ← Complex.exp_add]
  simp

theorem uniformCenteringUnitary_mem_unitaryGroup {d n : ℕ}
    (Ω : ℝ) (node : Fin n → Point d) :
    uniformCenteringUnitary Ω node ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [uniformCenteringUnitary, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [Matrix.diagonal_apply] using uniformCenteringPhase_mul_star Ω node i
  · simp [hij]

theorem uniformCenteringPhase_cancels {d n : ℕ} (Ω : ℝ)
    (node : Fin n → Point d) (j : Fin n) :
    uniformCenteringPhase Ω node j *
      Complex.exp (-Complex.I * (Ω * ∑ k, node j k : ℝ)) *
      uniformCenteringPhase Ω node j = 1 := by
  let t : ℝ := Ω / 2 * ∑ k, node j k
  have ht : Ω * ∑ k, node j k = 2 * t := by dsimp [t]; ring
  rw [ht]
  change Complex.exp (Complex.I * (t : ℂ)) *
    Complex.exp (-Complex.I * ((2 * t : ℝ) : ℂ)) *
    Complex.exp (Complex.I * (t : ℂ)) = 1
  rw [← Complex.exp_add, ← Complex.exp_add]
  have hzero : Complex.I * (t : ℂ) +
      -Complex.I * ((2 * t : ℝ) : ℂ) + Complex.I * (t : ℂ) = 0 := by
    push_cast
    ring
  rw [hzero]
  simp

theorem uniformCentering_diagonal_amplitude {d n : ℕ}
    (Ω : ℝ) (μ : AtomicMeasure d n) :
    uniformCenteringUnitary Ω μ.node *
      Matrix.diagonal (uniformPhaseAmplitude Ω μ) *
      uniformCenteringUnitary Ω μ.node = Matrix.diagonal μ.amplitude := by
  classical
  simp only [uniformCenteringUnitary, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  have hc := uniformCenteringPhase_cancels Ω μ.node j
  change uniformCenteringPhase Ω μ.node j *
      (μ.amplitude j * Complex.exp (-Complex.I *
        (Ω * ∑ k, μ.node j k : ℝ))) *
      uniformCenteringPhase Ω μ.node j = μ.amplitude j
  calc
    _ = μ.amplitude j *
        (uniformCenteringPhase Ω μ.node j *
          Complex.exp (-Complex.I * (Ω * ∑ k, μ.node j k : ℝ)) *
          uniformCenteringPhase Ω μ.node j) := by ring
    _ = μ.amplitude j := by rw [hc, mul_one]

theorem uniformNoiselessMatrix_eq_centered {d n s : ℕ}
    (Ω : ℝ) (μ : AtomicMeasure d n) (hs : 0 < s) :
    uniformNoiselessMatrix s Ω μ =
      centeredUniformVandermonde s Ω μ.node *
        Matrix.diagonal μ.amplitude *
        (centeredUniformVandermonde s Ω μ.node)ᵀ := by
  classical
  rw [uniformNoiselessMatrix,
    uniformVandermonde_eq_centered_mul_unitary Ω μ.node hs,
    Matrix.transpose_mul]
  rw [show (uniformCenteringUnitary Ω μ.node)ᵀ =
      uniformCenteringUnitary Ω μ.node by
      simp [uniformCenteringUnitary, Matrix.diagonal_transpose]]
  calc
    _ = (centeredUniformVandermonde s Ω μ.node *
          (uniformCenteringUnitary Ω μ.node *
            Matrix.diagonal (uniformPhaseAmplitude Ω μ) *
            uniformCenteringUnitary Ω μ.node)) *
          (centeredUniformVandermonde s Ω μ.node)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [uniformCentering_diagonal_amplitude]

/-- Right multiplication by a unitary matrix preserves every singular value. -/
theorem matrixSingularValue_mul_unitary {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (U : Matrix n n ℂ)
    (hU : U * Uᴴ = 1) (i : ℕ) :
    matrixSingularValue (A * U) i = matrixSingularValue A i := by
  classical
  have hgram : (A * U)ᴴ * (A * U) = Uᴴ * (Aᴴ * A) * U := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hchar : ((A * U)ᴴ * (A * U)).charpoly = (Aᴴ * A).charpoly := by
    rw [hgram]
    calc
      (Uᴴ * (Aᴴ * A) * U).charpoly =
          (U * (Uᴴ * (Aᴴ * A))).charpoly :=
        Matrix.charpoly_mul_comm _ _
      _ = (Aᴴ * A).charpoly := by
        rw [← Matrix.mul_assoc, hU, one_mul]
  have hlinchar (B : Matrix m n ℂ) :
      (B.toEuclideanLin.adjoint ∘ₗ B.toEuclideanLin).charpoly =
        (Bᴴ * B).charpoly := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [← Matrix.toLpLin_mul 2 2 2 Bᴴ B]
    change ((Matrix.toLin (EuclideanSpace.basisFun n ℂ).toBasis
      (EuclideanSpace.basisFun n ℂ).toBasis) (Bᴴ * B)).charpoly = _
    exact Matrix.charpoly_toLin _ _
  have heig :=
    (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff
      (A * U).toEuclideanLin.isSymmetric_adjoint_comp_self
      (finrank_euclideanSpace (𝕜 := ℂ) (ι := n))
      A.toEuclideanLin.isSymmetric_adjoint_comp_self
      (finrank_euclideanSpace (𝕜 := ℂ) (ι := n))).2
      (by simpa only [hlinchar] using hchar)
  by_cases hi : i < Fintype.card n
  · change (A * U).toEuclideanLin.singularValues i =
      A.toEuclideanLin.singularValues i
    rw [(A * U).toEuclideanLin.singularValues_of_lt
      (finrank_euclideanSpace (𝕜 := ℂ) (ι := n)) hi,
      A.toEuclideanLin.singularValues_of_lt
      (finrank_euclideanSpace (𝕜 := ℂ) (ι := n)) hi,
      heig]
  · have hi' : Fintype.card n ≤ i := Nat.le_of_not_lt hi
    change (A * U).toEuclideanLin.singularValues i =
      A.toEuclideanLin.singularValues i
    rw [(A * U).toEuclideanLin.singularValues_of_finrank_le
      (by simpa only [finrank_euclideanSpace] using hi'),
      A.toEuclideanLin.singularValues_of_finrank_le
      (by simpa only [finrank_euclideanSpace] using hi')]

/-- Manuscript Lemma `lem:nonnegative_to_centered`. -/
theorem uniformVandermonde_centering {d n s : ℕ}
    (Ω : ℝ) (μ : AtomicMeasure d n)
    (hs : 0 < s) (_hseven : Even s) :
    uniformCenteringUnitary Ω μ.node ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
    uniformVandermonde s Ω μ.node =
      centeredUniformVandermonde s Ω μ.node *
        uniformCenteringUnitary Ω μ.node ∧
    (∀ i : ℕ, matrixSingularValue (uniformVandermonde s Ω μ.node) i =
      matrixSingularValue (centeredUniformVandermonde s Ω μ.node) i) ∧
    uniformNoiselessMatrix s Ω μ =
      centeredUniformVandermonde s Ω μ.node *
        Matrix.diagonal μ.amplitude *
        (centeredUniformVandermonde s Ω μ.node)ᵀ := by
  have hunit := uniformCenteringUnitary_mem_unitaryGroup Ω μ.node
  refine ⟨hunit, uniformVandermonde_eq_centered_mul_unitary Ω μ.node hs,
    ?_, uniformNoiselessMatrix_eq_centered Ω μ hs⟩
  intro i
  rw [uniformVandermonde_eq_centered_mul_unitary Ω μ.node hs]
  exact matrixSingularValue_mul_unitary _ _
    (Unitary.mul_star_self_of_mem hunit) i

end
end NumDetect
end LeanNumDetect
