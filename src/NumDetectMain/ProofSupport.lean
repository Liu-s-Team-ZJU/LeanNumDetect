import NumDetectMain.Matrices
import General.MatrixAnalysis.SingularValueBounds
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
Reusable finite-dimensional matrix facts used by the NumDetect main proofs.

This file contains only proved reductions.  In particular, the Fourier matrix
identities below fix all phase and normalization conventions explicitly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace LeanNumDetect
namespace NumDetect

noncomputable section

theorem dot_add_right {d : ℕ} (x y z : Point d) :
    dot x (y + z) = dot x y + dot x z := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_sub_right {d : ℕ} (x y z : Point d) :
    dot x (y - z) = dot x y - dot x z := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem dot_comm {d : ℕ} (x y : Point d) :
    dot x y = dot y x := by
  simp only [dot, mul_comm]

/-- Exact generalized Hankel factorization of Fourier data sampled at sums of frequencies. -/
theorem generalizedHankel_fourier_eq_hankelVandermondeFactor
    {d n : ℕ} {ι κ : Type*}
    (rowFrequency : ι → Point d) (columnFrequency : κ → Point d)
    (μ : AtomicMeasure d n) :
    generalizedHankel rowFrequency columnFrequency (fourier μ) =
      hankelVandermondeFactor rowFrequency columnFrequency μ := by
  classical
  ext i k
  rw [hankelVandermondeFactor, Matrix.mul_assoc]
  simp only [generalizedHankel, fourier,
    generalizedVandermonde, steeringVector, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.transpose_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [dot_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]
  rw [dot_comm (μ.node j) (rowFrequency i), dot_comm (μ.node j) (columnFrequency k)]
  ring

/-- Exact shifted generalized Hankel factorization. -/
theorem generalizedHankel_shiftedFourier
    {d n : ℕ} {ι κ : Type*}
    (rowFrequency : ι → Point d) (columnFrequency : κ → Point d)
    (shift : Point d) (μ : AtomicMeasure d n) :
    generalizedHankel rowFrequency columnFrequency
        (fun ω => fourier μ (ω - shift)) =
      generalizedVandermonde rowFrequency μ.node *
        Matrix.diagonal (fun j => μ.amplitude j *
          Complex.exp (-Complex.I * (dot (μ.node j) shift : ℂ))) *
        (generalizedVandermonde columnFrequency μ.node)ᵀ := by
  classical
  ext i k
  rw [Matrix.mul_assoc]
  simp only [generalizedHankel, fourier, generalizedVandermonde, steeringVector,
    Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [dot_sub_right, dot_add_right, Complex.ofReal_sub, Complex.ofReal_add]
  rw [show Complex.I *
      ((dot (μ.node j) (rowFrequency i) : ℂ) +
        dot (μ.node j) (columnFrequency k) - dot (μ.node j) shift) =
      Complex.I * (dot (μ.node j) (rowFrequency i) : ℂ) +
        (-Complex.I * (dot (μ.node j) shift : ℂ)) +
        Complex.I * (dot (μ.node j) (columnFrequency k) : ℂ) by ring]
  rw [Complex.exp_add, Complex.exp_add]
  rw [dot_comm (μ.node j) (rowFrequency i), dot_comm (μ.node j) (columnFrequency k)]
  ring

/-- Exact contiguous-grid factorization, including the manuscript's phase shift. -/
theorem uniformMeasurementMatrix_fourier_eq_noiseless
    {d n : ℕ} (s : ℕ) (Ω : ℝ) (μ : AtomicMeasure d n) (hs : 0 < s) :
    uniformMeasurementMatrix s Ω (fourier μ) =
      uniformNoiselessMatrix s Ω μ := by
  classical
  ext α β
  rw [uniformNoiselessMatrix, Matrix.mul_assoc]
  simp only [uniformMeasurementMatrix, uniformVandermonde,
    generalizedVandermonde, steeringVector, fourier, uniformPhaseAmplitude,
    Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hphase :
      dot (μ.node j) (fun k =>
          Ω / s * ((α k : ℝ) + (β k : ℝ) - s)) =
        dot (μ.node j) (uniformFrequency d s Ω α) +
        dot (μ.node j) (uniformFrequency d s Ω β) -
        Ω * ∑ k, μ.node j k := by
    simp only [dot, uniformFrequency]
    have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    calc
      _ = ∑ k, (μ.node j k * (Ω / s * (α k : ℝ)) +
          μ.node j k * (Ω / s * (β k : ℝ)) - Ω * μ.node j k) := by
        apply Finset.sum_congr rfl
        intro k _
        field_simp
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hphase, Complex.ofReal_sub, Complex.ofReal_add]
  rw [show Complex.I *
      ((dot (μ.node j) (uniformFrequency d s Ω α) : ℂ) +
        dot (μ.node j) (uniformFrequency d s Ω β) -
        (Ω * ∑ k, μ.node j k : ℝ)) =
      Complex.I * (dot (μ.node j) (uniformFrequency d s Ω α) : ℂ) +
        (-Complex.I * (Ω * ∑ k, μ.node j k : ℝ)) +
        Complex.I * (dot (μ.node j) (uniformFrequency d s Ω β) : ℂ) by
        push_cast
        ring]
  rw [Complex.exp_add, Complex.exp_add]
  rw [dot_comm (μ.node j) (uniformFrequency d s Ω α),
    dot_comm (μ.node j) (uniformFrequency d s Ω β)]
  ring

/-- Exact segmented-grid factorization, including the manuscript's phase shift. -/
theorem segmentedMeasurementMatrix_fourier_eq_noiseless
    {d n : ℕ} (m r D : ℕ) (μ : AtomicMeasure d n) :
    segmentedMeasurementMatrix m r D (fourier μ) =
      segmentedNoiselessMatrix m r D μ := by
  classical
  ext α β
  rw [segmentedNoiselessMatrix, Matrix.mul_assoc]
  simp only [segmentedMeasurementMatrix,
    segmentedVandermonde, segmentedColumnVandermonde, generalizedVandermonde,
    steeringVector, fourier, segmentedPhaseAmplitude, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.transpose_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hphase :
      dot (μ.node j) (fun k =>
          segmentedFrequency d m r D α k + segmentedFrequency d m r D β k -
            segmentedCutoff m r D) =
        dot (μ.node j) (segmentedFrequency d m r D α) +
        dot (μ.node j) (segmentedFrequency d m r D β) -
        (segmentedCutoff m r D : ℝ) * ∑ k, μ.node j k := by
    simp only [dot]
    calc
      _ = ∑ k, (μ.node j k * segmentedFrequency d m r D α k +
          μ.node j k * segmentedFrequency d m r D β k -
          (segmentedCutoff m r D : ℝ) * μ.node j k) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hphase, Complex.ofReal_sub, Complex.ofReal_add]
  rw [show Complex.I *
      ((dot (μ.node j) (segmentedFrequency d m r D α) : ℂ) +
        dot (μ.node j) (segmentedFrequency d m r D β) -
        ((segmentedCutoff m r D : ℝ) * ∑ k, μ.node j k : ℝ)) =
      Complex.I * (dot (μ.node j) (segmentedFrequency d m r D α) : ℂ) +
        (-Complex.I *
          ((segmentedCutoff m r D : ℝ) * ∑ k, μ.node j k : ℝ)) +
        Complex.I * (dot (μ.node j) (segmentedFrequency d m r D β) : ℂ) by
        push_cast
        ring]
  rw [Complex.exp_add, Complex.exp_add]
  rw [dot_comm (μ.node j) (segmentedFrequency d m r D α),
    dot_comm (μ.node j) (segmentedFrequency d m r D β)]
  ring

theorem matrixSingularValue_nonneg
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (i : ℕ) :
    0 ≤ matrixSingularValue A i :=
  A.toEuclideanLin.singularValues_nonneg i

theorem matrixSingularValue_antitone
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) :
    Antitone (matrixSingularValue A) :=
  A.toEuclideanLin.singularValues_antitone

/-- Every singular value at or beyond the matrix rank vanishes. -/
theorem matrixSingularValue_eq_zero_of_rank_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {i : ℕ} (hi : A.rank ≤ i) :
    matrixSingularValue A i = 0 := by
  rw [matrixSingularValue]
  apply (A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range).2
  change Module.finrank ℂ (LinearMap.range
    ((Matrix.toLin (EuclideanSpace.basisFun n ℂ).toBasis
      (EuclideanSpace.basisFun m ℂ).toBasis) A)) ≤ i
  rw [← A.rank_eq_finrank_range_toLin
    (EuclideanSpace.basisFun m ℂ).toBasis (EuclideanSpace.basisFun n ℂ).toBasis]
  exact hi

/-- A product through `n` columns has no nonzero singular values from index `n` onward. -/
theorem matrixSingularValue_mul_eq_zero_of_card_le
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) {i : ℕ}
    (hi : Fintype.card n ≤ i) :
    matrixSingularValue (A * B) i = 0 := by
  apply matrixSingularValue_eq_zero_of_rank_le
  exact (Matrix.rank_mul_le_left A B).trans
    ((Matrix.rank_le_card_width A).trans hi)

/-- A three-factor Vandermonde product through `n` columns has rank at most `n`. -/
theorem matrixSingularValue_three_mul_eq_zero_of_card_le
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    (A : Matrix m n ℂ) (D : Matrix n n ℂ) (B : Matrix n p ℂ) {i : ℕ}
    (hi : Fintype.card n ≤ i) :
    matrixSingularValue (A * D * B) i = 0 :=
  matrixSingularValue_mul_eq_zero_of_card_le (A * D) B hi

/-- A pointwise lower bound on diagonal moduli gives the corresponding Euclidean lower bound. -/
theorem norm_diagonal_mulVec_lower
    {n : Type*} [Fintype n] [DecidableEq n]
    (a : n → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (ha : ∀ j, c ≤ ‖a j‖) (x : EuclideanSpace ℂ n) :
    c * ‖x‖ ≤ ‖(EuclideanSpace.equiv n ℂ).symm (Matrix.diagonal a *ᵥ x)‖ := by
  change c * ‖x‖ ≤ ‖toLp 2 (Matrix.diagonal a *ᵥ ofLp x)‖
  rw [← sq_le_sq₀ (mul_nonneg hc (norm_nonneg x)) (norm_nonneg _)]
  rw [mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum,
    EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro j _
  change c ^ 2 * ‖ofLp x j‖ ^ 2 ≤
    ‖(Matrix.diagonal a *ᵥ ofLp x) j‖ ^ 2
  rw [Matrix.mulVec_diagonal]
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ hc (norm_nonneg _)).2 (ha j)) (sq_nonneg ‖x j‖)

/-- The intrinsic minimum amplitude is no larger than every amplitude modulus. -/
theorem minAmplitude_le {d n : ℕ} (μ : AtomicMeasure d n) (hn : 0 < n)
    (j : Fin n) :
    minAmplitude μ hn ≤ ‖μ.amplitude j‖ := by
  exact Finset.inf'_le _ (Finset.mem_univ j)

/-- A reduced nonempty atomic measure has strictly positive minimum amplitude. -/
theorem minAmplitude_pos {d n : ℕ} (μ : AtomicMeasure d n) (hn : 0 < n) :
    0 < minAmplitude μ hn := by
  rw [minAmplitude, Finset.lt_inf'_iff]
  intro j _
  exact norm_pos_iff.mpr (μ.amplitude_ne_zero j)

/-- The phase-shifted amplitudes in the uniform factorization preserve moduli. -/
theorem norm_uniformPhaseAmplitude {d n : ℕ} (Ω : ℝ)
    (μ : AtomicMeasure d n) (j : Fin n) :
    ‖uniformPhaseAmplitude Ω μ j‖ = ‖μ.amplitude j‖ := by
  rw [uniformPhaseAmplitude, norm_mul, Complex.norm_exp]
  simp

/-- The phase-shifted amplitudes in the segmented factorization preserve moduli. -/
theorem norm_segmentedPhaseAmplitude {d n : ℕ} (m r D : ℕ)
    (μ : AtomicMeasure d n) (j : Fin n) :
    ‖segmentedPhaseAmplitude m r D μ j‖ = ‖μ.amplitude j‖ := by
  rw [segmentedPhaseAmplitude, norm_mul, Complex.norm_exp]
  simp

theorem minAmplitude_le_norm_uniformPhaseAmplitude
    {d n : ℕ} (Ω : ℝ) (μ : AtomicMeasure d n) (hn : 0 < n) (j : Fin n) :
    minAmplitude μ hn ≤ ‖uniformPhaseAmplitude Ω μ j‖ := by
  rw [norm_uniformPhaseAmplitude]
  exact minAmplitude_le μ hn j

theorem minAmplitude_le_norm_segmentedPhaseAmplitude
    {d n : ℕ} (m r D : ℕ) (μ : AtomicMeasure d n) (hn : 0 < n) (j : Fin n) :
    minAmplitude μ hn ≤ ‖segmentedPhaseAmplitude m r D μ j‖ := by
  rw [norm_segmentedPhaseAmplitude]
  exact minAmplitude_le μ hn j

/-- The phase shifts used in the GHM factorizations preserve amplitude moduli. -/
theorem norm_phase_amplitude
    {d n : ℕ} (μ : AtomicMeasure d n) (phase : Fin n → ℝ) (j : Fin n) :
    ‖μ.amplitude j * Complex.exp (Complex.I * (phase j : ℂ))‖ =
      ‖μ.amplitude j‖ := by
  rw [norm_mul, Complex.norm_exp]
  simp

/-- A lower bound on every vector is multiplicative under matrix products.
This is the variational core of the usual minimum-singular-value product bound. -/
theorem mul_lower_bound
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) {a b : ℝ}
    (ha : 0 ≤ a)
    (hA : ∀ x : EuclideanSpace ℂ n,
      a * ‖x‖ ≤ ‖A.toEuclideanLin x‖)
    (hB : ∀ x : EuclideanSpace ℂ p,
      b * ‖x‖ ≤ ‖B.toEuclideanLin x‖)
    (x : EuclideanSpace ℂ p) :
    (a * b) * ‖x‖ ≤ ‖(A * B).toEuclideanLin x‖ := by
  calc
    (a * b) * ‖x‖ = a * (b * ‖x‖) := by ring
    _ ≤ a * ‖B.toEuclideanLin x‖ :=
      mul_le_mul_of_nonneg_left (hB x) ha
    _ ≤ ‖A.toEuclideanLin (B.toEuclideanLin x)‖ := hA _
    _ = ‖(A * B).toEuclideanLin x‖ := by
      rw [Matrix.toLpLin_mul_same]
      rfl

/-- `matrixSpectralNorm` is mathlib's Euclidean operator norm. -/
theorem matrixSpectralNorm_eq_l2_opNorm
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) :
    matrixSpectralNorm A = ‖A‖ :=
  rfl

theorem matrixSpectralNorm_mul_le
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    matrixSpectralNorm (A * B) ≤ matrixSpectralNorm A * matrixSpectralNorm B := by
  simpa only [matrixSpectralNorm_eq_l2_opNorm] using Matrix.l2_opNorm_mul A B

theorem matrixSpectralNorm_conjTranspose
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) :
    matrixSpectralNorm Aᴴ = matrixSpectralNorm A := by
  simpa only [matrixSpectralNorm_eq_l2_opNorm] using Matrix.l2_opNorm_conjTranspose A

/-- A pointwise entry bound controls the Euclidean operator norm by the
square root of the number of entries. -/
theorem matrixSpectralNorm_le_card_sqrt_mul
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (E : Matrix m n ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hentry : ∀ i j, ‖E i j‖ ≤ c) :
    matrixSpectralNorm E ≤
      Real.sqrt (Fintype.card m * Fintype.card n) * c := by
  simpa only [matrixSpectralNorm_eq_l2_opNorm] using
    matrix_l2OpNorm_le_card_sqrt_mul E hc hentry

/-- The same bound from strict pointwise control. Nonemptiness makes the
strict hypothesis imply that the entry bound is nonnegative. -/
theorem matrixSpectralNorm_le_card_sqrt_mul_of_lt
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    [Nonempty m] [Nonempty n]
    (E : Matrix m n ℂ) {c : ℝ} (hentry : ∀ i j, ‖E i j‖ < c) :
    matrixSpectralNorm E ≤
      Real.sqrt (Fintype.card m * Fintype.card n) * c := by
  have hc : 0 ≤ c :=
    (norm_nonneg (E (Classical.choice inferInstance)
      (Classical.choice inferInstance))).trans (hentry _ _).le
  exact matrixSpectralNorm_le_card_sqrt_mul E hc fun i j => (hentry i j).le

/-- Singular-value Weyl bound, in the additive perturbation form used by
NumDetect. -/
theorem abs_matrixSingularValue_add_sub_le_spectralNorm
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A E : Matrix m n ℂ) {i : ℕ} (hi : i < Fintype.card n) :
    |matrixSingularValue (A + E) i - matrixSingularValue A i| ≤
      matrixSpectralNorm E := by
  simpa only [matrixSpectralNorm_eq_l2_opNorm, add_sub_cancel_left] using
    abs_matrixSingularValue_sub_le_l2OpNorm (A + E) A hi

/-- Lower half of singular-value Weyl for an additive perturbation. -/
theorem matrixSingularValue_sub_spectralNorm_le_add
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A E : Matrix m n ℂ) {i : ℕ} (hi : i < Fintype.card n) :
    matrixSingularValue A i - matrixSpectralNorm E ≤
      matrixSingularValue (A + E) i := by
  have h := abs_matrixSingularValue_add_sub_le_spectralNorm A E hi
  rw [abs_le] at h
  linarith [h.1]

/-- Upper half of singular-value Weyl for an additive perturbation. -/
theorem matrixSingularValue_add_le_add_spectralNorm
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A E : Matrix m n ℂ) {i : ℕ} (hi : i < Fintype.card n) :
    matrixSingularValue (A + E) i ≤
      matrixSingularValue A i + matrixSpectralNorm E := by
  have h := abs_matrixSingularValue_add_sub_le_spectralNorm A E hi
  rw [abs_le] at h
  linarith [h.2]

/-- Entrywise perturbation control combined with the lower Weyl bound. -/
theorem matrixSingularValue_sub_entryBound_le_add
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A E : Matrix m n ℂ) {i : ℕ} (hi : i < Fintype.card n)
    {c : ℝ} (hc : 0 ≤ c) (hentry : ∀ r s, ‖E r s‖ ≤ c) :
    matrixSingularValue A i -
        Real.sqrt (Fintype.card m * Fintype.card n) * c ≤
      matrixSingularValue (A + E) i := by
  exact sub_le_sub_left (matrixSpectralNorm_le_card_sqrt_mul E hc hentry)
    (matrixSingularValue A i) |>.trans
      (matrixSingularValue_sub_spectralNorm_le_add A E hi)

/-- Entrywise perturbation control combined with the upper Weyl bound. -/
theorem matrixSingularValue_add_le_add_entryBound
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A E : Matrix m n ℂ) {i : ℕ} (hi : i < Fintype.card n)
    {c : ℝ} (hc : 0 ≤ c) (hentry : ∀ r s, ‖E r s‖ ≤ c) :
    matrixSingularValue (A + E) i ≤
      matrixSingularValue A i +
        Real.sqrt (Fintype.card m * Fintype.card n) * c := by
  refine (matrixSingularValue_add_le_add_spectralNorm A E hi).trans ?_
  gcongr
  exact matrixSpectralNorm_le_card_sqrt_mul E hc hentry

/-- An entrywise error budget preserves a strict singular-value threshold. -/
theorem threshold_lt_matrixSingularValue_add_of_entryBound
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A E : Matrix m n ℂ) {i : ℕ} (hi : i < Fintype.card n)
    {c threshold : ℝ} (hc : 0 ≤ c) (hentry : ∀ r s, ‖E r s‖ ≤ c)
    (hgap : threshold +
        Real.sqrt (Fintype.card m * Fintype.card n) * c <
      matrixSingularValue A i) :
    threshold < matrixSingularValue (A + E) i := by
  have h := matrixSingularValue_sub_entryBound_le_add A E hi hc hentry
  linarith

/-- An entrywise error budget also preserves being strictly below a threshold. -/
theorem matrixSingularValue_add_lt_threshold_of_entryBound
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A E : Matrix m n ℂ) {i : ℕ} (hi : i < Fintype.card n)
    {c threshold : ℝ} (hc : 0 ≤ c) (hentry : ∀ r s, ‖E r s‖ ≤ c)
    (hgap : matrixSingularValue A i +
        Real.sqrt (Fintype.card m * Fintype.card n) * c < threshold) :
    matrixSingularValue (A + E) i < threshold :=
  (matrixSingularValue_add_le_add_entryBound A E hi hc hentry).trans_lt hgap

/-- Minimum-singular-value lower bound for a product with a diagonal middle
factor. The dimension hypothesis is exactly what is needed for index
`card n - 1` to exist in the domain of the right factor. -/
theorem matrixSingularValue_diagonal_threeFactor_lower
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p]
    (V₁ : Matrix m n ℂ) (a : n → ℂ) (V₂T : Matrix n p ℂ)
    (hn : 0 < Fintype.card n) (hnp : Fintype.card n ≤ Fintype.card p)
    {amin : ℝ} (hamin : 0 ≤ amin) (ha : ∀ j, amin ≤ ‖a j‖) :
    matrixSingularValue V₁ (Fintype.card n - 1) * amin *
        matrixSingularValue V₂T (Fintype.card n - 1) ≤
      matrixSingularValue (V₁ * Matrix.diagonal a * V₂T)
        (Fintype.card n - 1) :=
  matrixSingularValue_threeFactor_lower V₁ a V₂T hn hnp hamin ha

/-- Project full column rank is the injectivity condition used by the
Euclidean singular-value API. -/
theorem toEuclideanLin_injective_of_fullColumnRank
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hA : HasFullColumnRank A) :
    Function.Injective A.toEuclideanLin := by
  intro x y hxy
  apply WithLp.ofLp_injective
  apply hA
  exact congrArg ofLp hxy

/-- A nonempty full-column-rank matrix has positive last column singular value. -/
theorem matrixLastSingularValue_pos_of_fullColumnRank
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hn : 0 < Fintype.card n)
    (hA : HasFullColumnRank A) :
    0 < matrixSingularValue A (Fintype.card n - 1) := by
  apply A.toEuclideanLin.injective_iff_forall_lt_finrank_singularValues_pos.mp
    (toEuclideanLin_injective_of_fullColumnRank A hA)
  simpa using Nat.sub_lt hn Nat.zero_lt_one

/-- The manuscript's diagonal-transpose product bound. Full column rank of
`V₂` identifies an `n`-dimensional conjugate range for the transpose factor. -/
theorem matrixSingularValue_diagonal_transpose_lower_of_fullColumnRank
    {m p : Type*} [Fintype m] [Fintype p] [DecidableEq p] {n : ℕ}
    (V₁ : Matrix m (Fin n) ℂ) (a : Fin n → ℂ)
    (V₂ : Matrix p (Fin n) ℂ)
    (hn : 0 < n) (hnp : n ≤ Fintype.card p)
    (hV₂ : HasFullColumnRank V₂)
    {amin : ℝ} (hamin : 0 ≤ amin) (ha : ∀ j, amin ≤ ‖a j‖) :
    amin * matrixSingularValue V₁ (n - 1) *
        matrixSingularValue V₂ (n - 1) ≤
      matrixSingularValue (V₁ * Matrix.diagonal a * V₂ᵀ) (n - 1) :=
  matrixSingularValue_diagonal_transpose_lower V₁ a V₂ hn hnp
    (toEuclideanLin_injective_of_fullColumnRank V₂ hV₂) hamin ha

/-- Under full column rank of both outer matrices and positive amplitudes,
the product lower bound is itself strictly positive. -/
theorem matrixSingularValue_diagonal_transpose_pos_lower
    {m p : Type*} {n : ℕ} [Fintype m] [Fintype p] [DecidableEq p]
    (V₁ : Matrix m (Fin n) ℂ) (a : Fin n → ℂ)
    (V₂ : Matrix p (Fin n) ℂ)
    (hn : 0 < n) (hnp : n ≤ Fintype.card p)
    (hV₁ : HasFullColumnRank V₁) (hV₂ : HasFullColumnRank V₂)
    {amin : ℝ} (hamin : 0 < amin) (ha : ∀ j, amin ≤ ‖a j‖) :
    0 < amin * matrixSingularValue V₁ (n - 1) *
          matrixSingularValue V₂ (n - 1) ∧
      amin * matrixSingularValue V₁ (n - 1) *
          matrixSingularValue V₂ (n - 1) ≤
        matrixSingularValue (V₁ * Matrix.diagonal a * V₂ᵀ) (n - 1) := by
  have hV₁pos : 0 < matrixSingularValue V₁ (n - 1) := by
    simpa only [Fintype.card_fin] using
      matrixLastSingularValue_pos_of_fullColumnRank V₁ (by simpa using hn) hV₁
  have hV₂pos : 0 < matrixSingularValue V₂ (n - 1) := by
    simpa only [Fintype.card_fin] using
      matrixLastSingularValue_pos_of_fullColumnRank V₂ (by simpa using hn) hV₂
  exact ⟨mul_pos (mul_pos hamin hV₁pos) hV₂pos,
    matrixSingularValue_diagonal_transpose_lower_of_fullColumnRank
      V₁ a V₂ hn hnp hV₂ hamin.le ha⟩

/-- Thin wrapper used when MUSIC noise spaces are represented by orthogonal projections. -/
theorem noiseSubspaceProjection_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Submodule ℂ E) [S.HasOrthogonalProjection] :
    ‖S.starProjection‖ ≤ 1 :=
  S.starProjection_norm_le

end

end NumDetect
end LeanNumDetect
