import RandSamp.RandomModel
import General.Probability.FinitePopulationReindex

/-!
The Fourier population indexed by the integer cube `{0,...,M}^d`, together with
its uniform averages and the normalized matrix of selected rows. Nodes are
arbitrary real lifts of torus points; they need not form a Cartesian product.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The full set of integer frequencies in a `d`-dimensional cube. -/
abbrev CubeFrequency (d M : ℕ) := Fin d → Fin (M + 1)

@[simp] theorem card_cubeFrequency (d M : ℕ) :
    Fintype.card (CubeFrequency d M) = (M + 1) ^ d := by
  simp [CubeFrequency]

/-- One unnormalized Fourier row at a cube frequency. -/
def cubeFourierRow {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (k : CubeFrequency d M) (j : Fin s) : ℂ :=
  Complex.exp (Complex.I * ((∑ r, ((k r : ℕ) : ℝ) * Y j r : ℝ) : ℂ))

@[simp] theorem norm_cubeFourierRow {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (k : CubeFrequency d M) (j : Fin s) : ‖cubeFourierRow Y k j‖ = 1 := by
  simpa [cubeFourierRow, mul_comm] using
    Complex.norm_exp_ofReal_mul_I (∑ r, ((k r : ℕ) : ℝ) * Y j r)

/-- The positive rank-one matrix contributed by one cube frequency. -/
def cubeFourierRowGram {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (k : CubeFrequency d M) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => star (cubeFourierRow Y k i) * cubeFourierRow Y k j

theorem cubeFourierRowGram_posSemidef {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (k : CubeFrequency d M) : (cubeFourierRowGram Y k).PosSemidef := by
  let R : Matrix Unit (Fin s) ℂ := fun _ j => cubeFourierRow Y k j
  have he : cubeFourierRowGram Y k = Rᴴ * R := by
    ext i j
    simp [cubeFourierRowGram, Matrix.mul_apply, R]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self R

/-- The squared Fourier action of one cube frequency. -/
def cubeFourierRowEnergy {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (k : CubeFrequency d M) (z : Fin s → ℂ) : ℝ :=
  ‖∑ j, cubeFourierRow Y k j * z j‖ ^ 2

theorem cubeFourierRowGram_quadratic {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (k : CubeFrequency d M) (z : Fin s → ℂ) :
    (star z ⬝ᵥ ((cubeFourierRowGram Y k) *ᵥ z)).re =
      cubeFourierRowEnergy Y k z := by
  have he : star z ⬝ᵥ ((cubeFourierRowGram Y k) *ᵥ z) =
      star (∑ j, cubeFourierRow Y k j * z j) * (∑ j, cubeFourierRow Y k j * z j) := by
    simp only [dotProduct, Matrix.mulVec, cubeFourierRowGram, Pi.star_apply,
      star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, RCLike.star_def, Complex.conj_mul']
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, cubeFourierRowEnergy]

theorem cubeFourierRowEnergy_nonneg {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (k : CubeFrequency d M) (z : Fin s → ℂ) : 0 ≤ cubeFourierRowEnergy Y k z :=
  sq_nonneg _

/-- The uniform row bound is the number of nodes, independently of dimension. -/
theorem cubeFourierRowEnergy_le {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (k : CubeFrequency d M) (z : Fin s → ℂ) :
    cubeFourierRowEnergy Y k z ≤ (s : ℝ) * ∑ j, ‖z j‖ ^ 2 := by
  have hnorm : ‖∑ j, cubeFourierRow Y k j * z j‖ ≤ ∑ j, ‖z j‖ := by
    simpa only [norm_mul, norm_cubeFourierRow, one_mul] using
      norm_sum_le Finset.univ (fun j => cubeFourierRow Y k j * z j)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin s => (1 : ℝ))
    (fun j => ‖z j‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2
    hnorm).trans hcs

/-- The sampled cube Fourier matrix with normalization `1 / sqrt m`. -/
def cubeSampledVandermonde {d M s : ℕ} (m : ℕ) (Y : Fin s → Fin d → ℝ)
    (Ω : Finset (CubeFrequency d M)) : Matrix Ω (Fin s) ℂ :=
  fun k j => (Real.sqrt (m : ℝ) : ℂ)⁻¹ * cubeFourierRow Y k.val j

theorem cubeSampledVandermonde_energy {d M s : ℕ} (m : ℕ)
    (Y : Fin s → Fin d → ℝ) (Ω : Finset (CubeFrequency d M))
    (z : EuclideanSpace ℂ (Fin s)) :
    ‖(cubeSampledVandermonde m Y Ω).toEuclideanLin z‖ ^ 2 =
      (m : ℝ)⁻¹ * ∑ k ∈ Ω, cubeFourierRowEnergy Y k (ofLp z) := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ k : Ω, ‖∑ j, (Real.sqrt (m : ℝ) : ℂ)⁻¹ *
    cubeFourierRow Y k.val j * ofLp z j‖ ^ 2) = _
  simp_rw [mul_assoc, ← Finset.mul_sum, norm_mul, mul_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_coe_sort Ω (fun k => cubeFourierRowEnergy Y k (ofLp z))

theorem quadratic_cubeFourierRowGram {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (k : CubeFrequency d M) (z : EuclideanSpace ℂ (Fin s)) :
    FiniteMatrixSampling.quadratic (cubeFourierRowGram Y k) z =
      cubeFourierRowEnergy Y k (ofLp z) := by
  convert cubeFourierRowGram_quadratic Y k (ofLp z) using 1
  rw [FiniteMatrixSampling.quadratic, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

/-- The matrix-valued population, retaining each frequency's label. -/
def cubeFourierPopulation {d M s : ℕ} (Y : Fin s → Fin d → ℝ) :
    CubeFrequency d M → Matrix (Fin s) (Fin s) ℂ := cubeFourierRowGram Y

theorem cubeFourierPopulation_bound {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (k : CubeFrequency d M) (z : EuclideanSpace ℂ (Fin s)) :
    0 ≤ FiniteMatrixSampling.quadratic (cubeFourierPopulation Y k) z ∧
      FiniteMatrixSampling.quadratic (cubeFourierPopulation Y k) z ≤ (s : ℝ) * ‖z‖ ^ 2 := by
  rw [cubeFourierPopulation, quadratic_cubeFourierRowGram, EuclideanSpace.norm_sq_eq]
  exact ⟨cubeFourierRowEnergy_nonneg Y k (ofLp z), cubeFourierRowEnergy_le Y k (ofLp z)⟩

/-- The normalized full Gram matrix for all cube frequencies. -/
def cubeFullGram {d s : ℕ} (M : ℕ) (Y : Fin s → Fin d → ℝ) :
    Matrix (Fin s) (Fin s) ℂ :=
  finiteMean (cubeFourierPopulation (M := M) Y)

/-- The full average Gram energy uses all `(M+1)^d` frequencies. -/
theorem quadratic_cubeFourier_mean {d M s : ℕ} (Y : Fin s → Fin d → ℝ)
    (z : EuclideanSpace ℂ (Fin s)) :
    FiniteMatrixSampling.quadratic (finiteMean (cubeFourierPopulation (M := M) Y)) z =
      (((M : ℝ) + 1) ^ d)⁻¹ * ∑ k : CubeFrequency d M,
        cubeFourierRowEnergy Y k (ofLp z) := by
  rw [FiniteMatrixSampling.quadratic, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change (star (ofLp z) ⬝ᵥ (((Fintype.card (CubeFrequency d M) : ℂ)⁻¹ •
    ∑ k, cubeFourierPopulation Y k) *ᵥ ofLp z)).re = _
  simp only [Matrix.smul_mulVec, Matrix.sum_mulVec, dotProduct_smul, dotProduct_sum,
    smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.re_ofReal_mul, Complex.re_sum, cubeFourierPopulation,
    cubeFourierRowGram_quadratic]
  simp only [card_cubeFrequency, Nat.cast_pow, Nat.cast_add, Nat.cast_one]

/-- A sampled Gram average is exactly the squared action of the normalized
sampled Fourier matrix. -/
theorem quadratic_cubeFourier_sampleMean {d M s m : ℕ} (Y : Fin s → Fin d → ℝ)
    (Ω : FiniteSample (CubeFrequency d M) m) (z : EuclideanSpace ℂ (Fin s)) :
    FiniteMatrixSampling.quadratic (finiteSampleMean (cubeFourierPopulation Y) Ω) z =
      ‖(cubeSampledVandermonde m Y Ω.val).toEuclideanLin z‖ ^ 2 := by
  rw [cubeSampledVandermonde_energy]
  rw [FiniteMatrixSampling.quadratic, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  change (star (ofLp z) ⬝ᵥ (((m : ℂ)⁻¹ • ∑ k ∈ Ω.val, cubeFourierPopulation Y k) *ᵥ ofLp z)).re = _
  simp only [Matrix.smul_mulVec, Matrix.sum_mulVec, dotProduct_smul, dotProduct_sum,
    smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.re_ofReal_mul, Complex.re_sum, cubeFourierPopulation, cubeFourierRowGram_quadratic]

end

end LeanNumDetect.RandSamp
