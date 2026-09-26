import General.MatrixAnalysis.SingularValueBounds
import Mathlib.Analysis.Complex.Exponential

/-!
The finite Fourier population and the normalized matrix obtained by selecting
rows. Nodes are real representatives of points of the angular torus.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators ComplexOrder

namespace LeanNumDetect.RandSamp

noncomputable section

/-- A row of the unnormalized consecutive-frequency Vandermonde matrix. -/
def fourierRow {s : ℕ} (Y : Fin s → ℝ) (k : ℕ) (j : Fin s) : ℂ :=
  Complex.exp (Complex.I * (((k : ℝ) * Y j : ℝ) : ℂ))

@[simp] theorem norm_fourierRow {s : ℕ} (Y : Fin s → ℝ) (k : ℕ) (j : Fin s) :
    ‖fourierRow Y k j‖ = 1 := by
  simpa [fourierRow, mul_comm] using Complex.norm_exp_ofReal_mul_I ((k : ℝ) * Y j)

/-- The positive rank-one summand contributed by one frequency. -/
def fourierRowGram {s : ℕ} (Y : Fin s → ℝ) (k : ℕ) : Matrix (Fin s) (Fin s) ℂ :=
  fun i j => star (fourierRow Y k i) * fourierRow Y k j

theorem fourierRowGram_posSemidef {s : ℕ} (Y : Fin s → ℝ) (k : ℕ) :
    (fourierRowGram Y k).PosSemidef := by
  let R : Matrix Unit (Fin s) ℂ := fun _ j => fourierRow Y k j
  have he : fourierRowGram Y k = Rᴴ * R := by
    ext i j
    simp [fourierRowGram, Matrix.mul_apply, R]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self R

/-- Fourier energy at a single frequency. -/
def fourierRowEnergy {s : ℕ} (Y : Fin s → ℝ) (k : ℕ) (z : Fin s → ℂ) : ℝ :=
  ‖∑ j, fourierRow Y k j * z j‖ ^ 2

theorem fourierRowGram_quadratic {s : ℕ} (Y : Fin s → ℝ) (k : ℕ)
    (z : Fin s → ℂ) :
    (star z ⬝ᵥ ((fourierRowGram Y k) *ᵥ z)).re = fourierRowEnergy Y k z := by
  have he : star z ⬝ᵥ ((fourierRowGram Y k) *ᵥ z) =
      star (∑ j, fourierRow Y k j * z j) * (∑ j, fourierRow Y k j * z j) := by
    simp only [dotProduct, Matrix.mulVec, fourierRowGram, Pi.star_apply,
      star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, RCLike.star_def, Complex.conj_mul']
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, fourierRowEnergy]

theorem fourierRowEnergy_nonneg {s : ℕ} (Y : Fin s → ℝ) (k : ℕ)
    (z : Fin s → ℂ) : 0 ≤ fourierRowEnergy Y k z := sq_nonneg _

/-- Each rank-one population matrix is bounded above by `s I`. -/
theorem fourierRowEnergy_le {s : ℕ} (Y : Fin s → ℝ) (k : ℕ)
    (z : Fin s → ℂ) : fourierRowEnergy Y k z ≤ (s : ℝ) * ∑ j, ‖z j‖ ^ 2 := by
  have hnorm : ‖∑ j, fourierRow Y k j * z j‖ ≤ ∑ j, ‖z j‖ := by
    simpa only [norm_mul, norm_fourierRow, one_mul] using
      norm_sum_le Finset.univ (fun j => fourierRow Y k j * z j)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin s => (1 : ℝ))
    (fun j => ‖z j‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2
    hnorm).trans hcs

/-- The manuscript's matrix `A_Ω`, with the selected frequencies as its row type. -/
def sampledVandermonde {N s : ℕ} (m : ℕ) (Y : Fin s → ℝ)
    (Ω : Finset (Fin N)) : Matrix Ω (Fin s) ℂ :=
  fun k j => (Real.sqrt (m : ℝ) : ℂ)⁻¹ * fourierRow Y k.val.val j

theorem sampledVandermonde_energy {N s : ℕ} (m : ℕ) (Y : Fin s → ℝ)
    (Ω : Finset (Fin N)) (z : EuclideanSpace ℂ (Fin s)) :
    ‖(sampledVandermonde m Y Ω).toEuclideanLin z‖ ^ 2 =
      (m : ℝ)⁻¹ * ∑ k ∈ Ω, fourierRowEnergy Y k.val (ofLp z) := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ k : Ω, ‖∑ j, (Real.sqrt (m : ℝ) : ℂ)⁻¹ *
    fourierRow Y k.val.val j * ofLp z j‖ ^ 2) = _
  simp_rw [mul_assoc, ← Finset.mul_sum, norm_mul, mul_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_coe_sort Ω (fun k => fourierRowEnergy Y k.val (ofLp z))

end

end LeanNumDetect.RandSamp
