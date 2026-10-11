import General.Fourier.CubeShiftBounds
import General.Fourier.CubeFrameBasis
import General.MatrixAnalysis.FiniteFrameGram
import RandSamp.MultidimensionalMultiClumpSampling

/-! Normalization of the Fourier cube and its whitened finite frame. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling CubeShiftBounds FrameMatrixBounds
noncomputable section

def cubeUnitRoots {d n : ℕ} (Y : Fin n → Fin d → ℝ) : Fin n → Fin d → ℂ :=
  fun j r => Complex.exp (Complex.I*(Y j r : ℂ))

@[simp] theorem norm_cubeUnitRoots {d n : ℕ} (Y : Fin n → Fin d → ℝ) (j : Fin n) (r : Fin d) :
    ‖cubeUnitRoots Y j r‖ = 1 := by
  simpa only [cubeUnitRoots, mul_comm] using Complex.norm_exp_ofReal_mul_I (Y j r)

theorem cubeRootMatrix_cubeUnitRoots {d M n : ℕ} (Y : Fin n → Fin d → ℝ) :
    cubeRootMatrix (cubeUnitRoots Y) (M+1) = cubeFourierRow (M := M) Y := by
  ext k j
  simp only [cubeRootMatrix, cubeUnitRoots, cubeFourierRow,
    ← Complex.exp_nat_mul, ← Complex.exp_sum,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem cubeRootGram_eq_sum_cubeFourierPopulation {d M n : ℕ}
    (Y : Fin n → Fin d → ℝ) :
    cubeRootGram (cubeUnitRoots Y) (M+1) = ∑ k, cubeFourierPopulation (M := M) Y k := by
  rw [cubeRootGram, cubeRootMatrix_cubeUnitRoots]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    cubeFourierPopulation, cubeFourierRowGram]

theorem cubeRootGram_eq_card_smul_cubeFullGram {d M n : ℕ}
    (Y : Fin n → Fin d → ℝ) :
    cubeRootGram (cubeUnitRoots Y) (M+1) = (((M+1)^d : ℕ) : ℂ) • cubeFullGram M Y := by
  rw [cubeRootGram_eq_sum_cubeFourierPopulation, cubeFullGram, finiteMean,
    smul_smul, card_cubeFrequency]
  have hN : ((((M+1)^d : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero d (Nat.succ_ne_zero M))
  rw [mul_inv_cancel₀ hN, one_smul]

theorem framePopulation_linear {N n : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin n)) (A : Matrix (Fin n) (Fin n) ℂ) (k : Fin N) :
    framePopulation (fun i => A.toEuclideanLin (f i)) k = A * framePopulation f k * Aᴴ := by
  ext i j
  simp only [framePopulation, Matrix.toLpLin_apply, PiLp.toLp_apply,
    Matrix.mulVec, dotProduct, star_sum, star_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem framePopulation_real_smul {N n : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin n)) (a : ℝ) (k : Fin N) :
    framePopulation (fun i => (a : ℂ) • f i) k = ((a^2 : ℝ) : ℂ) • framePopulation f k := by
  ext i j
  simp only [framePopulation, PiLp.smul_apply, smul_eq_mul, Matrix.smul_apply,
    star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
  ring


def cubeWhitenedFrame {d M n : ℕ} (Y : Fin n → Fin d → ℝ)
    (P : Matrix (Fin n) (Fin n) ℂ) : CubeFrequency d M → EuclideanSpace ℂ (Fin n) :=
  fun k => isotropicCubeRootRow (cubeUnitRoots Y) P (M+1) (fun r => (k r).val)

theorem cubeWhitenedFrame_population {d M n : ℕ} (Y : Fin n → Fin d → ℝ)
    (P : Matrix (Fin n) (Fin n) ℂ)
    (e : Fin (Fintype.card (CubeFrequency d M)) ≃ CubeFrequency d M)
    (k : Fin (Fintype.card (CubeFrequency d M))) :
    framePopulation (fun i => cubeWhitenedFrame Y P (e i)) k =
      ((((M+1)^d : ℕ) : ℂ)) • (Pᴴ * cubeFourierPopulation Y (e k) * P) := by
  let raw := fun i => rawCubeRootRow (cubeUnitRoots Y) (fun r => (e i r).val)
  have hr : framePopulation raw k = cubeFourierPopulation Y (e k) := by
    ext i j
    have he := congrFun (congrFun (cubeRootMatrix_cubeUnitRoots (M := M) Y) (e k))
    simp only [framePopulation, raw, rawCubeRootRow, PiLp.toLp_apply, star_star,
      cubeFourierPopulation, cubeFourierRowGram]
    simp only [cubeRootMatrix] at he
    rw [he i, he j]
  have hs := framePopulation_real_smul
    (fun i => Pᴴ.toEuclideanLin (raw i))
    (Real.sqrt ((((M+1)^d : ℕ) : ℝ))) k
  rw [framePopulation_linear, Matrix.conjTranspose_conjTranspose, hr] at hs
  simpa only [cubeWhitenedFrame, isotropicCubeRootRow, whitenedCubeRootRow,
    raw, Fintype.card_fin, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast] using hs

theorem mean_real_smul {N n : ℕ} (X : Fin N → Matrix (Fin n) (Fin n) ℂ) (a : ℝ) :
    mean (fun k => (a : ℂ) • X k) = (a : ℂ) • mean X := by
  simp only [mean, Finset.smul_sum, smul_smul, mul_comm]

theorem sampleMean_real_smul {N n m : ℕ}
    (X : Fin N → Matrix (Fin n) (Fin n) ℂ) (a : ℝ) (Ω : Sample N m) :
    sampleMean (fun k => (a : ℂ) • X k) Ω = (a : ℂ) • sampleMean X Ω := by
  simp only [sampleMean, sampleSum, Finset.smul_sum, smul_smul, mul_comm]

theorem cubeRootGram_posDef_of_cubeFullGram {d M n : ℕ}
    (Y : Fin n → Fin d → ℝ) (hG : (cubeFullGram M Y).PosDef) :
    (cubeRootGram (cubeUnitRoots Y) (M+1)).PosDef := by
  rw [cubeRootGram_eq_card_smul_cubeFullGram]
  apply hG.smul
  exact_mod_cast (show (0 : ℝ) < (((M+1)^d : ℕ) : ℝ) by
    exact_mod_cast pow_pos (Nat.succ_pos M) d)

end
end LeanNumDetect.RandSamp
