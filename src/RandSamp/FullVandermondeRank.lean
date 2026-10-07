import RandSamp.MultiClumpModel
import RandSamp.SquareVandermonde
import RandSamp.LeverageSampling

/-! Distinct angular nodes make the full consecutive-frequency Gram matrix
positive definite as soon as there are at least as many rows as columns. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators ComplexOrder

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

theorem distinctAngularNodes_phase_injective {n : ℕ} (Y : Fin n → ℝ)
    (hY : DistinctAngularNodes Y) :
    Function.Injective (fun j => Complex.exp (Complex.I * (Y j : ℂ))) := by
  intro i j he
  by_contra hij
  obtain ⟨p, hp⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have him := congrArg Complex.im hp
  have hreal : Y i - Y j + 2 * Real.pi * ((-p : ℤ) : ℝ) = 0 := by
    norm_num [Complex.add_im, Complex.mul_im, Complex.mul_re] at him
    push_cast
    linarith
  exact hY i j hij (-p) hreal

theorem fourierRow_eq_phase_power {n : ℕ} (Y : Fin n → ℝ) (k : ℕ) (j : Fin n) :
    fourierRow Y k j = Complex.exp (Complex.I * (Y j : ℂ)) ^ k := by
  rw [← Complex.exp_nat_mul]
  unfold fourierRow
  congr 1
  push_cast
  ring

theorem powerVandermonde_mulVec_injective {n : ℕ} (z : Fin n → ℂ)
    (hz : Function.Injective z) : Function.Injective (powerVandermonde z).mulVec := by
  let C : Matrix (Fin n) (Fin n) ℂ := fun j k => lagrangeCoefficientRow z j k
  have hCV : C * powerVandermonde z = 1 := by
    ext j k
    simp only [Matrix.mul_apply, C, Matrix.one_apply]
    exact lagrangeCoefficientRow_interpolates z hz j k
  intro u v he
  have h := congrArg (fun w => C *ᵥ w) he
  simpa only [Matrix.mulVec_mulVec, hCV, Matrix.one_mulVec] using h

/-- Extracting the first `n` rows reduces full Fourier injectivity to the
ordinary square power Vandermonde matrix. -/
theorem angularDistinct_fullVandermonde_mulVec_injective {M n : ℕ}
    (hnM : n ≤ M + 1) (Y : Fin n → ℝ) (hY : DistinctAngularNodes Y) :
    Function.Injective (fullVandermonde M Y).mulVec := by
  have hsqrt : (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by positivity : (0 : ℝ) < (M + 1 : ℕ))
  intro u v huv
  apply powerVandermonde_mulVec_injective
    (fun j => Complex.exp (Complex.I * (Y j : ℂ)))
    (distinctAngularNodes_phase_injective Y hY)
  funext k
  let kM : Fin (M + 1) := ⟨k.val, k.isLt.trans_le hnM⟩
  have hk := congrFun huv kM
  simp only [Matrix.mulVec, dotProduct, fullVandermonde, mul_assoc,
    ← Finset.mul_sum] at hk
  apply mul_left_cancel₀ hsqrt at hk
  simpa only [Matrix.mulVec, dotProduct, powerVandermonde,
    fourierRow_eq_phase_power] using hk

/-- The population-mean normalization equals the matrix `A_M* A_M`. -/
theorem fullGram_eq_fullVandermonde_gram {M n : ℕ} (Y : Fin n → ℝ) :
    fullGram M Y = (fullVandermonde M Y)ᴴ * fullVandermonde M Y := by
  have hscalar : star (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
      (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ = ((M + 1 : ℕ) : ℂ)⁻¹ := by
    simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
    rw [← _root_.mul_inv_rev, ← pow_two, ← Complex.ofReal_pow,
      Real.sq_sqrt (Nat.cast_nonneg (M + 1)), Complex.ofReal_natCast]
  ext i j
  simp only [fullGram, mean, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    fourierPopulation, fourierRowGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    fullVandermonde, star_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show star (fourierRow Y k.val i) *
      star (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
      ((Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ * fourierRow Y k.val j) =
      (star (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹) *
          (star (fourierRow Y k.val i) * fourierRow Y k.val j) by ring, hscalar]

/-- Distinct angular sources imply a positive definite full normalized Gram
matrix. This applies in particular under `M ≥ n` in the multiclump theorem. -/
theorem angularDistinct_fullGram_posDef {M n : ℕ} (hnM : n ≤ M + 1)
    (Y : Fin n → ℝ) (hY : DistinctAngularNodes Y) :
    (fullGram M Y).PosDef := by
  rw [fullGram_eq_fullVandermonde_gram]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (angularDistinct_fullVandermonde_mulVec_injective hnM Y hY)

end

end LeanNumDetect.RandSamp
