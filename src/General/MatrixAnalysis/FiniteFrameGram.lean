import General.Probability.WeightedLowerSampling

/-! Rank-one population matrices for finite complex frames. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.FrameMatrixBounds

open FiniteMatrixSampling
noncomputable section

def framePopulation {N d : ℕ} (f : Fin N → EuclideanSpace ℂ (Fin d))
    (k : Fin N) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => ofLp (f k) i * star (ofLp (f k) j)

theorem framePopulation_posSemidef {N d : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin d)) (k : Fin N) :
    (framePopulation f k).PosSemidef := by
  let A : Matrix (Fin 1) (Fin d) ℂ := fun _ j => star (ofLp (f k) j)
  have h : Aᴴ * A = framePopulation f k := by
    ext i j
    simp [A, framePopulation, Matrix.mul_apply]
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self A

theorem quadratic_framePopulation {N d : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin d)) (k : Fin N)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadratic (framePopulation f k) x = ‖⟪f k, x⟫_ℂ‖ ^ 2 := by
  have hvec : (framePopulation f k).toEuclideanLin x = ⟪f k, x⟫_ℂ • f k := by
    rw [Matrix.toLpLin_apply]
    ext i
    simp only [framePopulation, Matrix.mulVec, dotProduct,
      EuclideanSpace.inner_eq_star_dotProduct, Pi.star_apply,
      ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [quadratic, hvec, inner_smul_right, ← inner_conj_symm (f k) x]
  rw [Complex.conj_mul']
  simp only [RCLike.norm_conj, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem trace_mul_framePopulation {N d : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin d)) (k : Fin N)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    (A * framePopulation f k).trace.re = quadratic A (f k) := by
  unfold quadratic
  rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
  congr 1
  change (∑ i, ∑ j, A i j * (ofLp (f k) j * star (ofLp (f k) i))) =
    ∑ i, (∑ j, A i j * ofLp (f k) j) * star (ofLp (f k) i)
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem trace_mul_weightedMean {N d : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin d)) (w : Fin N → ℝ)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    (A * mean (weightedPopulation (framePopulation f) w)).trace.re =
      (N : ℝ)⁻¹ * ∑ k, w k * quadratic A (f k) := by
  rw [mean, Matrix.mul_smul, Matrix.mul_sum, Matrix.trace_smul, Matrix.trace_sum]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [weightedPopulation, Matrix.mul_smul, Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, trace_mul_framePopulation]

end
end LeanNumDetect.FrameMatrixBounds
