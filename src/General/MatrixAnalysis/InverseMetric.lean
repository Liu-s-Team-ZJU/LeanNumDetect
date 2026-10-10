import General.Probability.WeightedLowerSampling
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Rank-one leverage relative to a positive-definite metric. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace LeanNumDetect.FrameMatrixBounds

open FiniteMatrixSampling
noncomputable section

theorem quadratic_sub {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadratic (A-B) x = quadratic A x - quadratic B x := by
  simp [quadratic, map_sub, inner_sub_right]

theorem quadratic_mono {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hAB : A ≤ B) (x : EuclideanSpace ℂ (Fin d)) : quadratic A x ≤ quadratic B x := by
  have h := quadratic_nonneg (Matrix.le_iff.mp hAB) x
  rw [quadratic_sub] at h
  linarith

theorem matrix_le_of_quadratic_le {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : ∀ x : EuclideanSpace ℂ (Fin d), quadratic A x ≤ quadratic B x) : A ≤ B := by
  apply Matrix.le_iff.mpr
  have hH : (B-A).IsHermitian := hB.sub hA
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro x
  apply RCLike.nonneg_iff.mpr
  refine ⟨?_, hH.im_star_dotProduct_mulVec_self x⟩
  have h := hAB (toLp 2 x)
  have hh : 0 ≤ quadratic (B-A) (toLp 2 x) := by rw [quadratic_sub]; linarith
  simpa only [quadratic, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct_comm, ofLp_toLp, RCLike.re_eq_complex_re] using hh

theorem inverse_quadratic_antitone {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : ∀ x : EuclideanSpace ℂ (Fin d), quadratic A x ≤ quadratic B x)
    (x : EuclideanSpace ℂ (Fin d)) : quadratic B⁻¹ x ≤ quadratic A⁻¹ x := by
  letI : CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) := {}
  have horder := matrix_le_of_quadratic_le hA.isHermitian hB.isHermitian hAB
  let a := hA.isUnit.unit
  let b := hB.isUnit.unit
  have ha : (a : Matrix (Fin d) (Fin d) ℂ) = A := hA.isUnit.unit_spec
  have hb : (b : Matrix (Fin d) (Fin d) ℂ) = B := hB.isUnit.unit_spec
  have h := CStarAlgebra.inv_le_inv (A := Matrix (Fin d) (Fin d) ℂ) (a := a) (b := b)
    (by simpa only [ha] using hA.posSemidef.nonneg) (by simpa only [ha, hb] using horder)
  rw [Matrix.coe_units_inv, Matrix.coe_units_inv, ha, hb] at h
  exact quadratic_mono h x

theorem inverse_eq_whitening_gram {d : ℕ}
    {G P : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosDef)
    (hP : IsUnit P) (hwhite : Pᴴ * G * P = 1) : G⁻¹ = P * Pᴴ := by
  letI := hP.invertible
  letI := hG.isUnit.invertible
  have hn : (P * Pᴴ) * G = 1 := by
    have h := congrArg (fun A => P * A * P⁻¹) hwhite
    simpa only [Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
      Matrix.mul_one, Matrix.one_mul] using h
  calc
    G⁻¹ = 1 * G⁻¹ := by simp
    _ = ((P * Pᴴ) * G) * G⁻¹ := by rw [hn]
    _ = P * Pᴴ := by simp only [Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
      Matrix.mul_one]

theorem quadratic_whitening_gram {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℂ) (r : EuclideanSpace ℂ (Fin d)) :
    quadratic (P * Pᴴ) r = ‖Pᴴ.toEuclideanLin r‖ ^ 2 := by
  have h : (Pᴴ)ᴴ * (1 : Matrix (Fin d) (Fin d) ℂ) * Pᴴ = P * Pᴴ := by simp
  rw [← h, quadratic_congruence, quadratic_identity]

/-- Cauchy--Schwarz after whitening bounds one row by its inverse-metric energy. -/
theorem row_energy_le_inverse_metric {d : ℕ}
    (G : Matrix (Fin d) (Fin d) ℂ) (hG : G.PosDef)
    (r x : EuclideanSpace ℂ (Fin d)) :
    ‖⟪r, x⟫_ℂ‖ ^ 2 ≤ quadratic G⁻¹ r * quadratic G x := by
  obtain ⟨P, hP, hwhite⟩ := exists_whitening_matrix G hG
  letI := hP.invertible
  let y := P⁻¹.toEuclideanLin x
  have hxy : P.toEuclideanLin y = x := by
    change (P.toEuclideanLin ∘ₗ P⁻¹.toEuclideanLin) x = x
    rw [← Matrix.toLpLin_mul_same, Matrix.mul_inv_of_invertible]
    simp
  have he : quadratic G x = ‖y‖ ^ 2 := by
    rw [← hxy, ← quadratic_congruence, hwhite, quadratic_identity]
  have hinner : ⟪r, x⟫_ℂ = ⟪Pᴴ.toEuclideanLin r, y⟫_ℂ := by
    rw [← hxy, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_left]
  rw [inverse_eq_whitening_gram hG hP hwhite, quadratic_whitening_gram, he, hinner]
  have h := norm_inner_le_norm (𝕜 := ℂ) (Pᴴ.toEuclideanLin r) y
  have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa only [mul_pow] using hh

end
end LeanNumDetect.FrameMatrixBounds
