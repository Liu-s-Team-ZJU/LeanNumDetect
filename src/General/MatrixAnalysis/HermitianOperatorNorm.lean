import General.Probability.RestrictedQuadraticMoments
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Hermitian Euclidean operator norms and real quadratic forms

The Euclidean operator norm of a Hermitian matrix is characterized by
its absolute real quadratic form. The identity-shifted form gives the
usual equivalence between operator RIP bias and quadratic-energy bias.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped InnerProductSpace

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section

/-- For a Hermitian matrix, a Euclidean operator-norm bound is exactly
the uniform absolute bound on its real quadratic form. -/
theorem hermitian_operatorNorm_le_iff_quadratic_abs_le {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) {γ : ℝ} (hγ : 0 ≤ γ) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ γ ↔
      ∀ z : EuclideanSpace ℂ (Fin d),
        |FiniteMatrixSampling.quadratic A z| ≤ γ * ‖z‖ ^ 2 := by
  let T := A.toEuclideanLin.toContinuousLinearMap
  constructor
  · intro hnorm z
    calc
      |FiniteMatrixSampling.quadratic A z| ≤ ‖⟪z, T z⟫_ℂ‖ := by
        simpa only [FiniteMatrixSampling.quadratic, T, RCLike.re_eq_complex_re,
          LinearMap.coe_toContinuousLinearMap'] using
          (RCLike.abs_re_le_norm (⟪z, A.toEuclideanLin z⟫_ℂ))
      _ ≤ ‖z‖ * ‖T z‖ := norm_inner_le_norm _ _
      _ ≤ ‖z‖ * (‖T‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm z) (norm_nonneg z)
      _ = ‖T‖ * ‖z‖ ^ 2 := by ring
      _ ≤ γ * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right hnorm (sq_nonneg _)
  · intro hquad
    have hT : T.IsSymmetric := by
      change A.toEuclideanLin.IsSymmetric
      exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
    change ‖T‖ ≤ γ
    rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro z
    by_cases hz : z = 0
    · simpa only [hz, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero] using hγ
    have hn : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) 2
    have hinner : T.reApplyInnerSelf z = FiniteMatrixSampling.quadratic A z := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      change Complex.re ⟪A.toEuclideanLin z, z⟫_ℂ = Complex.re ⟪z, A.toEuclideanLin z⟫_ℂ
      simpa only [RCLike.re_eq_complex_re] using
        (inner_re_symm (𝕜 := ℂ) (A.toEuclideanLin z) z)
    change |T.reApplyInnerSelf z / ‖z‖ ^ 2| ≤ γ
    rw [hinner, abs_div, abs_of_nonneg (sq_nonneg ‖z‖), div_le_iff₀ hn]
    exact hquad z

@[simp] theorem quadratic_identity {d : ℕ} (z : EuclideanSpace ℂ (Fin d)) :
    FiniteMatrixSampling.quadratic (1 : Matrix (Fin d) (Fin d) ℂ) z = ‖z‖ ^ 2 := by
  unfold FiniteMatrixSampling.quadratic
  have he : (1 : Matrix (Fin d) (Fin d) ℂ).toEuclideanLin z = z := by
    change toLp 2 ((1 : Matrix (Fin d) (Fin d) ℂ) *ᵥ ofLp z) = z
    simp
  rw [he]
  simpa only [RCLike.re_eq_complex_re] using (inner_self_eq_norm_sq (𝕜 := ℂ) z)

@[simp] theorem quadratic_sub_identity {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (z : EuclideanSpace ℂ (Fin d)) :
    FiniteMatrixSampling.quadratic (A - 1) z =
      FiniteMatrixSampling.quadratic A z - ‖z‖ ^ 2 := by
  simpa only [quadraticTestLinearMap_apply, quadratic_identity] using
    (quadraticTestLinearMap z).map_sub A 1

/-- The usual spectral/Euclidean operator bias from identity equals the
quadratic-energy bias used in a relative Gram conversion. -/
theorem hermitian_operatorBias_le_iff_quadratic_bias_le {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) {γ : ℝ} (hγ : 0 ≤ γ) :
    ‖(A - 1).toEuclideanLin.toContinuousLinearMap‖ ≤ γ ↔
      ∀ z : EuclideanSpace ℂ (Fin d),
        |FiniteMatrixSampling.quadratic A z - ‖z‖ ^ 2| ≤ γ * ‖z‖ ^ 2 := by
  simpa only [quadratic_sub_identity] using
    hermitian_operatorNorm_le_iff_quadratic_abs_le (A - 1)
      (hA.sub Matrix.isHermitian_one) hγ

end

end LeanNumDetect.FiniteMatrixSampling
