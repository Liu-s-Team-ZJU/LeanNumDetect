import General.Probability.FiniteMatrixSampling
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-!
Spectral formulas and convexity for the real trace of the exponential of a
complex Hermitian matrix. These are finite-dimensional proofs from the
orthonormal spectral theorem and scalar Jensen's inequality.
-/

set_option autoImplicit false

open Matrix NormedSpace
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace LeanNumDetect
namespace TraceExponential

variable {d : ℕ}

/-- The real trace of a matrix exponential. -/
noncomputable def traceExp (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (Matrix.trace (exp A)).re

theorem traceExp_eq_sum {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    traceExp A = ∑ i, Real.exp (hA.eigenvalues i) := by
  rw [traceExp, ← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint,
    hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle]
  simp [Complex.exp_ofReal_re]

theorem traceExp_nonneg {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    0 ≤ traceExp A := by
  rw [traceExp_eq_sum hA]
  exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le

@[simp] theorem traceExp_zero : traceExp (0 : Matrix (Fin d) (Fin d) ℂ) = d := by
  simp [traceExp]

theorem cfc_apply_eigenvector {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (j : Fin d) :
    (cfc f A).toEuclideanLin (hA.eigenvectorBasis j) =
      (f (hA.eigenvalues j) : ℂ) • hA.eigenvectorBasis j := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  apply WithLp.ofLp_injective
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul,
    ← Matrix.mulVec_mulVec,
    hA.star_eigenvectorUnitary_mulVec, Matrix.diagonal_mulVec_single]
  simp

theorem exp_apply_eigenvector {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (j : Fin d) :
    (exp A).toEuclideanLin (hA.eigenvectorBasis j) =
      (Real.exp (hA.eigenvalues j) : ℂ) • hA.eigenvectorBasis j := by
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
  exact cfc_apply_eigenvector hA Real.exp j

theorem quadratic_eq_sum_of_eigenbasis (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (v : Fin d → ℝ) (hv : ∀ i, A.toEuclideanLin (b i) = (v i : ℂ) • b i)
    (x : EuclideanSpace ℂ (Fin d)) :
    FiniteMatrixSampling.quadratic A x = ∑ i, v i * ‖⟪b i, x⟫_ℂ‖ ^ 2 := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have he (i : Fin d) :
      ⟪b i, A.toEuclideanLin x⟫_ℂ = (v i : ℂ) * ⟪b i, x⟫_ℂ := by
    rw [← hs, hv]
    rw [inner_smul_left]
    simp only [Complex.conj_ofReal]
  unfold FiniteMatrixSampling.quadratic
  rw [← b.sum_inner_mul_inner x (A.toEuclideanLin x), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [he, mul_left_comm]
  change RCLike.re ((v i) • (⟪x, b i⟫_ℂ * ⟪b i, x⟫_ℂ)) = _
  rw [RCLike.smul_re, inner_mul_symm_re_eq_norm, norm_mul,
    ← inner_conj_symm x (b i), RCLike.norm_conj, ← pow_two]

theorem quadratic_eq_sum {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    FiniteMatrixSampling.quadratic A x =
      ∑ i, hA.eigenvalues i * ‖⟪hA.eigenvectorBasis i, x⟫_ℂ‖ ^ 2 := by
  apply quadratic_eq_sum_of_eigenbasis A hA
  intro i
  apply WithLp.ofLp_injective
  simpa using hA.mulVec_eigenvectorBasis i

theorem quadratic_exp_eq_sum {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    FiniteMatrixSampling.quadratic (exp A) x =
      ∑ i, Real.exp (hA.eigenvalues i) * ‖⟪hA.eigenvectorBasis i, x⟫_ℂ‖ ^ 2 :=
  quadratic_eq_sum_of_eigenbasis (exp A) hA.exp hA.eigenvectorBasis
    (Real.exp ∘ hA.eigenvalues) (exp_apply_eigenvector hA) x

/-- Scalar Jensen in an orthonormal eigenbasis. -/
theorem exp_quadratic_le {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) (hx : ‖x‖ = 1) :
    Real.exp (FiniteMatrixSampling.quadratic A x) ≤
      FiniteMatrixSampling.quadratic (exp A) x := by
  rw [quadratic_eq_sum hA, quadratic_exp_eq_sum hA]
  have hsum : ∑ i, ‖⟪hA.eigenvectorBasis i, x⟫_ℂ‖ ^ 2 = 1 := by
    rw [hA.eigenvectorBasis.sum_sq_norm_inner_right, hx, one_pow]
  simpa only [smul_eq_mul, mul_comm] using
    convexOn_exp.map_sum_le (t := Finset.univ)
      (fun i _ => sq_nonneg ‖⟪hA.eigenvectorBasis i, x⟫_ℂ‖) hsum
      (fun i _ => Set.mem_univ (hA.eigenvalues i))

theorem quadratic_exp_le_traceExp {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) (hx : ‖x‖ = 1) :
    FiniteMatrixSampling.quadratic (exp A) x ≤ traceExp A := by
  rw [quadratic_exp_eq_sum hA, traceExp_eq_sum hA]
  apply Finset.sum_le_sum
  intro i _
  have hi : ‖⟪hA.eigenvectorBasis i, x⟫_ℂ‖ ^ 2 ≤ 1 := by
    have hi := norm_inner_le_norm (𝕜 := ℂ) (hA.eigenvectorBasis i) x
    rw [hA.eigenvectorBasis.orthonormal.1, hx, mul_one] at hi
    nlinarith [norm_nonneg ⟪hA.eigenvectorBasis i, x⟫_ℂ]
  exact mul_le_of_le_one_right (Real.exp_pos _).le hi

theorem exp_quadratic_le_traceExp {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) (hx : ‖x‖ = 1) :
    Real.exp (FiniteMatrixSampling.quadratic A x) ≤ traceExp A :=
  (exp_quadratic_le hA x hx).trans (quadratic_exp_le_traceExp hA x hx)

theorem trace_eq_sum_quadratic (A : Matrix (Fin d) (Fin d) ℂ)
    (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) :
    A.trace.re = ∑ i, FiniteMatrixSampling.quadratic A (b i) := by
  have h := LinearMap.trace_eq_sum_inner A.toEuclideanLin b
  have ht : LinearMap.trace ℂ _ A.toEuclideanLin = A.trace :=
    A.trace_toLin_eq (PiLp.basisFun 2 ℂ (Fin d))
  rw [ht] at h
  simpa [FiniteMatrixSampling.quadratic] using congrArg Complex.re h

theorem sum_exp_quadratic_le_traceExp {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian)
    (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) :
    (∑ i, Real.exp (FiniteMatrixSampling.quadratic A (b i))) ≤ traceExp A := by
  rw [traceExp, trace_eq_sum_quadratic (exp A) b]
  exact Finset.sum_le_sum fun i _ => exp_quadratic_le hA (b i) (b.orthonormal.1 i)

theorem quadratic_add (A B : Matrix (Fin d) (Fin d) ℂ)
    (x : EuclideanSpace ℂ (Fin d)) :
    FiniteMatrixSampling.quadratic (A + B) x =
      FiniteMatrixSampling.quadratic A x + FiniteMatrixSampling.quadratic B x := by
  simp [FiniteMatrixSampling.quadratic, map_add, inner_add_right]

theorem quadratic_real_smul (A : Matrix (Fin d) (Fin d) ℂ)
    (a : ℝ) (x : EuclideanSpace ℂ (Fin d)) :
    FiniteMatrixSampling.quadratic (a • A) x =
      a * FiniteMatrixSampling.quadratic A x := by
  have he : a • A = (a : ℂ) • A := by ext i j; simp [Complex.real_smul]
  rw [he, FiniteMatrixSampling.quadratic_smul_matrix]

theorem quadratic_eigenvector {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (i : Fin d) :
    FiniteMatrixSampling.quadratic A (hA.eigenvectorBasis i) = hA.eigenvalues i := by
  rw [quadratic_eq_sum hA]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hA.eigenvectorBasis.inner_eq_ite, hji]
  · simp

/-- Convexity of the trace exponential on Hermitian matrices. -/
theorem traceExp_convex_combination {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    traceExp (a • A + b • B) ≤ a * traceExp A + b * traceExp B := by
  have hC : (a • A + b • B).IsHermitian :=
    (hA.smul (isSelfAdjoint_iff.mpr (star_trivial a))).add
      (hB.smul (isSelfAdjoint_iff.mpr (star_trivial b)))
  let e := hC.eigenvectorBasis
  calc
    traceExp (a • A + b • B) =
        ∑ i, Real.exp (FiniteMatrixSampling.quadratic (a • A + b • B) (e i)) := by
      simp only [e, quadratic_eigenvector, traceExp_eq_sum hC]
    _ ≤ ∑ i, (a * Real.exp (FiniteMatrixSampling.quadratic A (e i)) +
        b * Real.exp (FiniteMatrixSampling.quadratic B (e i))) := by
      apply Finset.sum_le_sum
      intro i _
      rw [quadratic_add, quadratic_real_smul, quadratic_real_smul]
      exact convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
    _ = a * (∑ i, Real.exp (FiniteMatrixSampling.quadratic A (e i))) +
        b * (∑ i, Real.exp (FiniteMatrixSampling.quadratic B (e i))) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * traceExp A + b * traceExp B :=
      add_le_add (mul_le_mul_of_nonneg_left (sum_exp_quadratic_le_traceExp hA e) ha)
        (mul_le_mul_of_nonneg_left (sum_exp_quadratic_le_traceExp hB e) hb)

theorem convexOn_traceExp : ConvexOn ℝ Set.univ
    (fun A : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) => traceExp A.val) := by
  refine ⟨convex_univ, ?_⟩
  intro A _ B _ a b ha hb hab
  exact traceExp_convex_combination A.property B.property ha hb hab

end TraceExponential
end LeanNumDetect
