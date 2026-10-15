import MultiTuran.DerivativeMatrix
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Trace

/-! # A finite Hilbert space estimate for differentiation

This is a linear algebra theorem. The boundary form and a spanning family of
imaginary eigenvectors control the operator, without requiring its eigenvectors
to be orthogonal or its eigenvalues to be distinct.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open Matrix

namespace LeanNumDetect.MultiTuran
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The coordinate energy of a bounded evaluation functional in an orthonormal
basis is at most the square of its bound. -/
theorem orthonormalBasis_functional_energy_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (L : E →ₗ[ℂ] ℂ) {K : ℝ}
    (hK : 0 ≤ K) (hL : ∀ f, ‖L f‖ ≤ K * ‖f‖) :
    (∑ i, ‖L (b i)‖ ^ 2) ≤ K ^ 2 := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  let A := L.toContinuousLinearMap
  let v := (InnerProductSpace.toDual ℂ E).symm A
  have hv : ‖v‖ ≤ K := by
    rw [show ‖v‖ = ‖A‖ from (InnerProductSpace.toDual ℂ E).symm.norm_map A]
    exact A.opNorm_le_bound hK hL
  have he : ∀ i, L (b i) = ⟪v, b i⟫_ℂ := by
    intro i
    exact (InnerProductSpace.toDual_symm_apply (y := A)).symm
  simp_rw [he]
  rw [b.sum_sq_norm_inner_left]
  exact (sq_le_sq₀ (norm_nonneg _) hK).2 hv

/-- A spanning imaginary eigenvector family bounds the negative real trace of
`T²`; repeated eigenvectors and repeated frequencies are allowed. -/
theorem neg_re_trace_square_le_of_spanning_eigenvectors {n : ℕ}
    (T : E →ₗ[ℂ] E) (frequency : Fin n → ℝ) (gen : Fin n → E) {W : ℝ}
    (hspan : Submodule.span ℂ (Set.range gen) = ⊤)
    (heigen : ∀ j, T (gen j) = (Complex.I * (frequency j : ℂ)) • gen j)
    (hfrequency : ∀ j, |frequency j| ≤ W) :
    -(LinearMap.trace ℂ E (T * T)).re ≤ (n : ℝ) * W ^ 2 := by
  classical
  let hs : (⊤ : Submodule ℂ E) ≤ Submodule.span ℂ (Set.range gen) := hspan.ge
  let b := Module.Basis.ofSpan hs
  let ι := (linearIndepOn_empty ℂ (id : E → E)).extend (Set.empty_subset (Set.range gen))
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have hbmem : ∀ i, b i ∈ Set.range gen := fun i =>
    Module.Basis.ofSpan_subset hs (Set.mem_range_self i)
  choose j hj using hbmem
  have hjinj : Function.Injective j := by
    intro i k hik
    apply b.injective
    rw [← hj i, ← hj k, hik]
  have hcard : Fintype.card ι ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective j hjinj
  have heig : ∀ i, T (b i) = (Complex.I * (frequency (j i) : ℂ)) • b i := by
    intro i
    rw [← hj i, heigen]
  have heig2 : ∀ i, (T * T) (b i) = (-(frequency (j i) : ℂ)^2) • b i := by
    intro i
    simp only [Module.End.mul_apply, heig, map_smul, smul_smul]
    congr 1
    calc
      _ = Complex.I^2 * (frequency (j i) : ℂ)^2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  have hdiag : LinearMap.toMatrix b b (T*T) =
      Matrix.diagonal (fun i => -(frequency (j i) : ℂ)^2) := by
    ext i k
    by_cases hik : i = k
    · subst k
      simp [LinearMap.toMatrix_apply, heig2, Matrix.diagonal_apply]
    · simp [LinearMap.toMatrix_apply, heig2, Matrix.diagonal_apply, Finsupp.single_apply,
        hik, Ne.symm hik]
  have ht : (LinearMap.trace ℂ E (T*T)).re = -(∑ i : ι, frequency (j i)^2) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b, hdiag, Matrix.trace_diagonal]
    simp [Complex.mul_re, pow_two]
    rfl
  rw [ht, neg_neg]
  calc
    _ ≤ ∑ _i : ι, W^2 := by
      apply Finset.sum_le_sum
      intro i _
      exact sq_le_sq.mpr ((hfrequency (j i)).trans (le_abs_self W))
    _ = (Fintype.card ι : ℝ) * W^2 := by simp
    _ ≤ (n : ℝ) * W^2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg W)

/-- Transfer a Frobenius-energy bound in orthonormal coordinates to the
underlying Hilbert space. -/
theorem norm_apply_le_sqrt_matrixEntryNormSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →ₗ[ℂ] E) (f : E) :
    ‖T f‖ ≤ Real.sqrt (matrixEntryNormSq (LinearMap.toMatrix b.toBasis b.toBasis T)) *
      ‖f‖ := by
  let D := LinearMap.toMatrix b.toBasis b.toBasis T
  have hrepr : D.toEuclideanLin (b.repr f) = b.repr (T f) := by
    apply PiLp.ext
    intro i
    change (D *ᵥ (fun j => b.repr f j)) i = b.repr (T f) i
    have hcoeff : ⇑(b.toBasis.repr f) = (fun j => b.repr f j) :=
      funext (fun j => b.coe_toBasis_repr_apply f j)
    rw [← hcoeff]
    exact congrFun (T.toMatrix_mulVec_repr b.toBasis b.toBasis f) i
  have h := D.toEuclideanLin.toContinuousLinearMap.le_opNorm (b.repr f)
  change ‖D.toEuclideanLin (b.repr f)‖ ≤
    ‖D.toEuclideanLin.toContinuousLinearMap‖ * ‖b.repr f‖ at h
  rw [hrepr, b.repr.norm_map, b.repr.norm_map] at h
  have hD : ‖D.toEuclideanLin.toContinuousLinearMap‖ ≤
      Real.sqrt (matrixEntryNormSq D) := by
    change ‖D‖ ≤ _
    exact matrix_l2OpNorm_le_sqrt_entryNormSq D
  exact h.trans (mul_le_mul_of_nonneg_right hD (norm_nonneg f))

/-- Boundary evaluation and imaginary eigenvalues bound the differentiation
operator in a finite-dimensional Hilbert space. -/
theorem finiteHilbert_derivative_norm_le {n : ℕ}
    (T : E →ₗ[ℂ] E) (eval0 eval1 : E →ₗ[ℂ] ℂ)
    (frequency : Fin n → ℝ) (gen : Fin n → E) {K W : ℝ}
    (hK : 0 ≤ K) (_hW : 0 ≤ W)
    (hboundary : ∀ f g, ⟪T f, g⟫_ℂ + ⟪f, T g⟫_ℂ =
      star (eval1 f) * eval1 g - star (eval0 f) * eval0 g)
    (heval0 : ∀ f, ‖eval0 f‖ ≤ K * ‖f‖)
    (heval1 : ∀ f, ‖eval1 f‖ ≤ K * ‖f‖)
    (hspan : Submodule.span ℂ (Set.range gen) = ⊤)
    (heigen : ∀ j, T (gen j) = (Complex.I * (frequency j : ℂ)) • gen j)
    (hfrequency : ∀ j, |frequency j| ≤ W) (f : E) :
    ‖T f‖ ≤ Real.sqrt ((n : ℝ) * W^2 + 2*K^4) * ‖f‖ := by
  classical
  let b := stdOrthonormalBasis ℂ E
  let D := LinearMap.toMatrix b.toBasis b.toBasis T
  let u := fun i => star (eval1 (b i))
  let v := fun i => star (eval0 (b i))
  have hu : (∑ i, ‖u i‖^2) ≤ K^2 := by
    simpa only [u, norm_star] using orthonormalBasis_functional_energy_le b eval1 hK heval1
  have hv : (∑ i, ‖v i‖^2) ≤ K^2 := by
    simpa only [v, norm_star] using orthonormalBasis_functional_energy_le b eval0 hK heval0
  have hb : D + Dᴴ = Matrix.vecMulVec u (star u) - Matrix.vecMulVec v (star v) := by
    ext i j
    simp only [D, LinearMap.toMatrix_apply, b.coe_toBasis,
      b.coe_toBasis_repr_apply, b.repr_apply_apply, Matrix.add_apply,
      Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
      Pi.star_apply, u, v, star_star]
    have hc : star ⟪b j, T (b i)⟫_ℂ = ⟪T (b i), b j⟫_ℂ :=
      inner_conj_symm _ _
    rw [hc]
    simpa only [add_comm] using hboundary (b i) (b j)
  have ht : (Matrix.trace (D*D)).re = (LinearMap.trace ℂ E (T*T)).re := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis, LinearMap.toMatrix_mul]
  have htrace := neg_re_trace_square_le_of_spanning_eigenvectors
    T frequency gen hspan heigen hfrequency
  have hB := matrixEntryNormSq_sub_le_twice
    (Matrix.vecMulVec u (star u)) (Matrix.vecMulVec v (star v))
  rw [matrixEntryNormSq_vecMulVec_star, matrixEntryNormSq_vecMulVec_star] at hB
  have hu0 : 0 ≤ ∑ i, ‖u i‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hv0 : 0 ≤ ∑ i, ‖v i‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hu2 := (sq_le_sq₀ hu0 (sq_nonneg K)).2 hu
  have hv2 := (sq_le_sq₀ hv0 (sq_nonneg K)).2 hv
  have hD := matrixEntryNormSq_eq_neg_trace_add_half D
  rw [hb, ht] at hD
  have henergy : matrixEntryNormSq D ≤ (n:ℝ)*W^2+2*K^4 := by
    nlinarith
  exact (norm_apply_le_sqrt_matrixEntryNormSq b T f).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt henergy) (norm_nonneg f))

end
end LeanNumDetect.MultiTuran
