import Mathlib.Tactic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Vandermonde

/-! Reusable quadratic-form, Gram-matrix and eigenvalue estimates. No external admissions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ComplexOrder
open Matrix Finset

namespace LeanNumDetect

noncomputable def quadratic {n : Type*} [Fintype n]
    (G : Matrix n n ℂ) (v : n → ℂ) : ℝ :=
  (star v ⬝ᵥ (G *ᵥ v)).re

/-- A bound for quadratic forms bounds every eigenvalue of `G⁻¹ G₀`.
The real part formulation does not incorrectly assume that `G⁻¹ G₀` is Hermitian. -/
theorem eigenvalue_le_of_quadratic {n : Type*} [Fintype n] [DecidableEq n]
    (G G₀ : Matrix n n ℂ) (hG : G.PosDef) {L : ℝ}
    (hbound : ∀ v, quadratic G₀ v ≤ L * quadratic G v)
    {z : ℂ} {v : n → ℂ} (hv : v ≠ 0) (heig : (G⁻¹ * G₀) *ᵥ v = z • v) :
    z.re ≤ L := by
  have hdet := G.isUnit_iff_isUnit_det.mp hG.isUnit
  have hmul : G₀ *ᵥ v = z • (G *ᵥ v) := by
    calc
      _ = (G * (G⁻¹ * G₀)) *ᵥ v := by rw [G.mul_nonsing_inv_cancel_left G₀ hdet]
      _ = G *ᵥ ((G⁻¹ * G₀) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = _ := by rw [heig, Matrix.mulVec_smul]
  have hq := congrArg (fun x => star v ⬝ᵥ x) hmul
  rw [dotProduct_smul, smul_eq_mul] at hq
  have him : (star v ⬝ᵥ (G *ᵥ v)).im = 0 := hG.isHermitian.im_star_dotProduct_mulVec_self v
  have hreal : quadratic G₀ v = z.re * quadratic G v := by
    simpa only [quadratic, Complex.mul_re, him, mul_zero, sub_zero] using congrArg Complex.re hq
  have hpos : 0 < quadratic G v := hG.re_dotProduct_pos hv
  have hb := hbound v
  rw [hreal] at hb
  nlinarith only [hpos, hb]

/-- The same eigenpair has a real eigenvalue when both Gram matrices are Hermitian. -/
theorem eigenvalue_im_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    (G G₀ : Matrix n n ℂ) (hG : G.PosDef) (hG₀ : G₀.IsHermitian)
    {z : ℂ} {v : n → ℂ} (hv : v ≠ 0) (heig : (G⁻¹ * G₀) *ᵥ v = z • v) :
    z.im = 0 := by
  have hdet := G.isUnit_iff_isUnit_det.mp hG.isUnit
  have hmul := congrArg (fun x => G *ᵥ x) heig
  rw [Matrix.mulVec_mulVec, G.mul_nonsing_inv_cancel_left G₀ hdet, Matrix.mulVec_smul] at hmul
  have hq := congrArg (fun x => star v ⬝ᵥ x) hmul
  rw [dotProduct_smul, smul_eq_mul] at hq
  have him : (star v ⬝ᵥ (G *ᵥ v)).im = 0 := hG.isHermitian.im_star_dotProduct_mulVec_self v
  have him₀ : (star v ⬝ᵥ (G₀ *ᵥ v)).im = 0 := hG₀.im_star_dotProduct_mulVec_self v
  have hz : z.im * (star v ⬝ᵥ (G *ᵥ v)).re = 0 := by
    have hi := congrArg Complex.im hq
    simpa only [Complex.mul_im, him, him₀, mul_zero, zero_add, eq_comm] using hi
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt (hG.re_dotProduct_pos hv))

/-- Matrix determinant lemma in the form used for deleting the first row. -/
theorem determinant_rank_one_ratio {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : IsUnit H.det) (u v : n → ℂ) :
    (H - Matrix.vecMulVec u v).det / H.det = 1 - v ⬝ᵥ (H⁻¹ *ᵥ u) := by
  have hm : H - Matrix.vecMulVec u v =
      H + Matrix.replicateCol Unit (-u) * Matrix.replicateRow Unit v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec, Matrix.replicateCol, Matrix.replicateRow, sub_eq_add_neg]
  rw [hm, Matrix.det_add_replicateCol_mul_replicateRow hH]
  rw [mul_div_cancel_left₀ _ hH.ne_zero, Matrix.det_unique]
  simp [Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow, Matrix.mulVec,
    dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc, sub_eq_add_neg]
  rw [Finset.sum_comm]

/-- Nonzero determinant of the first square Vandermonde block. -/
theorem square_vandermonde_injective {n : ℕ} (z : Fin n → ℂ)
    (hz : Function.Injective z) : Function.Injective (Matrix.vandermonde z).mulVec := by
  exact Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
      (Matrix.det_vandermonde_ne_zero_iff.mpr hz)))

theorem weighted_cauchy_schwarz {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.PosDef) (u v : n → ℂ) :
    ‖star u ⬝ᵥ (H *ᵥ v)‖ ^ 2 ≤ quadratic H u * quadratic H v := by
  letI := H.toSeminormedAddCommGroup hH.posSemidef
  letI := H.toInnerProductSpace hH.posSemidef
  have h := pow_le_pow_left₀ (norm_nonneg (inner ℂ u v)) (norm_inner_le_norm u v) 2
  rw [mul_pow, ← inner_self_eq_norm_sq (𝕜 := ℂ) u, ← inner_self_eq_norm_sq (𝕜 := ℂ) v] at h
  change ‖(H *ᵥ v) ⬝ᵥ star u‖ ^ 2 ≤
    ((H *ᵥ u) ⬝ᵥ star u).re * ((H *ᵥ v) ⬝ᵥ star v).re at h
  simpa only [quadratic, dotProduct_comm] using h

/-- The inverse-Gram expression bounds the scalar endpoint functional. -/
theorem endpoint_functional_bound {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.PosDef) (u v : n → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ quadratic H⁻¹ u * quadratic H v := by
  let w := H⁻¹ *ᵥ u
  have hdet := H.isUnit_iff_isUnit_det.mp hH.isUnit
  have hw : H *ᵥ w = u := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hrow : star w ᵥ* H = star u := by
    rw [← hH.isHermitian.eq, ← Matrix.star_mulVec, hw]
  have hpair : star w ⬝ᵥ (H *ᵥ v) = star u ⬝ᵥ v := by
    rw [dotProduct_mulVec, hrow]
  have hq : quadratic H w = quadratic H⁻¹ u := by
    unfold quadratic
    rw [hw]
    change (star w ⬝ᵥ u).re = (star u ⬝ᵥ w).re
    have hs : star (star w ⬝ᵥ u) = star u ⬝ᵥ w := by
      rw [star_dotProduct, star_star, dotProduct_comm]
    rw [← hs]
    rfl
  simpa only [hpair, hq] using weighted_cauchy_schwarz H hH w v

theorem quadratic_gram {m n : Type*} [Fintype m] [Fintype n]
    (V : Matrix m n ℂ) (v : n → ℂ) :
    quadratic (Vᴴ * V) v = ∑ k, ‖(V *ᵥ v) k‖ ^ 2 := by
  unfold quadratic
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  simp only [dotProduct, Pi.star_apply, Complex.star_def,
    Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_sum, Complex.ofReal_re]

/-- Summing scalar endpoint estimates gives the block Gram comparison. -/
theorem block_gram_bound {m n : Type*} [Fintype m] [Fintype n]
    (r : ℕ) (V : Fin (r + 1) → Matrix m n ℂ) {ell : ℝ}
    (hscalar : ∀ (v : n → ℂ) (k : m),
      ‖(V 0 *ᵥ v) k‖ ^ 2 ≤ ell * ∑ j, ‖(V j *ᵥ v) k‖ ^ 2) :
    ∀ v, quadratic ((V 0)ᴴ * V 0) v ≤
      ell * quadratic (∑ j, (V j)ᴴ * V j) v := by
  intro v
  rw [quadratic_gram]
  have hq : quadratic (∑ j, (V j)ᴴ * V j) v =
      ∑ j, ∑ k, ‖(V j *ᵥ v) k‖ ^ 2 := by
    unfold quadratic
    rw [Matrix.sum_mulVec, dotProduct_sum]
    change Complex.reAddGroupHom (∑ i, star v ⬝ᵥ (((V i)ᴴ * V i) *ᵥ v)) = _
    rw [map_sum]
    exact sum_congr rfl (fun j _ => quadratic_gram (V j) v)
  rw [hq, sum_comm, mul_sum]
  exact sum_le_sum (fun k _ => hscalar v k)

end LeanNumDetect
