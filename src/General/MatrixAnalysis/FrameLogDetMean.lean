import General.Fourier.ConnectedBasisBounds
import General.Probability.SmoothFramePotential
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.FrameLogDetMean
open FiniteMatrixSampling FrameMatrixBounds ConnectedBasisBounds
noncomputable section

/-- The real logarithmic determinant is monotone on the positive cone. -/
theorem log_det_mono {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hB : B.PosDef)
    (hAB : ∀ x : EuclideanSpace ℂ (Fin n), quadratic A x ≤ quadratic B x) :
    Real.log A.det.re ≤ Real.log B.det.re := by
  obtain ⟨P, hP, hwhite⟩ := exists_whitening_matrix A hA
  have hC : (Pᴴ * B * P).PosDef :=
    hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hP)
  have hlow (x : EuclideanSpace ℂ (Fin n)) :
      ‖x‖ ^ 2 ≤ quadratic (Pᴴ * B * P) x := by
    have h := hAB (P.toEuclideanLin x)
    rw [← quadratic_congruence A, ← quadratic_congruence B, hwhite,
      quadratic_identity] at h
    exact h
  have heig (i : Fin n) : 1 ≤ hC.isHermitian.eigenvalues i := by
    have h := hlow (hC.isHermitian.eigenvectorBasis i)
    rw [TraceExponential.quadratic_eigenvector,
      hC.isHermitian.eigenvectorBasis.orthonormal.1 i] at h
    simpa using h
  have hl : 0 ≤ Real.log (realDet (Pᴴ * B * P)) := by
    rw [log_realDet_eq_sum hC]
    exact Finset.sum_nonneg (fun i _ => Real.log_nonneg (heig i))
  have hd := realDet_whitening_identity (B := B) hA hwhite
  have hh := congrArg Real.log hd
  rw [Real.log_mul (realDet_pos hC).ne' (realDet_pos hA).ne'] at hh
  change Real.log (realDet A) ≤ Real.log (realDet B)
  linarith

/-- Hadamard's inequality in logarithmic form for a positive-definite matrix. -/
theorem log_det_le_sum_log_diag {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) : Real.log H.det.re ≤ ∑ i, Real.log (H i i).re := by
  have hdiag (i : Fin n) : 0 < (H i i).re :=
    (RCLike.pos_iff.mp (hH.diag_pos (i := i))).1
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((H i i).re : ℂ))
  have hD : D.PosDef := Matrix.PosDef.diagonal (fun i =>
    RCLike.pos_iff.mpr ⟨hdiag i, by simp⟩)
  have hde (i : Fin n) : ((H i i).re : ℂ) = H i i := by
    have hh := congrFun hH.isHermitian.coe_re_diag i
    exact hh
  have hinv : D⁻¹ = Matrix.diagonal (fun i => (((H i i).re : ℂ))⁻¹) := by
    apply Matrix.inv_eq_left_inv
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Matrix.mul_diagonal, Complex.ofReal_ne_zero.mpr (hdiag i).ne']
    · simp [D, Matrix.mul_diagonal, hij]
  have ht : (D⁻¹ * H).trace.re = n := by
    rw [hinv]
    have he : (Matrix.diagonal (fun i => (((H i i).re : ℂ))⁻¹) * H).trace = n := by
      change (∑ i, (Matrix.diagonal (fun j => (((H j j).re : ℂ))⁻¹) * H) i i) = _
      have hei (i : Fin n) :
          (Matrix.diagonal (fun j => (((H j j).re : ℂ))⁻¹) * H) i i = 1 := by
        rw [Matrix.diagonal_mul, ← hde i]
        exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hdiag i).ne')
      calc
        _ = ∑ i : Fin n, (1 : ℂ) := Finset.sum_congr rfl (fun i _ => hei i)
        _ = n := by simp
    rw [he]
    simp
  have hh := relative_log_realDet_le_trace hD hH
  rw [ht] at hh
  have hd : Real.log (realDet D) = ∑ i, Real.log (H i i).re := by
    have he : D.det = ((∏ i, (H i i).re : ℝ) : ℂ) := by
      simp [D, Matrix.det_diagonal]
    rw [realDet, he, Complex.ofReal_re]
    exact Real.log_prod (fun i _ => (hdiag i).ne')
  change Real.log (realDet H) ≤ _
  rw [hd] at hh
  linarith

/-- The coefficient ℓ¹ bound includes the Euclidean coefficient norm. -/
theorem norm_le_sum_coordinate_norm {n : ℕ} (x : EuclideanSpace ℂ (Fin n)) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => norm_nonneg _))).mp
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)

/-- A square synthesis matrix inherits the coefficient lower bound. -/
theorem synthesis_lower {n : ℕ} (f : Fin n → EuclideanSpace ℂ (Fin n))
    {c : ℝ} (hc : 0 ≤ c) (hf : L1LowerBound f c)
    (x : EuclideanSpace ℂ (Fin n)) :
    c * ‖x‖ ≤ ‖Matrix.toEuclideanLin (fun i j => f j i : Matrix (Fin n) (Fin n) ℂ) x‖ := by
  have he : Matrix.toEuclideanLin (fun i j => f j i : Matrix (Fin n) (Fin n) ℂ) x =
      ∑ j, (x j) • f j := by
    ext i
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [he]
  exact (mul_le_mul_of_nonneg_left (norm_le_sum_coordinate_norm x) hc).trans (hf _)

/-- The same conorm lower bound holds for the adjoint synthesis matrix. -/
theorem adjoint_synthesis_lower {n : ℕ} (f : Fin n → EuclideanSpace ℂ (Fin n))
    {c : ℝ} (hc : 0 < c) (hf : L1LowerBound f c)
    (x : EuclideanSpace ℂ (Fin n)) :
    c * ‖x‖ ≤ ‖(fun i j => f j i : Matrix (Fin n) (Fin n) ℂ)ᴴ.toEuclideanLin x‖ := by
  let F : Matrix (Fin n) (Fin n) ℂ := fun i j => f j i
  have hlow := synthesis_lower f hc.le hf
  have hF : IsUnit F := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro u v huv
    have hh : F.toEuclideanLin (toLp 2 (u-v)) = 0 := by
      change toLp 2 (F *ᵥ (u-v)) = 0
      simp [Matrix.mulVec_sub, huv]
    have hh' := hlow (toLp 2 (u-v))
    change c * ‖toLp 2 (u-v)‖ ≤ ‖F.toEuclideanLin (toLp 2 (u-v))‖ at hh'
    rw [hh, norm_zero] at hh'
    have hn : ‖toLp 2 (u-v)‖ = 0 := by nlinarith [norm_nonneg (toLp 2 (u-v))]
    have he : u-v = 0 := by simpa using congrArg ofLp (norm_eq_zero.mp hn)
    exact sub_eq_zero.mp he
  letI := hF.invertible
  let y := F⁻¹.toEuclideanLin x
  have hxy : F.toEuclideanLin y = x := by
    change (F.toEuclideanLin ∘ₗ F⁻¹.toEuclideanLin) x = x
    rw [← Matrix.toLpLin_mul_same, Matrix.mul_inv_of_invertible]
    simp
  have hy : c * ‖y‖ ≤ ‖x‖ := by
    have hh := hlow y
    change c * ‖y‖ ≤ ‖F.toEuclideanLin y‖ at hh
    rwa [hxy] at hh
  have hi : ‖x‖ ^ 2 ≤ ‖Fᴴ.toEuclideanLin x‖ * ‖y‖ := by
    calc
      ‖x‖ ^ 2 = ‖⟪x, x⟫_ℂ‖ := by simp [inner_self_eq_norm_sq_to_K]
      _ = ‖⟪Fᴴ.toEuclideanLin x, y⟫_ℂ‖ := by
        rw [← hxy, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
          LinearMap.adjoint_inner_left]
      _ ≤ _ := norm_inner_le_norm _ _
  by_cases hx : ‖x‖ = 0
  · simp [hx, norm_nonneg]
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    have hh := mul_le_mul_of_nonneg_left hi hc.le
    have hh' := mul_le_mul_of_nonneg_left hy (norm_nonneg (Fᴴ.toEuclideanLin x))
    change c * ‖x‖ ≤ ‖Fᴴ.toEuclideanLin x‖
    nlinarith

@[simp] theorem quadratic_real_matrix_smul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (x : EuclideanSpace ℂ (Fin n)) :
    quadratic (r • A) x = r * quadratic A x := by
  exact (quadraticTestLinearMap x).map_smul r A

@[simp] theorem quadratic_matrix_add {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    quadratic (A+B) x = quadratic A x + quadratic B x := by
  exact (quadraticTestLinearMap x).map_add A B

@[simp] theorem quadratic_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    quadratic A (EuclideanSpace.single i 1) = (A i i).re := by
  unfold quadratic
  change ((A *ᵥ Pi.single i 1) ⬝ᵥ star (Pi.single i (1 : ℂ))).re = _
  have hs : star (Pi.single i (1 : ℂ) : Fin n → ℂ) = (Pi.single i 1 : Fin n → ℂ) := by
    ext j
    by_cases hij : j = i
    · subst j; simp
    · simp [hij]
  rw [hs]
  simp

/-- A conditioned square family controls its row Gram without a thickness argument. -/
theorem row_gram_lower {n : ℕ} (f : Fin n → EuclideanSpace ℂ (Fin n))
    {c : ℝ} (hc : 0 < c) (hf : L1LowerBound f c)
    (x : EuclideanSpace ℂ (Fin n)) :
    c ^ 2 * ‖x‖ ^ 2 ≤ quadratic
      (Matrix.of (fun i j => f j i) *
        (Matrix.of (fun i j => f j i))ᴴ) x := by
  rw [quadratic_whitening_gram]
  have hh := adjoint_synthesis_lower f hc hf x
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ c * ‖x‖) (norm_nonneg _)).mpr hh
  convert hs using 1 <;> first | rfl | simp only [mul_pow]

/-- Hadamard and determinant monotonicity give the log-determinant estimate
for one quantitatively independent square row family. -/
theorem basis_sum_log_lower {n : ℕ} (f : Fin n → EuclideanSpace ℂ (Fin n))
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) (hf : L1LowerBound f c)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    Real.log (1 + (c ^ 2 / R) • A).det.re ≤
      ∑ j, Real.log (1 + quadratic A (f j) / R) := by
  let F : Matrix (Fin n) (Fin n) ℂ := fun i j => f j i
  obtain ⟨S, hS, hwhite⟩ := exists_whitening_matrix A⁻¹ hA.inv
  letI := hA.isUnit.invertible
  have hAs : A = S * Sᴴ := by
    have hh := inverse_eq_whitening_gram hA.inv hS hwhite
    simpa only [Matrix.inv_inv_of_invertible] using hh
  let H := (1 : Matrix (Fin n) (Fin n) ℂ) + (1 / R : ℝ) • (Fᴴ * A * F)
  let C := (1 : Matrix (Fin n) (Fin n) ℂ) + (1 / R : ℝ) • (Sᴴ * (F * Fᴴ) * S)
  let D := (1 : Matrix (Fin n) (Fin n) ℂ) + (c ^ 2 / R : ℝ) • (Sᴴ * S)
  have hH : H.PosDef := Matrix.PosDef.one.add_posSemidef
    ((hA.posSemidef.conjTranspose_mul_mul_same F).smul (by positivity))
  have hC : C.PosDef := Matrix.PosDef.one.add_posSemidef
    (((Matrix.posSemidef_self_mul_conjTranspose F).conjTranspose_mul_mul_same S).smul
      (by positivity))
  have hD : D.PosDef := Matrix.PosDef.one.add_posSemidef
    ((Matrix.posSemidef_conjTranspose_mul_self S).smul (by positivity))
  have hmono : Real.log D.det.re ≤ Real.log C.det.re := by
    apply log_det_mono hD hC
    intro x
    have hh := row_gram_lower f hc hf (S.toEuclideanLin x)
    change c ^ 2 * ‖S.toEuclideanLin x‖ ^ 2 ≤ quadratic (F * Fᴴ) (S.toEuclideanLin x) at hh
    have hSgram : quadratic (Sᴴ * S) x = ‖S.toEuclideanLin x‖ ^ 2 := by
      simpa using quadratic_congruence (1 : Matrix (Fin n) (Fin n) ℂ) S x
    simp only [D, C, quadratic_matrix_add, quadratic_real_matrix_smul,
      quadratic_identity, quadratic_congruence, hSgram]
    apply add_le_add_right
    have h := mul_le_mul_of_nonneg_left hh (le_of_lt (one_div_pos.mpr hR))
    convert h using 1 <;> first | rfl | ring
  have hCH : C.det = H.det := by
    have hh := Matrix.det_one_add_mul_comm
      ((1 / R : ℝ) • (Sᴴ * F)) (Fᴴ * S)
    convert hh using 1 <;>
      simp [C, H, hAs, Matrix.mul_assoc]
  have hDdet : D.det = (1 + (c ^ 2 / R) • A).det := by
    have hh := Matrix.det_one_add_mul_comm ((c ^ 2 / R : ℝ) • Sᴴ) S
    convert hh using 1 <;>
      simp [D, hAs]
  have hdiag (j : Fin n) : (H j j).re = 1 + quadratic A (f j) / R := by
    have hFj : F.toEuclideanLin (EuclideanSpace.single j 1) = f j := by
      ext i
      simp [F, Matrix.toLpLin_apply, EuclideanSpace.single]
    rw [← quadratic_single H j]
    simp only [H, quadratic_matrix_add, quadratic_real_matrix_smul,
      quadratic_identity, PiLp.norm_single, norm_one, one_pow,
      quadratic_congruence, hFj]
    ring
  have hhad := log_det_le_sum_log_diag hH
  rw [← hDdet]
  rw [← hCH] at hhad
  simp_rw [hdiag] at hhad
  exact hmono.trans hhad

end
end LeanNumDetect.FrameLogDetMean
