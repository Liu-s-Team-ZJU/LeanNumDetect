import General.MatrixAnalysis.InverseMetric
import General.MatrixAnalysis.TraceExponential

/-! Positive-definite determinant identities and logarithmic trace bounds. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.FrameMatrixBounds

noncomputable section

def realDet {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ := A.det.re

theorem realDet_pos {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosDef) : 0 < realDet A := by
  exact (RCLike.pos_iff.mp hA.det_pos).1

theorem realDet_eq_prod_eigenvalues {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) : realDet A = ∏ i, hA.eigenvalues i := by
  unfold realDet
  rw [hA.det_eq_prod_eigenvalues]
  have hp : (∏ i, (hA.eigenvalues i : ℂ)) = ((∏ i, hA.eigenvalues i : ℝ) : ℂ) := by
    norm_cast
  change (∏ i, (hA.eigenvalues i : ℂ)).re = ∏ i, hA.eigenvalues i
  rw [hp]
  rfl

theorem log_realDet_eq_sum {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosDef) :
    Real.log (realDet A) = ∑ i, Real.log (hA.isHermitian.eigenvalues i) := by
  rw [realDet_eq_prod_eigenvalues hA.isHermitian]
  exact Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')

theorem log_realDet_le_trace_sub {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosDef) : Real.log (realDet A) ≤ A.trace.re - d := by
  have ht : A.trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum]
    rfl
  rw [log_realDet_eq_sum hA, ht]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
    (fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, RCLike.ofReal_re] using h

open FiniteMatrixSampling

theorem realDet_whitening_identity {d : ℕ}
    {G B P : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosDef)
    (hwhite : Pᴴ * G * P = 1) :
    realDet (Pᴴ * B * P) * realDet G = realDet B := by
  have he : (Pᴴ * B * P).det * G.det = B.det := by
    calc
      _ = (Pᴴ * G * P).det * B.det := by simp only [Matrix.det_mul]; ring
      _ = B.det := by rw [hwhite, Matrix.det_one, one_mul]
  have him : G.det.im = 0 := (RCLike.pos_iff.mp hG.det_pos).2
  have h := congrArg Complex.re he
  simpa only [realDet, Complex.mul_re, him, mul_zero, sub_zero] using h

theorem relative_log_realDet_le_trace {d : ℕ}
    {G B : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosDef) (hB : B.PosDef) :
    Real.log (realDet B) - Real.log (realDet G) ≤ (G⁻¹ * B).trace.re - d := by
  obtain ⟨P, hP, hwhite⟩ := exists_whitening_matrix G hG
  have hC : (Pᴴ * B * P).PosDef :=
    hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hP)
  have he := realDet_whitening_identity (B := B) hG hwhite
  have hl := congrArg Real.log he
  rw [Real.log_mul (realDet_pos hC).ne' (realDet_pos hG).ne'] at hl
  have ht : (G⁻¹ * B).trace = (Pᴴ * B * P).trace := by
    rw [inverse_eq_whitening_gram hG hP hwhite, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  have hb := log_realDet_le_trace_sub hC
  rw [← ht] at hb
  linarith

end
end LeanNumDetect.FrameMatrixBounds
