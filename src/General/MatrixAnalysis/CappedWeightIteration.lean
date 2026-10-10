import General.MatrixAnalysis.CappedRowLeverage
import General.MatrixAnalysis.TraceExponential
import Mathlib.Analysis.SpecificLimits.Basic

/-! Finite descent and logarithmic determinant inequalities used by the capped
auxiliary-row construction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.CappedWeightIteration

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

/-- A positive definite contraction has every eigenvalue at least its determinant. -/
theorem realDet_le_eigenvalue_of_quadratic_upper {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosDef)
    (hupper : ∀ x : EuclideanSpace ℂ (Fin d), quadratic A x ≤ ‖x‖^2)
    (j : Fin d) : realDet A ≤ hA.isHermitian.eigenvalues j := by
  have hcap (i : Fin d) : hA.isHermitian.eigenvalues i ≤ 1 := by
    have h := hupper (hA.isHermitian.eigenvectorBasis i)
    rw [TraceExponential.quadratic_eigenvector, hA.isHermitian.eigenvectorBasis.orthonormal.1 i] at h
    simpa using h
  rw [realDet_eq_prod_eigenvalues hA.isHermitian]
  calc
    _ ≤ ∏ i : Fin d, if i = j then hA.isHermitian.eigenvalues j else 1 := by
      apply Finset.prod_le_prod (fun i _ => (hA.eigenvalues_pos i).le)
      intro i _
      split_ifs with hij
      · subst i; exact le_rfl
      · exact hcap i
    _ = hA.isHermitian.eigenvalues j := by simp

theorem quadratic_lower_of_realDet_lower {d : ℕ}
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosDef)
    (hupper : ∀ x : EuclideanSpace ℂ (Fin d), quadratic A x ≤ ‖x‖^2)
    {α : ℝ} (hdet : α ≤ realDet A) (x : EuclideanSpace ℂ (Fin d)) :
    α * ‖x‖^2 ≤ quadratic A x := by
  rw [TraceExponential.quadratic_eq_sum hA.isHermitian,
    ← hA.isHermitian.eigenvectorBasis.sum_sq_norm_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right
    (hdet.trans (realDet_le_eigenvalue_of_quadratic_upper hA hupper i)) (sq_nonneg _)

/-- Failure of a relative Gram lower bound forces a determinant decrease. -/
theorem realDet_drop_of_not_relative_lower {d : ℕ}
    {G B : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosDef) (hB : B.PosDef)
    (hupper : ∀ x : EuclideanSpace ℂ (Fin d), quadratic B x ≤ quadratic G x)
    {α : ℝ}
    (hbad : ¬ ∀ x : EuclideanSpace ℂ (Fin d), α * quadratic G x ≤ quadratic B x) :
    realDet B < α * realDet G := by
  obtain ⟨P, hP, hwhite⟩ := exists_whitening_matrix G hG
  letI := hP.invertible
  have hC : (Pᴴ * B * P).PosDef :=
    hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hP)
  have hcap (x : EuclideanSpace ℂ (Fin d)) : quadratic (Pᴴ * B * P) x ≤ ‖x‖^2 := by
    have h := hupper (P.toEuclideanLin x)
    rw [← quadratic_congruence, ← quadratic_congruence G, hwhite, quadratic_identity] at h
    exact h
  have hc : realDet (Pᴴ * B * P) < α := by
    by_contra hnot
    have hdet := le_of_not_gt hnot
    apply hbad
    intro x
    let y := P⁻¹.toEuclideanLin x
    have hxy : P.toEuclideanLin y = x := by
      change (P.toEuclideanLin ∘ₗ P⁻¹.toEuclideanLin) x = x
      rw [← Matrix.toLpLin_mul_same, Matrix.mul_inv_of_invertible]
      simp
    have hl := quadratic_lower_of_realDet_lower hC hcap hdet y
    have hm : quadratic G x = ‖y‖^2 := by
      rw [← hxy, ← quadratic_congruence, hwhite, quadratic_identity]
    rw [quadratic_congruence, hxy, ← hm] at hl
    exact hl
  have he := realDet_whitening_identity (B := B) hG hwhite
  have h := mul_lt_mul_of_pos_right hc (realDet_pos hG)
  rwa [he] at h

/-- A uniform positive lower bound prevents indefinite geometric descent.
This is a finite argument and requires no convergence or minimizer theorem. -/
theorem exists_nondescending_step (p : ℕ → ℝ) (good : ℕ → Prop)
    {α δ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hδ : 0 < δ)
    (hp0 : p 0 ≤ 1) (hlower : ∀ k, δ ≤ p k)
    (hdrop : ∀ k, ¬ good k → p (k+1) ≤ α * p k) :
    ∃ k, good k := by
  by_contra hnone
  push Not at hnone
  have hb (k : ℕ) : p k ≤ α^k := by
    induction k with
    | zero => simpa using hp0
    | succ k ih =>
      calc
        p (k+1) ≤ α*p k := hdrop k (hnone k)
        _ ≤ α*α^k := mul_le_mul_of_nonneg_left ih hα0
        _ = α^(k+1) := by rw [pow_succ]; ring
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ hα1
  exact (not_lt_of_ge ((hlower k).trans (hb k))) hk

end
end LeanNumDetect.CappedWeightIteration
