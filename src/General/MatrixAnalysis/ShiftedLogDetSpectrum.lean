import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The logarithmic determinant of an identity plus a positive matrix,
expressed in the original matrix's eigenvalues. -/

set_option autoImplicit false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace LeanNumDetect.FiniteMatrixSampling
noncomputable section

theorem shifted_log_det_eq_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) {r : ℝ} (hr : 0 ≤ r) :
    Real.log ((1 + (r : ℂ) • A).det.re) =
      ∑ j, Real.log (1 + r * hA.isHermitian.eigenvalues j) := by
  let U := hA.isHermitian.eigenvectorUnitary
  let σ := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) U
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun j => ((1 + r * hA.isHermitian.eigenvalues j : ℝ) : ℂ))
  have hd : D = 1 + (r : ℂ) •
      Matrix.diagonal (fun j => (hA.isHermitian.eigenvalues j : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, hij]
  have hs : σ D = 1 + (r : ℂ) • A := by
    rw [hd, map_add, map_one, map_smul]
    have hh := hA.isHermitian.spectral_theorem
    simpa only [σ, U, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      congrArg (fun H : Matrix (Fin n) (Fin n) ℂ => 1 + (r : ℂ) • H) hh.symm
  have hdet : (1 + (r : ℂ) • A).det =
      ∏ j, ((1 + r * hA.isHermitian.eigenvalues j : ℝ) : ℂ) := by
    rw [← hs]
    dsimp [σ]
    rw [Matrix.det_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
    exact Matrix.det_diagonal
  have hreal : (1 + (r : ℂ) • A).det.re =
      ∏ j, (1 + r * hA.isHermitian.eigenvalues j) := by
    rw [hdet]
    have hh : (∏ j, ((1 + r * hA.isHermitian.eigenvalues j : ℝ) : ℂ)) =
        ((∏ j, (1 + r * hA.isHermitian.eigenvalues j) : ℝ) : ℂ) := by norm_cast
    rw [hh]
    rfl
  rw [hreal]
  apply Real.log_prod
  intro j _
  have hp := hA.eigenvalues_pos j
  positivity

/-- The same spectral formula for the real scalar action on complex matrices. -/
theorem shifted_log_det_real_smul_eq_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) {r : ℝ} (hr : 0 ≤ r) :
    Real.log ((1 + r • A).det.re) =
      ∑ j, Real.log (1 + r * hA.isHermitian.eigenvalues j) := by
  have he : r • A = (r : ℂ) • A := by
    ext i j
    simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  rw [he]
  exact shifted_log_det_eq_sum A hA hr

end
end LeanNumDetect.FiniteMatrixSampling
