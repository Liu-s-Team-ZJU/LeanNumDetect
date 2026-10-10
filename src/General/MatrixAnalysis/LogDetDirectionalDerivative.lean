import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped ComplexOrder

namespace LeanNumDetect

noncomputable section

/-- Jacobi's formula at zero for an arbitrary affine matrix direction. -/
theorem hasDerivAt_det_affine {n : Type*} [Fintype n] [DecidableEq n]
    (A H : Matrix n n ℂ) (hA : IsUnit A.det) :
    HasDerivAt (fun t : ℂ => (A + t • H).det)
      (A.det * (A⁻¹ * H).trace) 0 := by
  let M : Matrix n n ℂ := A⁻¹ * H
  let p : Polynomial ℂ := Matrix.det ((1 : Matrix n n (Polynomial ℂ)) + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)
  have hp : HasDerivAt (fun t : ℂ => p.eval t) M.trace 0 := by
    simpa only [p, Matrix.derivative_det_one_add_X_smul] using p.hasDerivAt 0
  have heq (t : ℂ) : (A + t • H).det = A.det * p.eval t := by
    have hm : A + t • H = A * (1 + t • M) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
      dsimp [M]
      rw [A.mul_nonsing_inv_cancel_left H hA]
    rw [hm, Matrix.det_mul]
    congr 1
    rw [show p.eval t = ((1 + (Polynomial.X : Polynomial ℂ) •
      M.map Polynomial.C).map (Polynomial.evalRingHom t)).det by
        exact (Polynomial.evalRingHom t).map_det _]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, map_add, map_mul]

    split_ifs <;> simp
  simpa only [← heq, M] using hp.const_mul A.det

/-- The real part version used by Hermitian precision potentials. -/
theorem hasDerivAt_realDet_affine {n : Type*} [Fintype n] [DecidableEq n]
    (A H : Matrix n n ℂ) (hA : A.PosDef) :
    HasDerivAt (fun t : ℝ => (A + (t : ℂ) • H).det.re)
      (A.det.re * (A⁻¹ * H).trace.re) 0 := by
  have h := (hasDerivAt_det_affine A H
    (A.isUnit_iff_isUnit_det.mp hA.isUnit)).real_of_complex
  have him : A.det.im = 0 := (RCLike.pos_iff.mp hA.det_pos).2
  simpa only [Complex.mul_re, him, zero_mul, sub_zero] using h

/-- Directional derivative of the logarithmic real determinant at a positive matrix. -/
theorem hasDerivAt_log_realDet_affine {n : Type*} [Fintype n] [DecidableEq n]
    (A H : Matrix n n ℂ) (hA : A.PosDef) :
    HasDerivAt (fun t : ℝ => Real.log (A + (t : ℂ) • H).det.re)
      (A⁻¹ * H).trace.re 0 := by
  have hpos : 0 < A.det.re := (RCLike.pos_iff.mp hA.det_pos).1
  have h := (hasDerivAt_realDet_affine A H hA).log (by simpa using hpos.ne')
  simpa only [Complex.ofReal_zero, zero_smul, add_zero, mul_div_cancel_left₀ _ hpos.ne'] using h

end
end LeanNumDetect
