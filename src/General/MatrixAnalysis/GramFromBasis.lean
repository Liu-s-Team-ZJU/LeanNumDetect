import General.MatrixAnalysis.RowDeletion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped ComplexOrder
namespace LeanNumDetect
/-- An orthonormal family of the same column count in the range certifies full rank. -/
theorem gram_posDef_of_orthonormal_range {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (U V : Matrix m n ℂ) (hU : Uᴴ * U = 1)
    (hspan : LinearMap.range U.mulVecLin ≤ LinearMap.range V.mulVecLin) :
    (Vᴴ * V).PosDef := by
  classical
  obtain ⟨P, hP⟩ := factor_of_range_le U V hspan
  have hnorm : (Pᴴ * (Vᴴ * V)) * P = 1 := by
    simpa only [hP, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hU
  have hleft : ((P * Pᴴ) * Vᴴ) * V = 1 := by
    simpa only [Matrix.mul_assoc] using mul_eq_one_comm.mp hnorm
  have hinj : Function.Injective V.mulVec := by
    intro v w he
    have hh := congrArg (fun z => ((P * Pᴴ) * Vᴴ) *ᵥ z) he
    simpa only [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] using hh
  simpa only [Matrix.mul_one] using
    (Matrix.PosDef.one : (1 : Matrix m m ℂ).PosDef).conjTranspose_mul_mul_same hinj
end LeanNumDetect
