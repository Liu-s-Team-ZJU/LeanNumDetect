import General.MatrixAnalysis.GoldenThompsonDyadic
import General.MatrixAnalysis.LieTrotter
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
The Golden--Thompson trace inequality, obtained from finite dyadic sorting
and the Lie--Trotter product formula.
-/

set_option autoImplicit false

open Matrix NormedSpace Filter
open scoped Topology Matrix.Norms.L2Operator

namespace LeanNumDetect.GoldenThompson

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma exp_inv_nat_smul_pow (A : Matrix n n ℂ) {p : ℕ} (hp : 0 < p) :
    exp ((p : ℝ)⁻¹ • A) ^ p = exp A := by
  rw [← Matrix.exp_nsmul]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hp0, one_smul]

/-- Every dyadic Lie--Trotter approximant satisfies the final trace bound. -/
lemma trace_exp_mul_exp_pow_dyadic_le (k : ℕ) {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace ((exp (((2 ^ (k + 1) : ℕ) : ℝ)⁻¹ • A) *
      exp (((2 ^ (k + 1) : ℕ) : ℝ)⁻¹ • B)) ^ (2 ^ (k + 1)))).re ≤
        (Matrix.trace (exp A * exp B)).re := by
  have h := trace_mul_pow_dyadic_le k
    (hA.smul (show IsSelfAdjoint (((2 ^ (k + 1) : ℕ) : ℝ)⁻¹) from by rfl)).exp
    (hB.smul (show IsSelfAdjoint (((2 ^ (k + 1) : ℕ) : ℝ)⁻¹) from by rfl)).exp
  simpa only [exp_inv_nat_smul_pow _ (by positivity : 0 < 2 ^ (k + 1))] using h

omit [DecidableEq n] in
lemma continuous_trace_re : Continuous (fun A : Matrix n n ℂ => (Matrix.trace A).re) := by
  unfold Matrix.trace
  fun_prop

/-- Golden--Thompson for arbitrary finite complex Hermitian matrices. -/
theorem trace_exp_add_le {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (exp (A + B))).re ≤ (Matrix.trace (exp A * exp B)).re := by
  rcases isEmpty_or_nonempty n with hn | hn
  · letI := hn
    simp [Matrix.trace]
  · letI := hn
    have hT := LeanNumDetect.tendsto_exp_mul_exp_pow_two A B
    have hlim := continuous_trace_re.tendsto (exp (A + B)) |>.comp
      (hT.comp (tendsto_add_atTop_nat 1))
    exact le_of_tendsto hlim
      (Eventually.of_forall (fun k => trace_exp_mul_exp_pow_dyadic_le k hA hB))

end

end LeanNumDetect.GoldenThompson
