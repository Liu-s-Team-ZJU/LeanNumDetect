import General.MatrixAnalysis.SingularValueBounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Angular Vandermonde matrices and their column subspaces

Concrete definitions used for clustered Fourier geometry. Their conventions
follow Batenkov--Diederichs--Goldman--Yomdin, arXiv:1909.01927, Definitions
2.1, 2.4 and 2.5. This module contains no admitted theorem.
-/

set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open Set Matrix WithLp

namespace LeanNumDetect.ClusteredVandermonde
noncomputable section

/-- Source Definition 2.1, angular wrap-around distance. -/
def angularDistance (x y : ℝ) : ℝ :=
  |Complex.arg (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)))|

/-- The unnormalized matrix (1.1), rows `0, …, N`. -/
def vandermonde {s : ℕ} (N : ℕ) (node : Fin s → ℝ) : Matrix (Fin (N + 1)) (Fin s) ℂ :=
  fun k j => Complex.exp (Complex.I * (((k.val : ℝ) * node j : ℝ) : ℂ))

/-- Source Definition 2.4, the subspace spanned by one cluster's columns. -/
def clusterSubspace {s : ℕ} (N : ℕ) (node : Fin s → ℝ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (N + 1))) :=
  Submodule.span ℂ (Set.range fun j => toLp 2 (fun k => vandermonde N node k j))

/-- Source Definition 2.5, minimal principal angle in `[0,π/2]`. -/
def minimalPrincipalAngle {N : ℕ}
    (U V : Submodule ℂ (EuclideanSpace ℂ (Fin (N + 1)))) : ℝ :=
  sInf {a | ∃ u ∈ U, ∃ v ∈ V, u ≠ 0 ∧ v ≠ 0 ∧
    a = Real.arccos (‖⟪u, v⟫_ℂ‖ / (‖u‖ * ‖v‖))}

end
end LeanNumDetect.ClusteredVandermonde
