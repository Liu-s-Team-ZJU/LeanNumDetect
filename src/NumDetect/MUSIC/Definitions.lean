import NumDetect.Preliminaries.Matrices

/-! MUSIC noise-space bases, steering normalization, and correlation functions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- A matrix whose columns are an orthonormal basis of the left noise space of `A`. -/
def IsLeftNoiseSpaceBasis {ι κ q : Type*}
    [Fintype ι] [Fintype κ] [Fintype q] [DecidableEq q]
    (A : Matrix ι κ ℂ) (U₂ : Matrix ι q ℂ) : Prop :=
  U₂ᴴ * U₂ = 1 ∧
  LinearMap.range U₂.mulVecLin = LinearMap.ker Aᴴ.mulVecLin

/-- An orthonormal basis of left singular vectors, ordered by decreasing
singular value. It is obtained by diagonalizing `A Aᴴ`. -/
noncomputable def leftSingularBasis {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) :
    OrthonormalBasis (Fin (Fintype.card ι)) ℂ (EuclideanSpace ℂ ι) :=
  A.toEuclideanLin.adjoint.isSymmetric_adjoint_comp_self.eigenvectorBasis
    finrank_euclideanSpace

/-- The span of the left singular vectors after the first `signalRank`
vectors. This is the fixed-rank noise subspace used by MUSIC for both exact
and perturbed data matrices. -/
noncomputable def trailingLeftSingularSubspace {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (signalRank : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ ι) :=
  Submodule.span ℂ
    (Set.range fun j :
      {j : Fin (Fintype.card ι) // signalRank ≤ (j : ℕ)} =>
        leftSingularBasis A j.1)

/-- Unit-normalized row-frequency steering vector. -/
def normalizedSteering {d : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d) (y : Point d) : ι → ℂ :=
  (‖toLp 2 (steeringVector frequency y)‖ : ℂ)⁻¹ • steeringVector frequency y

/-- MUSIC noise-space correlation `R(y) = ‖U₂* a(y)‖₂`. -/
def noiseSpaceCorrelation {d : ℕ} {ι q : Type*}
    [Fintype ι] [Fintype q]
    (frequency : ι → Point d) (U₂ : Matrix ι q ℂ) (y : Point d) : ℝ :=
  ‖toLp 2 (U₂ᴴ *ᵥ normalizedSteering frequency y)‖

/-- MUSIC correlation formed from the trailing left singular subspace after a
fixed number of signal singular vectors. -/
noncomputable def rankNoiseSpaceCorrelation
    {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (frequency : ι → Point d) (A : Matrix ι κ ℂ)
    (signalRank : ℕ) (y : Point d) : ℝ :=
  ‖(trailingLeftSingularSubspace A signalRank).starProjection
      (toLp 2 (normalizedSteering frequency y))‖

/-- Uniform distance between two MUSIC correlation functions. -/
def correlationUniformDistance {d : ℕ} (R₁ R₂ : Point d → ℝ) : ℝ :=
  sSup (Set.range fun y => |R₁ y - R₂ y|)

end

end NumDetect
end LeanNumDetect
