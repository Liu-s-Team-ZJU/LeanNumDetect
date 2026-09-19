import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! The Moore–Penrose inverse of arbitrary finite complex matrices, including
rank-deficient matrices. Construction uses orthogonal projections and a linear
section of the range; no external result is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
namespace LeanNumDetect

/-- The four Penrose equations, with no rank hypothesis. -/
structure IsMoorePenrose {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n m ℂ) : Prop where
  mul_self : A * B * A = A
  self_mul : B * A * B = B
  left_hermitian : (A * B)ᴴ = A * B
  right_hermitian : (B * A)ᴴ = B * A

private theorem exists_inverse_projections
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (f : E →ₗ[ℂ] F) :
    ∃ b : F →ₗ[ℂ] E,
      f ∘ₗ b = f.range.starProjection.toLinearMap ∧
      b ∘ₗ f = f.kerᗮ.starProjection.toLinearMap ∧
      ∀ y, b y ∈ f.kerᗮ := by
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let b := f.kerᗮ.starProjection.toLinearMap ∘ₗ g ∘ₗ f.range.orthogonalProjectionOnto.toLinearMap
  have hproj (x : E) : f (f.kerᗮ.starProjection x) = f x := by
    rw [Submodule.starProjection_orthogonal_val, map_sub]
    have hz : f (f.ker.starProjection x) = 0 :=
      Submodule.starProjection_apply_mem f.ker x
    rw [hz, sub_zero]
  have hfb (y : F) : f (b y) = f.range.starProjection y := by
    dsimp [b]
    rw [hproj]
    exact congrArg Subtype.val (LinearMap.congr_fun hg (f.range.orthogonalProjectionOnto y))
  have hbmem (y : F) : b y ∈ f.kerᗮ := Submodule.starProjection_apply_mem _ _
  refine ⟨b, LinearMap.ext hfb, LinearMap.ext (fun x => ?_), hbmem⟩
  apply Eq.symm
  apply Submodule.eq_starProjection_of_mem_orthogonal (hbmem (f x))
  rw [Submodule.orthogonal_orthogonal]
  change f (x - b (f x)) = 0
  rw [map_sub, hfb, Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self f x),
    sub_self]

theorem exists_moorePenrose {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : ∃ B, IsMoorePenrose A B := by
  classical
  obtain ⟨b, hab, hba, hbmem⟩ := exists_inverse_projections A.toEuclideanLin
  let B : Matrix n m ℂ := Matrix.toEuclideanLin.symm b
  have hb : B.toEuclideanLin = b := Matrix.toEuclideanLin.apply_symm_apply b
  have hab' : (A * B).toEuclideanLin = A.toEuclideanLin.range.starProjection.toLinearMap := by
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, hb] using hab
  have hba' : (B * A).toEuclideanLin = A.toEuclideanLin.kerᗮ.starProjection.toLinearMap := by
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, hb] using hba
  refine ⟨B, ⟨?_, ?_, ?_, ?_⟩⟩
  · apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, hab']
    apply LinearMap.ext
    intro x
    exact Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self A.toEuclideanLin x)
  · apply Matrix.toEuclideanLin.injective
    rw [Matrix.toLpLin_mul_same, hba', hb]
    apply LinearMap.ext
    intro x
    exact Submodule.starProjection_eq_self_iff.mpr (hbmem x)
  · apply Matrix.toEuclideanLin.injective
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hab']
    exact (Submodule.starProjection_isSymmetric _).adjoint_eq
  · apply Matrix.toEuclideanLin.injective
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hba']
    exact (Submodule.starProjection_isSymmetric _).adjoint_eq

/-- The unique Moore–Penrose inverse; defined for every rectangular complex matrix. -/
def moorePenrose {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : Matrix n m ℂ :=
  (exists_moorePenrose A).choose

theorem moorePenrose_spec {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : IsMoorePenrose A (moorePenrose A) :=
  (exists_moorePenrose A).choose_spec

private theorem hermitian_absorption_eq {n : Type*} [Fintype n]
    (P Q : Matrix n n ℂ) (hP : Pᴴ = P) (hQ : Qᴴ = Q)
    (hPQ : P * Q = Q) (hQP : Q * P = P) : P = Q := by
  have h := congrArg Matrix.conjTranspose hPQ
  simpa only [Matrix.conjTranspose_mul, hP, hQ, hQP] using h

/-- The Penrose equations characterize the inverse uniquely, even at deficient rank. -/
theorem IsMoorePenrose.unique {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m n ℂ} {B C : Matrix n m ℂ}
    (hB : IsMoorePenrose A B) (hC : IsMoorePenrose A C) : B = C := by
  have hl : A * B = A * C := hermitian_absorption_eq _ _
    hB.left_hermitian hC.left_hermitian
    (by rw [← Matrix.mul_assoc, hB.mul_self])
    (by rw [← Matrix.mul_assoc, hC.mul_self])
  have hp : (C * A) * (B * A) = C * A := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A B A, hB.mul_self]
  have hq : (B * A) * (C * A) = B * A := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A C A, hC.mul_self]
  have hr : C * A = B * A := by
    have h := congrArg Matrix.conjTranspose hp
    simpa only [Matrix.conjTranspose_mul, hB.right_hermitian,
      hC.right_hermitian, hq] using h.symm
  calc
    B = B * (A * B) := by rw [← Matrix.mul_assoc, hB.self_mul]
    _ = B * (A * C) := by rw [hl]
    _ = C * A * C := by rw [← Matrix.mul_assoc, ← hr]
    _ = C := hC.self_mul

/-- The usual Gram formula is valid when the Gram matrix is invertible. -/
theorem moorePenrose_eq_gram {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hA : IsUnit (Aᴴ * A)) :
    moorePenrose A = (Aᴴ * A)⁻¹ * Aᴴ := by
  have hleft : ((Aᴴ * A)⁻¹ * Aᴴ) * A = 1 := by
    rw [Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  apply (moorePenrose_spec A).unique
  constructor
  · rw [Matrix.mul_assoc, hleft, Matrix.mul_one]
  · rw [hleft, Matrix.one_mul]
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
  · rw [hleft, Matrix.conjTranspose_one]

/-- Unitary changes of column basis commute with the MP inverse at every rank. -/
theorem moorePenrose_mul_unitary {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (Q : Matrix n n ℂ) (hQ : Qᴴ * Q = 1) :
    moorePenrose (A * Q) = Qᴴ * moorePenrose A := by
  have hQQ : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQ
  let B := moorePenrose A
  have hb := moorePenrose_spec A
  have hl : (A * Q) * (Qᴴ * B) = A * B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Qᴴ, hQQ, Matrix.one_mul]
  apply (moorePenrose_spec (A * Q)).unique
  constructor
  · rw [hl, ← Matrix.mul_assoc, hb.mul_self]
  · calc
      (Qᴴ * B) * (A * Q) * (Qᴴ * B) = Qᴴ * (B * A * B) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Q Qᴴ, hQQ, Matrix.one_mul]
      _ = Qᴴ * B := by rw [hb.self_mul]
  · rw [hl]; exact hb.left_hermitian
  · have he : (Qᴴ * B) * (A * Q) = Qᴴ * (B * A) * Q := by
      simp only [Matrix.mul_assoc]
    rw [he, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hb.right_hermitian]
    simp only [Matrix.mul_assoc, B]

end LeanNumDetect
