import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Multiset.Fintype
import General.SpectralPerturbation.PolynomialRootMatching

/-!
# Characteristic-polynomial roots with algebraic multiplicity

An indexed enumeration retains repeated eigenvalues. Product factorization and
similarity connect these algebraic root lists to the polynomial homotopy.
-/

noncomputable section
open Matrix Polynomial
namespace LeanNumDetect

/-- An eigenvalue list including every root with its algebraic multiplicity. -/
def EigenvalueEnumeration {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin n → ℂ) : Prop :=
  Finset.univ.val.map z = A.charpoly.roots

/-- Every complex square matrix has a full enumeration of its characteristic roots. -/
theorem exists_eigenvalueEnumeration {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ z, EigenvalueEnumeration A z := by
  classical
  let s := A.charpoly.roots
  have hs : Fintype.card s = n := by
    rw [Multiset.card_coe, ← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e := (Fintype.equivFinOfCardEq hs).symm
  refine ⟨fun i => ((e i : s) : ℂ), ?_⟩
  unfold EigenvalueEnumeration
  have he := Finset.univ_map_equiv_to_embedding e
  have hm := congrArg (fun t : Finset s => t.val.map (fun x : s => (x : ℂ))) he
  simpa only [Finset.map_val, Multiset.map_map, Function.comp_def,
    Equiv.coe_toEmbedding, Multiset.map_univ_coe] using hm

/-- Similarity preserves the full eigenvalue multiset. -/
theorem eigenvalueEnumeration_conjugate_iff {n : ℕ}
    (A X : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) (hX : IsUnit X) :
    EigenvalueEnumeration (X⁻¹ * A * X) z ↔ EigenvalueEnumeration A z := by
  unfold EigenvalueEnumeration
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv X ((Matrix.isUnit_iff_isUnit_det X).mp hX), Matrix.one_mul]

/-- The entries of a diagonal matrix enumerate its spectrum, with multiplicities. -/
theorem diagonal_eigenvalueEnumeration {n : ℕ} (a : Fin n → ℂ) :
    EigenvalueEnumeration (diagonal a) a := by
  unfold EigenvalueEnumeration
  rw [Matrix.charpoly_diagonal]
  have h := Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map a)
  simpa only [Multiset.map_map, Function.comp_def, Finset.prod] using h.symm

/-- The monic characteristic polynomial factors over its complete eigenvalue list. -/
theorem EigenvalueEnumeration.eval_eq_rootProduct {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ}
    (hz : EigenvalueEnumeration A z) : A.charpoly.eval = rootProduct z := by
  funext w
  rw [(IsAlgClosed.splits A.charpoly).eval_eq_prod_roots_of_monic A.charpoly_monic,
    ← hz]
  simp only [Multiset.map_map, Function.comp_def, rootProduct, Finset.prod]

/-- Every entry of an enumeration is a characteristic-polynomial root. -/
theorem EigenvalueEnumeration.isRoot {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ}
    (hz : EigenvalueEnumeration A z) (i : Fin n) : A.charpoly.IsRoot (z i) := by
  apply (Polynomial.mem_roots A.charpoly_monic.ne_zero).mp
  rw [← hz]
  exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val _, rfl⟩

end LeanNumDetect
