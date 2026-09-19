import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.Interval.Finset.Fin

/-!
The full Hermitian Courant--Fischer principle, proved from the orthonormal
eigenbasis. The dimension argument uses the kernel of a coordinate restriction:
a subspace of dimension larger than the number of restricted coordinates contains
a unit vector on which all those coordinates vanish.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped InnerProductSpace

namespace LeanNumDetect

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι]

/-- A subcollection of an orthonormal basis spans a space of the expected dimension. -/
theorem finrank_orthonormal_span (b : OrthonormalBasis ι ℂ E) (s : Finset ι) :
    Module.finrank ℂ (Submodule.span ℂ (b '' (s : Set ι))) = s.card := by
  classical
  have hli : LinearIndependent ℂ (fun j : s => b j) :=
    b.toBasis.linearIndependent.comp _ Subtype.val_injective
  have he : Set.range (fun j : s => b j) = b '' (s : Set ι) := by
    ext x
    simp
  have hh := finrank_span_eq_card hli
  change Module.finrank ℂ (Submodule.span ℂ (Set.range (fun j : s => b j))) =
    Fintype.card s at hh
  rw [he] at hh
  simpa only [Fintype.card_coe] using hh

omit [FiniteDimensional ℂ E] in
/-- Coordinates outside a chosen basis span vanish. -/
theorem orthonormal_inner_eq_zero_of_mem_span (b : OrthonormalBasis ι ℂ E)
    (s : Finset ι) {x : E} (hx : x ∈ Submodule.span ℂ (b '' (s : Set ι)))
    {j : ι} (hj : j ∉ s) : ⟪b j, x⟫_ℂ = 0 := by
  classical
  have hs := b.toBasis.repr_support_subset_of_mem_span (s : Set ι) hx
  have hz : b.toBasis.repr x j = 0 := by
    by_contra h
    exact hj (hs (Finsupp.mem_support_iff.mpr h))
  simpa only [OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply] using hz

/-- A dimension surplus supplies a unit vector annihilated by prescribed coordinates. -/
theorem exists_unit_mem_coord_zero (b : OrthonormalBasis ι ℂ E)
    (S : Submodule ℂ E) (s : Finset ι) (hd : s.card < Module.finrank ℂ S) :
    ∃ x : E, x ∈ S ∧ ‖x‖ = 1 ∧ ∀ j ∈ s, ⟪b j, x⟫_ℂ = 0 := by
  classical
  let f : S →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun x j => b.repr (x : E) j
      map_add' := by intro x y; ext j; simp
      map_smul' := by intro c x; ext j; simp }
  have hk : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hd)
  obtain ⟨x, hx, hx0⟩ := (LinearMap.ker f).ne_bot_iff.mp hk
  have hx0' : (x : E) ≠ 0 := by
    intro h
    apply hx0
    exact Subtype.ext h
  refine ⟨(‖(x : E)‖⁻¹ : ℂ) • (x : E), S.smul_mem _ x.property,
    norm_smul_inv_norm hx0', ?_⟩
  intro j hj
  have he : b.repr (x : E) j = 0 := congrFun (LinearMap.mem_ker.mp hx) ⟨j, hj⟩
  rw [OrthonormalBasis.repr_apply_apply] at he
  rw [inner_smul_right, he, mul_zero]

end Coordinates

section Symmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)

/-- The Rayleigh quadratic form expanded in a Hermitian eigenbasis. -/
theorem re_inner_eq_sum_eigenvalues (x : E) :
    RCLike.re ⟪x, T x⟫_ℂ = ∑ j : Fin (Module.finrank ℂ E),
      hT.eigenvalues rfl j * ‖⟪hT.eigenvectorBasis rfl j, x⟫_ℂ‖ ^ 2 := by
  let b := hT.eigenvectorBasis rfl
  have he (j : Fin (Module.finrank ℂ E)) :
      ⟪b j, T x⟫_ℂ = (hT.eigenvalues rfl j : ℂ) * ⟪b j, x⟫_ℂ := by
    rw [← hT, hT.apply_eigenvectorBasis]
    simp only [inner_smul_real_left, Complex.real_smul, b]
  rw [← b.sum_inner_mul_inner x (T x), map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [he, mul_left_comm]
  change RCLike.re ((hT.eigenvalues rfl j) •
    (⟪x, b j⟫_ℂ * ⟪b j, x⟫_ℂ)) = _
  rw [RCLike.smul_re, inner_mul_symm_re_eq_norm, norm_mul,
    ← inner_conj_symm x (b j), RCLike.norm_conj, ← pow_two]

/-- A spectral lower bound on the nonzero coordinates bounds the Rayleigh form. -/
theorem rayleigh_lower_of_support (x : E) {c : ℝ}
    (h : ∀ j : Fin (Module.finrank ℂ E),
      ⟪hT.eigenvectorBasis rfl j, x⟫_ℂ ≠ 0 → c ≤ hT.eigenvalues rfl j) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, T x⟫_ℂ := by
  let b := hT.eigenvectorBasis rfl
  rw [re_inner_eq_sum_eigenvalues T hT,
    ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : ⟪b j, x⟫_ℂ = 0
  · simp only [b] at hj
    simp only [b, hj, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, le_refl]
  · exact mul_le_mul_of_nonneg_right (h j hj) (sq_nonneg _)

/-- A spectral upper bound on the nonzero coordinates bounds the Rayleigh form. -/
theorem rayleigh_upper_of_support (x : E) {c : ℝ}
    (h : ∀ j : Fin (Module.finrank ℂ E),
      ⟪hT.eigenvectorBasis rfl j, x⟫_ℂ ≠ 0 → hT.eigenvalues rfl j ≤ c) :
    RCLike.re ⟪x, T x⟫_ℂ ≤ c * ‖x‖ ^ 2 := by
  let b := hT.eigenvectorBasis rfl
  rw [re_inner_eq_sum_eigenvalues T hT,
    ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : ⟪b j, x⟫_ℂ = 0
  · simp only [b] at hj
    simp only [b, hj, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, le_refl]
  · exact mul_le_mul_of_nonneg_right (h j hj) (sq_nonneg _)

/-- The max--min half of Courant--Fischer, with attainment and the universal bound. -/
theorem symmetric_eigenvalue_max_min (i : Fin (Module.finrank ℂ E)) :
    IsGreatest {c : ℝ | ∃ S : Submodule ℂ E,
      Module.finrank ℂ S = i.val + 1 ∧
      ∀ x ∈ S, ‖x‖ = 1 → c ≤ RCLike.re ⟪x, T x⟫_ℂ}
      (hT.eigenvalues rfl i) := by
  classical
  let b := hT.eigenvectorBasis rfl
  constructor
  · refine ⟨Submodule.span ℂ (b '' (Finset.Iic i : Set (Fin (Module.finrank ℂ E)))),
      ?_, ?_⟩
    · simpa using finrank_orthonormal_span b (Finset.Iic i)
    · intro x hx hn
      have hl := rayleigh_lower_of_support T hT x (c := hT.eigenvalues rfl i) (by
        intro j hj
        have hji : j ≤ i := by
          by_contra hji
          exact hj (orthonormal_inner_eq_zero_of_mem_span b (Finset.Iic i) hx
            (by simpa using hji))
        exact hT.eigenvalues_antitone rfl hji)
      simpa only [hn, one_pow, mul_one] using hl
  · rintro c ⟨S, hd, hS⟩
    obtain ⟨x, hx, hn, hz⟩ := exists_unit_mem_coord_zero b S (Finset.Iio i)
      (by simpa only [Fin.card_Iio, hd] using Nat.lt_succ_self i.val)
    have hu := rayleigh_upper_of_support T hT x (c := hT.eigenvalues rfl i) (by
      intro j hj
      have hij : i ≤ j := by
        by_contra hij
        exact hj (hz j (Finset.mem_Iio.mpr (lt_of_not_ge hij)))
      exact hT.eigenvalues_antitone rfl hij)
    have hu' : RCLike.re ⟪x, T x⟫_ℂ ≤ hT.eigenvalues rfl i := by
      simpa only [hn, one_pow, mul_one] using hu
    exact (hS x hx hn).trans hu'

/-- The min--max half of Courant--Fischer, including the attaining tail eigenspace. -/
theorem symmetric_eigenvalue_min_max (i : Fin (Module.finrank ℂ E)) :
    IsLeast {c : ℝ | ∃ S : Submodule ℂ E,
      Module.finrank ℂ S = Module.finrank ℂ E - i.val ∧
      ∀ x ∈ S, ‖x‖ = 1 → RCLike.re ⟪x, T x⟫_ℂ ≤ c}
      (hT.eigenvalues rfl i) := by
  classical
  let b := hT.eigenvectorBasis rfl
  constructor
  · refine ⟨Submodule.span ℂ (b '' (Finset.Ici i : Set (Fin (Module.finrank ℂ E)))),
      ?_, ?_⟩
    · simpa using finrank_orthonormal_span b (Finset.Ici i)
    · intro x hx hn
      have hu := rayleigh_upper_of_support T hT x (c := hT.eigenvalues rfl i) (by
        intro j hj
        have hij : i ≤ j := by
          by_contra hij
          exact hj (orthonormal_inner_eq_zero_of_mem_span b (Finset.Ici i) hx
            (by simpa using hij))
        exact hT.eigenvalues_antitone rfl hij)
      simpa only [hn, one_pow, mul_one] using hu
  · rintro c ⟨S, hd, hS⟩
    obtain ⟨x, hx, hn, hz⟩ := exists_unit_mem_coord_zero b S (Finset.Ioi i) (by
      rw [Fin.card_Ioi, hd]
      have hi := i.isLt
      omega)
    have hl := rayleigh_lower_of_support T hT x (c := hT.eigenvalues rfl i) (by
      intro j hj
      have hji : j ≤ i := by
        by_contra hji
        exact hj (hz j (Finset.mem_Ioi.mpr (lt_of_not_ge hji)))
      exact hT.eigenvalues_antitone rfl hji)
    have hl' : hT.eigenvalues rfl i ≤ RCLike.re ⟪x, T x⟫_ℂ := by
      simpa only [hn, one_pow, mul_one] using hl
    exact hl'.trans (hS x hx hn)

/-- Both variational characterizations for a symmetric operator. -/
theorem symmetric_courant_fischer (i : Fin (Module.finrank ℂ E)) :
    IsGreatest {c : ℝ | ∃ S : Submodule ℂ E,
      Module.finrank ℂ S = i.val + 1 ∧
      ∀ x ∈ S, ‖x‖ = 1 → c ≤ RCLike.re ⟪x, T x⟫_ℂ}
      (hT.eigenvalues rfl i) ∧
    IsLeast {c : ℝ | ∃ S : Submodule ℂ E,
      Module.finrank ℂ S = Module.finrank ℂ E - i.val ∧
      ∀ x ∈ S, ‖x‖ = 1 → RCLike.re ⟪x, T x⟫_ℂ ≤ c}
      (hT.eigenvalues rfl i) :=
  ⟨symmetric_eigenvalue_max_min T hT i, symmetric_eigenvalue_min_max T hT i⟩

end Symmetric

/-- The full Hermitian Courant--Fischer theorem for matrices, with zero-based
indices and the source's unit-vector normalization. -/
theorem hermitian_courant_fischer {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.toEuclideanLin.IsSymmetric)
    (i : Fin (Module.finrank ℂ (EuclideanSpace ℂ n))) :
    IsGreatest {c : ℝ | ∃ S : Submodule ℂ (EuclideanSpace ℂ n),
      Module.finrank ℂ S = i.val + 1 ∧
      ∀ x ∈ S, ‖x‖ = 1 → c ≤ RCLike.re ⟪x, A.toEuclideanLin x⟫_ℂ}
      (hA.eigenvalues rfl i) ∧
    IsLeast {c : ℝ | ∃ S : Submodule ℂ (EuclideanSpace ℂ n),
      Module.finrank ℂ S = Module.finrank ℂ (EuclideanSpace ℂ n) - i.val ∧
      ∀ x ∈ S, ‖x‖ = 1 → RCLike.re ⟪x, A.toEuclideanLin x⟫_ℂ ≤ c}
      (hA.eigenvalues rfl i) :=
  symmetric_courant_fischer A.toEuclideanLin hA i

end LeanNumDetect
