import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Finite uniform sampling and quadratic forms for matrix concentration. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators InnerProductSpace
open Matrix

namespace LeanNumDetect.FiniteMatrixSampling

/-- The equally likely outcomes when sampling `m` of `N` labelled objects. -/
abbrev Sample (N m : ℕ) := {Ω : Finset (Fin N) // Ω.card = m}

/-- Uniform counting probability; no random matrix or node set is built into it. -/
noncomputable def probability {α : Type*} [Fintype α] (P : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

/-- The real quadratic form of a complex matrix, in Euclidean coordinates. -/
noncomputable def quadratic {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (x : EuclideanSpace ℂ (Fin d)) : ℝ :=
  Complex.re ⟪x, A.toEuclideanLin x⟫_ℂ

/-- The set of unit-vector Rayleigh values. Its least and greatest elements are
exactly the extreme eigenvalues when the matrix is Hermitian. -/
def rayleighValues {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : Set ℝ :=
  {q | ∃ x : EuclideanSpace ℂ (Fin d), ‖x‖ = 1 ∧ quadratic A x = q}

/-- Population expectation of one uniform draw. -/
noncomputable def mean {N d : ℕ} (X : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ := ((N : ℂ)⁻¹) • ∑ k, X k

/-- The unnormalized sum for one sample without replacement. -/
noncomputable def sampleSum {N d m : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) (Ω : Sample N m) :
    Matrix (Fin d) (Fin d) ℂ := ∑ k ∈ Ω.val, X k

/-- Average of the sampled matrices. -/
noncomputable def sampleMean {N d m : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) (Ω : Sample N m) :
    Matrix (Fin d) (Fin d) ℂ := ((m : ℂ)⁻¹) • sampleSum X Ω

theorem sample_nonempty {N m : ℕ} (hm : m ≤ N) : Nonempty (Sample N m) := by
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin N))) (by simpa using hm)
  exact ⟨⟨s, hs⟩⟩

theorem probability_mono {α : Type*} [Fintype α] {P Q : α → Prop}
    (h : ∀ x, P x → Q x) : probability P ≤ probability Q := by
  classical
  unfold probability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show Finset.univ.filter P ⊆ Finset.univ.filter Q from
    by intro x hx; simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      h x (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx))

theorem probability_or_le {α : Type*} [Fintype α] (P Q : α → Prop) :
    probability (fun x => P x ∨ Q x) ≤ probability P + probability Q := by
  classical
  unfold probability
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := Finset.card_union_le (Finset.univ.filter P) (Finset.univ.filter Q)
  rw [← Finset.filter_or] at h
  convert (show (((Finset.univ.filter (fun x => P x ∨ Q x)).card : ℕ) : ℝ) ≤
      (Finset.univ.filter P).card + (Finset.univ.filter Q).card from by exact_mod_cast h) using 1 <;>
    congr 2
  ext x
  simp

theorem probability_not {α : Type*} [Fintype α] [Nonempty α] (P : α → Prop) :
    probability (fun x => ¬ P x) = 1 - probability P := by
  classical
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α)) P
  have hr : ((Finset.univ.filter P).card : ℝ) +
      ((Finset.univ.filter (fun x => ¬ P x)).card : ℝ) = Fintype.card α := by
    exact_mod_cast h
  unfold probability
  apply (eq_sub_iff_add_eq).mpr
  rw [← add_div]
  have hr' : ((Finset.univ.filter (fun x => ¬ P x)).card : ℝ) +
      ((Finset.univ.filter P).card : ℝ) = (Fintype.card α : ℝ) := by linarith only [hr]
  calc
    _ = (Fintype.card α : ℝ) / (Fintype.card α : ℝ) := by
      congr 1
      convert hr' using 1
      congr 2
      congr 1
      ext x
      simp
    _ = 1 := div_self hc

@[simp] theorem quadratic_zero {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    quadratic A 0 = 0 := by simp [quadratic]

@[simp] theorem quadratic_real_smul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (r : ℝ) (x : EuclideanSpace ℂ (Fin d)) :
    quadratic A ((r : ℂ) • x) = r ^ 2 * quadratic A x := by
  simp only [quadratic, map_smul, inner_smul_left, inner_smul_right]
  simp [Complex.mul_re, pow_two, mul_assoc, mul_left_comm]

@[simp] theorem quadratic_smul_matrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (r : ℝ) (x : EuclideanSpace ℂ (Fin d)) :
    quadratic ((r : ℂ) • A) x = r * quadratic A x := by
  unfold quadratic
  have he : (((r : ℂ) • A).toEuclideanLin x) = (r : ℂ) • (A.toEuclideanLin x) := by
    change WithLp.toLp 2 (((r : ℂ) • A) *ᵥ WithLp.ofLp x) = _
    rw [Matrix.smul_mulVec, WithLp.toLp_smul]
    rfl
  rw [he, inner_smul_right]
  simp

/-- Passing from unit vectors to arbitrary vectors is a proved normalization step. -/
theorem bounds_of_unit_bounds {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    {a b : ℝ} (h : ∀ x : EuclideanSpace ℂ (Fin d), ‖x‖ = 1 →
      a ≤ quadratic A x ∧ quadratic A x ≤ b) :
    ∀ x : EuclideanSpace ℂ (Fin d),
      a * ‖x‖ ^ 2 ≤ quadratic A x ∧ quadratic A x ≤ b * ‖x‖ ^ 2 := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hh := h ((‖x‖⁻¹ : ℂ) • x) (norm_smul_inv_norm hx)
  rw [← Complex.ofReal_inv, quadratic_real_smul] at hh
  have hnorm : ‖x‖ ^ 2 * ‖x‖⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hn.ne', one_pow]
  have he : (‖x‖⁻¹ ^ 2 * quadratic A x) * ‖x‖ ^ 2 = quadratic A x := by
    calc
      _ = (‖x‖ ^ 2 * ‖x‖⁻¹ ^ 2) * quadratic A x := by ring
      _ = _ := by rw [hnorm, one_mul]
  constructor
  · simpa only [he] using mul_le_mul_of_nonneg_right hh.1 (sq_nonneg ‖x‖)
  · simpa only [he] using mul_le_mul_of_nonneg_right hh.2 (sq_nonneg ‖x‖)

/-- Compactness supplies actual extreme Rayleigh values. -/
theorem exists_rayleigh_extrema {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    ∃ l u : ℝ, IsLeast (rayleighValues A) l ∧ IsGreatest (rayleighValues A) u := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hn : (Metric.sphere (0 : EuclideanSpace ℂ (Fin d)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hc : Continuous (quadratic A) := by
    unfold quadratic
    fun_prop
  obtain ⟨x, hx, hxmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ (Fin d)) 1).exists_isMinOn
    hn hc.continuousOn
  obtain ⟨y, hy, hymax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ (Fin d)) 1).exists_isMaxOn
    hn hc.continuousOn
  refine ⟨quadratic A x, quadratic A y, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ⟨x, by simpa using hx, rfl⟩
  · rintro q ⟨z, hz, rfl⟩
    exact hxmin (by simpa using hz)
  · exact ⟨y, by simpa using hy, rfl⟩
  · rintro q ⟨z, hz, rfl⟩
    exact hymax (by simpa using hz)

end LeanNumDetect.FiniteMatrixSampling
