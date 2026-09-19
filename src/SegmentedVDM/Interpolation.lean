import General.MatrixAnalysis.RowDeletion

/-! The finite-dimensional Lagrange-interpolation argument of NumDetect,
`lem:minsvd_bound_by_lagInterp_high_dim`. All norms below are Euclidean;
the coefficient sum is the normalized torus L² norm squared by Parseval. -/

set_option autoImplicit false
open scoped BigOperators
open Matrix LeanNumDetect

namespace SegmentedVDM

noncomputable def energy {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ∑ i, ‖v i‖ ^ 2

theorem energy_nonneg {ι : Type*} [Fintype ι] (v : ι → ℂ) : 0 ≤ energy v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem energy_pos {ι : Type*} [Fintype ι] (v : ι → ℂ) (hv : v ≠ 0) :
    0 < energy v := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _,
    sq_pos_of_pos (norm_pos_iff.mpr hi)⟩

theorem dotProduct_norm_sq_le {ι : Type*} [Fintype ι] (c v : ι → ℂ) :
    ‖c ⬝ᵥ v‖ ^ 2 ≤ energy c * energy v := by
  have h := norm_sum_le Finset.univ (fun i => c i * v i)
  simp only [norm_mul] at h
  exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
    (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).2 h).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖c i‖) (fun i => ‖v i‖))

/-- No conjugation is missing: interpolation uses the ordinary transpose. -/
theorem interpolation_energy {ρ ι : Type*} [Fintype ρ] [Fintype ι] [DecidableEq ι]
    (V : Matrix ρ ι ℂ) (C : Matrix ι ρ ℂ) (hCV : C * V = 1) (v : ι → ℂ) :
    energy v ≤ (∑ j, energy (C j)) * energy (V *ᵥ v) := by
  have he : C *ᵥ (V *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hCV, one_mulVec]
  calc
    energy v = ∑ j, ‖C j ⬝ᵥ (V *ᵥ v)‖ ^ 2 := by
      change energy v = energy (C *ᵥ (V *ᵥ v))
      rw [he]
    _ ≤ ∑ j, energy (C j) * energy (V *ᵥ v) :=
      Finset.sum_le_sum fun j _ => dotProduct_norm_sq_le _ _
    _ = _ := (Finset.sum_mul ..).symm

theorem gram_eigenvector_energy {ρ : Type*} [Fintype ρ] {n : ℕ}
    (V : Matrix ρ (Fin n) ℂ) (v : Fin n → ℂ) (eigenvalue : ℝ)
    (he : (Vᴴ * V) *ᵥ v = (eigenvalue : ℂ) • v) :
    energy (V *ᵥ v) = eigenvalue * energy v := by
  change (∑ k, ‖(V *ᵥ v) k‖ ^ 2) = _
  rw [← quadratic_gram]
  unfold quadratic
  rw [he, dotProduct_smul, smul_eq_mul]
  have hh : star v ⬝ᵥ v = (energy v : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul',
      energy, ← Complex.ofReal_pow, ← Complex.ofReal_sum]
  rw [hh]
  simp

/-- A coefficient norm bound gives the smallest singular value bound, including
full column rank; there is no rank hypothesis hidden in this reduction. -/
theorem singularValue_ge_of_interpolation {ρ : Type*} [Fintype ρ] {n : ℕ}
    (V : Matrix ρ (Fin n) ℂ) (C : Matrix (Fin n) ρ ℂ)
    (hCV : C * V = 1) (hn : 0 < n) {B : ℝ} (hB : 0 < B)
    (hC : ∀ j, energy (C j) ≤ B ^ 2) :
    1 / (Real.sqrt n * B) ≤ matrixSingularValue V (n - 1) := by
  obtain ⟨v, hv, he⟩ := singularValue_gram_eigenvector V (by omega : n - 1 < n)
  have hp := energy_pos v hv
  have h := interpolation_energy V C hCV v
  have hsum : (∑ j, energy (C j)) ≤ (n : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin n, B ^ 2 := Finset.sum_le_sum fun j _ => hC j
      _ = _ := by simp
  have hb := h.trans (mul_le_mul_of_nonneg_right hsum (energy_nonneg _))
  rw [gram_eigenvector_energy V v _ he] at hb
  have hcancel : 1 ≤ (n : ℝ) * B ^ 2 * matrixSingularValue V (n - 1) ^ 2 := by
    nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sq_sqrt hnR.le
  have hσ := V.toEuclideanLin.singularValues_nonneg (n - 1)
  change 0 ≤ matrixSingularValue V (n - 1) at hσ
  have hprod : 1 ≤ Real.sqrt n * B * matrixSingularValue V (n - 1) := by
    have hnonneg : 0 ≤ Real.sqrt n * B * matrixSingularValue V (n - 1) := by positivity
    have hsq : 1 ^ 2 ≤ (Real.sqrt n * B * matrixSingularValue V (n - 1)) ^ 2 := by
      simpa only [mul_pow, hs, one_pow] using hcancel
    exact (sq_le_sq₀ (by norm_num) hnonneg).mp hsq
  exact (div_le_iff₀ (mul_pos (Real.sqrt_pos.2 hnR) hB)).2 (by nlinarith)

end SegmentedVDM
