import SegmentedVDM.ClumpBound
import General.MatrixAnalysis.Reindex
import General.Finite.PeriodicClumpLift

/-!
An admission-free lower bound for a one-dimensional consecutive-frequency
Vandermonde matrix with one short clump. The proof specializes the existing
constructive interpolation-packet bound: all sources share one label, the
localization and averaging degrees are zero, and the physical spacing is one.
The coefficient may depend on the source count. This is sufficient for the
multiclump manuscript, whose final smallest-singular-value coefficient may
depend on the clump sizes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Matrix WithLp

namespace LeanNumDetect.SingleClumpVandermonde
noncomputable section

/-- The unnormalized rows `0, …, N` at real angular nodes. -/
def consecutive {s : ℕ} (N : ℕ) (x : Fin s → ℝ) : Matrix (Fin (N + 1)) (Fin s) ℂ :=
  fun k j => Complex.exp (Complex.I * (((k.val : ℝ) * x j : ℝ) : ℂ))

/-- All nodes lie in one clump; the slot is their original index. -/
def singleClump (s : ℕ) : SegmentedVDM.Clumps s s where
  label _ := 0
  slot := id
  injective := by
    intro i j h
    exact congrArg Prod.snd h

theorem segmented_singleton_rows_singularValue {s : ℕ} (N : ℕ) (x : Fin s → ℝ) (i : ℕ) :
    matrixSingularValue (SegmentedVDM.vandermonde 0 N 1 x) i =
      matrixSingularValue (consecutive N x) i := by
  apply congrArg (fun values : ℕ →₀ ℝ => values i)
  apply singularValues_eq_of_norm_eq
  intro z
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change (∑ k : Fin (N + 1) × Fin 1,
    ‖∑ j, SegmentedVDM.vandermonde 0 N 1 x k j * z j‖ ^ 2) =
      ∑ k : Fin (N + 1), ‖∑ j, consecutive N x k j * z j‖ ^ 2
  rw [Fintype.sum_prod_type]
  simp [SegmentedVDM.vandermonde, SegmentedVDM.steering, consecutive]

/-- Explicit constructive single-clump lower bound. No spectral result from
external literature and no analytic admission is used in this proof. -/
theorem minimumSingularValue_lower {s N : ℕ} (hs : 0 < s) (hN : 2 * s ≤ N)
    (x : Fin s → ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hscale : ((N : ℝ) / s) * Δ ≤ Real.pi)
    (hgap : ∀ i j, i ≠ j → Δ ≤ |x i - x j|)
    (hdiam : ∀ i j, |x i - x j| ≤ Real.pi / 2) :
    (Real.sqrt (1 / 2 : ℝ)) ^ s * Real.sqrt ((N : ℝ) / ((s : ℝ) * s)) *
        ((N : ℝ) * Δ / (Real.sqrt 2 * Real.pi * s)) ^ (s - 1) ≤
      matrixSingularValue (consecutive N x) (s - 1) := by
  have h := SegmentedVDM.clump_singularValue_bound_of_split
    (singleClump s) hs (by omega) 0 0 N hN (1 : ℝ) Δ (by norm_num) hΔ x
    (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (by simpa only [mul_one] using hscale) hgap
    (fun i j _ => by simpa using hdiam i j)
    (fun i j hij => False.elim (hij rfl))
  rw [← SegmentedVDM.sqrt_pow_eq_rpow (1 / 2 : ℝ) (by norm_num)] at h
  simpa only [Nat.zero_add, Nat.add_zero, Nat.cast_one, mul_one,
    segmented_singleton_rows_singularValue] using h

/-- A positive source-count-dependent lower coefficient after factoring
`√N (NΔ)^(s−1)` out of the preceding estimate. -/
def lowerCoefficient (s : ℕ) : ℝ :=
  (Real.sqrt (1 / 2 : ℝ)) ^ s /
    ((s : ℝ) * (Real.sqrt 2 * Real.pi * s) ^ (s - 1))

theorem lowerCoefficient_pos {s : ℕ} (hs : 0 < s) : 0 < lowerCoefficient s := by
  unfold lowerCoefficient
  positivity

/-- A singleton requires no spacing parameter, and its one column has the
expected `√N` lower bound for every bandwidth. -/
theorem minimumSingularValue_singleton_lower (N : ℕ) (x : Fin 1 → ℝ) :
    Real.sqrt (N : ℝ) ≤ matrixSingularValue (consecutive N x) 0 := by
  apply le_singularValues_of_subspace (consecutive N x).toEuclideanLin
    (i := 0) (by simp) ⊤ (by simp)
  intro z _
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).1
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  simp only [EuclideanSpace.norm_sq_eq]
  change (N : ℝ) * (∑ j : Fin 1, ‖z j‖ ^ 2) ≤
    ∑ k : Fin (N + 1), ‖∑ j : Fin 1, consecutive N x k j * z j‖ ^ 2
  simp only [Fin.sum_univ_one, consecutive, norm_mul, Complex.norm_exp_I_mul_ofReal,
    one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  nlinarith [sq_nonneg ‖z 0‖]

theorem minimumSingularValue_lower_factored {s N : ℕ} (hs : 0 < s) (hN : 2 * s ≤ N)
    (x : Fin s → ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (hscale : ((N : ℝ) / s) * Δ ≤ Real.pi)
    (hgap : ∀ i j, i ≠ j → Δ ≤ |x i - x j|)
    (hdiam : ∀ i j, |x i - x j| ≤ Real.pi / 2) :
    lowerCoefficient s * Real.sqrt (N : ℝ) * ((N : ℝ) * Δ) ^ (s - 1) ≤
      matrixSingularValue (consecutive N x) (s - 1) := by
  have h := minimumSingularValue_lower hs hN x hΔ hscale hgap hdiam
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hroot : Real.sqrt ((N : ℝ) / ((s : ℝ) * s)) = Real.sqrt (N : ℝ) / s := by
    rw [Real.sqrt_div (Nat.cast_nonneg N), ← pow_two,
      Real.sqrt_sq hsR.le]
  rw [hroot, div_pow] at h
  convert h using 1
  unfold lowerCoefficient
  ring

/-- Integer changes of the real lifts preserve every matrix entry. -/
theorem consecutive_sub_winding {s : ℕ} (N : ℕ) (x : Fin s → ℝ) (p : Fin s → ℤ) :
    consecutive N (fun j => x j - 2 * Real.pi * p j) = consecutive N x := by
  ext k j
  unfold consecutive
  have he : Complex.I * (((k.val : ℝ) * (x j - 2 * Real.pi * p j) : ℝ) : ℂ) =
      Complex.I * (((k.val : ℝ) * x j : ℝ) : ℂ) -
        (((k.val : ℤ) * p j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- Periodic-distance version of the constructive lower bound, valid for
arbitrary real representatives of the angular nodes. -/
theorem periodic_minimumSingularValue_lower_factored {s N : ℕ}
    (hs : 0 < s) (hN : 2 * s ≤ N) (x : Fin s → ℝ) {Δ w : ℝ}
    (hΔ : 0 < Δ) (hw : 0 ≤ w) (hwpi : w ≤ Real.pi / 2)
    (hscale : ((N : ℝ) / s) * Δ ≤ Real.pi)
    (hgap : ∀ i j, i ≠ j → ∀ p : ℤ, Δ ≤ |x i - x j - 2 * Real.pi * p|)
    (hdiam : ∀ i j, ∃ p : ℤ, |x i - x j - 2 * Real.pi * p| ≤ w) :
    lowerCoefficient s * Real.sqrt (N : ℝ) * ((N : ℝ) * Δ) ^ (s - 1) ≤
      matrixSingularValue (consecutive N x) (s - 1) := by
  have hshort : 3 * w < 2 * Real.pi := by nlinarith [Real.pi_pos]
  obtain ⟨p, hp⟩ := periodic_clump_lift hs x hw hshort hdiam
  let y : Fin s → ℝ := fun j => x j - 2 * Real.pi * p j
  have hgap' (i j : Fin s) (hij : i ≠ j) : Δ ≤ |y i - y j| := by
    have h := hgap i j hij (p i - p j)
    convert h using 1
    congr 1
    dsimp [y]
    push_cast
    ring
  have hdiam' (i j : Fin s) : |y i - y j| ≤ Real.pi / 2 := by
    have h := Metric.dist_le_diam_of_mem (Set.finite_range y).isBounded
      (Set.mem_range_self i) (Set.mem_range_self j)
    rw [Real.dist_eq] at h
    exact h.trans (hp.trans hwpi)
  have h := minimumSingularValue_lower_factored hs hN y hΔ hscale hgap' hdiam'
  rw [show consecutive N y = consecutive N x from consecutive_sub_winding N x p] at h
  exact h

end
end LeanNumDetect.SingleClumpVandermonde
