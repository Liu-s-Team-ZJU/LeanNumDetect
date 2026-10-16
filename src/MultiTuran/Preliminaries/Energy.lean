import MultiTuran.Preliminaries.Volume
import MultiTuran.Preliminaries.Interpolation
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Actual continuous energy and discrete norming

`continuousEnergy` integrates the squared modulus over the genuine thickened
row set. `ContinuousNorming` is the inequality in `ass:norming`. The transfer
below records the elementary spectral consequence of that inequality and a
continuous lower bound. It does not assume or assert a Turán or Nikolskii
inequality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp MeasureTheory
open scoped BigOperators

namespace LeanNumDetect.MultiTuran
noncomputable section

theorem continuous_exponentialSum {d n : ℕ} (Y : Fin n → Point d)
    (c : Fin n → ℂ) : Continuous (exponentialSum Y c) := by
  unfold exponentialSum
  fun_prop

/-- All continuous energies below integrate continuous functions on compact
sets, so their integrals have the usual finite-energy meaning. -/
theorem exponentialSum_energy_integrableOn {d n : ℕ} (Y : Fin n → Point d)
    (c : Fin n → ℂ) {S : Set (Point d)} (hS : IsCompact S) :
    IntegrableOn (fun t => ‖exponentialSum Y c t‖ ^ 2) S :=
  ((continuous_exponentialSum Y c).norm.pow 2).continuousOn.integrableOn_compact hS

/-- Squared `L²` norm on an actual subset of Euclidean frequency space. -/
def setEnergy {d n : ℕ} (Y : Fin n → Point d) (c : Fin n → ℂ)
    (S : Set (Point d)) : ℝ :=
  ∫ t in S, ‖exponentialSum Y c t‖ ^ 2

theorem setEnergy_nonneg {d n : ℕ} (Y : Fin n → Point d) (c : Fin n → ℂ)
    (S : Set (Point d)) : 0 ≤ setEnergy Y c S :=
  integral_nonneg fun _ => sq_nonneg _

/-- The continuous energy over `E_Λ`. -/
def continuousEnergy {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (c : Fin n → ℂ) : ℝ :=
  setEnergy Y c G.thickening

/-- The continuous `L²` norm over `E_Λ`. -/
def continuousL2Norm {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (c : Fin n → ℂ) : ℝ :=
  Real.sqrt (continuousEnergy G Y c)

/-- The discrete squared norm on the actual measured product rows. -/
def discreteEnergy {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (c : Fin n → ℂ) : ℝ :=
  ∑ k : G.Row, ‖exponentialSum Y c (fun q => (G.rowVector k q : ℝ))‖ ^ 2

/-- Exact inequality `eq:norming`, with the uniform coefficient quantifier. -/
def ContinuousNorming {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (η : ℝ) : Prop :=
  ∀ c : Fin n → ℂ, η * continuousEnergy G Y c ≤ discreteEnergy G Y c

theorem continuousEnergy_nonneg {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (c : Fin n → ℂ) : 0 ≤ continuousEnergy G Y c :=
  setEnergy_nonneg Y c G.thickening

@[simp] theorem continuousL2Norm_sq {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (c : Fin n → ℂ) :
    continuousL2Norm G Y c ^ 2 = continuousEnergy G Y c :=
  Real.sq_sqrt (continuousEnergy_nonneg G Y c)

/-- The matrix action is exactly the measured exponential sum energy. -/
theorem discreteEnergy_eq_matrix_energy {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (c : Fin n → ℂ) :
    discreteEnergy G Y c =
      ∑ k : G.Row, ‖∑ j, generalizedVandermonde G Y k j * c j‖ ^ 2 := by
  unfold discreteEnergy
  apply Finset.sum_congr rfl
  intro k _
  rw [← generalizedVandermonde_mulVec]
  rfl

/-- The square root of the actual row energy is the Euclidean action norm. -/
theorem matrix_action_norm_eq_sqrt_discreteEnergy {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (z : EuclideanSpace ℂ (Fin n)) :
    ‖(generalizedVandermonde G Y).toEuclideanLin z‖ =
      Real.sqrt (discreteEnergy G Y (ofLp z)) := by
  rw [EuclideanSpace.norm_eq, discreteEnergy_eq_matrix_energy]
  rfl

/-- Exact attained minimum characterization `eq:minsv-characterization`:
the least column singular value is the minimum sampled norm over unit vectors. -/
theorem minimumSingularValue_characterization {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (hn : 0 < n) :
    (∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ = 1 →
      matrixSingularValue (generalizedVandermonde G Y) (n - 1) ≤
        Real.sqrt (discreteEnergy G Y (ofLp z))) ∧
    ∃ z : EuclideanSpace ℂ (Fin n), ‖z‖ = 1 ∧
      matrixSingularValue (generalizedVandermonde G Y) (n - 1) =
        Real.sqrt (discreteEnergy G Y (ofLp z)) := by
  let A := generalizedVandermonde G Y
  constructor
  · intro z hz
    have h := lastMatrixSingularValue_mul_norm_le A (by simpa using hn) z
    dsimp only [A] at h
    simpa only [Fintype.card_fin, hz, mul_one,
      matrix_action_norm_eq_sqrt_discreteEnergy] using h
  · obtain ⟨z, hz, he⟩ := exists_unit_vector_norm_sq_eq_singularValue_sq A
      (i := n - 1) (by simpa using Nat.sub_lt hn Nat.zero_lt_one)
    refine ⟨z, hz, ?_⟩
    have hnorm : ‖A.toEuclideanLin z‖ = matrixSingularValue A (n - 1) :=
      (sq_eq_sq₀ (norm_nonneg _) (A.toEuclideanLin.singularValues_nonneg _)).mp he
    exact hnorm.symm.trans (matrix_action_norm_eq_sqrt_discreteEnergy G Y z)

/-- The continuous-to-discrete spectral step, with actual integrals and actual
matrix singular values. The continuous bound remains an explicit premise. -/
theorem minimumSingularValue_ge_of_continuousNorming
    {d n : ℕ} (G : SegmentedGrid d) (Y : Fin n → Point d) (hn : 0 < n)
    {η b : ℝ} (hη : 0 ≤ η) (hb : 0 ≤ b)
    (hnorming : ContinuousNorming G Y η)
    (hcontinuous : ∀ c : Fin n → ℂ,
      b ^ 2 * (∑ j, ‖c j‖ ^ 2) ≤ continuousEnergy G Y c) :
    Real.sqrt η * b ≤ matrixSingularValue (generalizedVandermonde G Y) (n - 1) := by
  apply minimumSingularValue_ge_of_energy_lower _ hn (mul_nonneg (Real.sqrt_nonneg _) hb)
  intro c
  rw [mul_pow, Real.sq_sqrt hη, ← discreteEnergy_eq_matrix_energy]
  calc
    η * b ^ 2 * (∑ j, ‖c j‖ ^ 2) = η * (b ^ 2 * (∑ j, ‖c j‖ ^ 2)) := by ring
    _ ≤ η * continuousEnergy G Y c := mul_le_mul_of_nonneg_left (hcontinuous c) hη
    _ ≤ discreteEnergy G Y c := hnorming c

/-- An `L²` lower bound is equivalent to its squared-energy version for a
nonnegative coefficient. -/
theorem continuousEnergy_lower_of_L2_lower
    {d n : ℕ} (G : SegmentedGrid d) (Y : Fin n → Point d)
    {b : ℝ} (hb : 0 ≤ b)
    (hcontinuous : ∀ c : Fin n → ℂ,
      b * Real.sqrt (∑ j, ‖c j‖ ^ 2) ≤ continuousL2Norm G Y c) :
    ∀ c : Fin n → ℂ,
      b ^ 2 * (∑ j, ‖c j‖ ^ 2) ≤ continuousEnergy G Y c := by
  intro c
  have h := (sq_le_sq₀ (mul_nonneg hb (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg (continuousEnergy G Y c))).mpr (hcontinuous c)
  rwa [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (continuousEnergy_nonneg G Y c)] at h

end
end LeanNumDetect.MultiTuran
