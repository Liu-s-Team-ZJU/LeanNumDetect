import RandSamp.DFTGrid
import General.MatrixAnalysis.Reindex
import General.MatrixAnalysis.SpectralInterval

/-! The one-dimensional DFT grid as the one-coordinate Cartesian grid.
The original row and column index types are retained by explicit bijections. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- A scalar grid index viewed as its one-coordinate tuple. -/
def dftOneIndexEquiv (M : ℕ) : Fin (M + 1) ≃ DFTIndex 1 (M + 1) :=
  (Equiv.funUnique (Fin 1) (Fin (M + 1))).symm

/-- The induced relabelling of elements of an arbitrary support or sample. -/
def dftOneFinsetEquiv {M : ℕ} (S : Finset (Fin (M + 1))) :
    S ≃ S.map (dftOneIndexEquiv M).toEmbedding :=
  (dftOneIndexEquiv M).subtypeEquiv (by intro j; simp)

/-- The original normalized one-dimensional DFT matrix restricted to `S`. -/
def dftSupportMatrixOne {M : ℕ} (m : ℕ) (Ω S : Finset (Fin (M + 1))) :
    Matrix Ω S ℂ :=
  fun k j => sampledVandermonde m (fun q : Fin (M + 1) =>
    2 * Real.pi * q.val / (M + 1)) Ω k j.val

/-- The scalar DFT support matrix is a row and column relabelling of the
Cartesian support matrix at `d = 1`. -/
theorem dftSupportMatrixOne_eq_reindex {M : ℕ} (m : ℕ)
    (Ω S : Finset (Fin (M + 1))) :
    dftSupportMatrixOne m Ω S =
      Matrix.submatrix (dftSupportMatrix m (Ω.map (dftOneIndexEquiv M).toEmbedding)
        (S.map (dftOneIndexEquiv M).toEmbedding))
        (dftOneFinsetEquiv Ω) (dftOneFinsetEquiv S) := by
  ext k j
  simp only [dftSupportMatrixOne, sampledVandermonde, Matrix.submatrix_apply,
    dftSupportMatrix, dftSampledMatrix, dftCharacter_one]
  congr 1
  unfold fourierRow
  congr 1
  change Complex.I * (((k.val.val : ℝ) *
      (2 * Real.pi * j.val.val / (M + 1) : ℝ) : ℝ) : ℂ) =
    2 * Real.pi * Complex.I * ((k.val.val : ℂ) * (j.val.val : ℂ)) /
      ((M + 1 : ℕ) : ℂ)
  push_cast
  ring

/-- Every singular value agrees after the one-coordinate identification. -/
theorem dftSupportMatrixOne_singularValue {M : ℕ} (m : ℕ)
    (Ω S : Finset (Fin (M + 1))) (i : ℕ) :
    matrixSingularValue (dftSupportMatrixOne m Ω S) i =
      matrixSingularValue (dftSupportMatrix m (Ω.map (dftOneIndexEquiv M).toEmbedding)
        (S.map (dftOneIndexEquiv M).toEmbedding)) i := by
  rw [dftSupportMatrixOne_eq_reindex]
  exact matrixSingularValue_submatrix_equiv _ _ _ _

/-- The original one-dimensional event, quantified over all scalar supports. -/
def DFTGridOneSingularValueEvent {M m : ℕ} (r : ℕ) (ρ : ℝ)
    (Ω : Sample (M + 1) m) : Prop :=
  ∀ S : Finset (Fin (M + 1)), 1 ≤ S.card → S.card ≤ r →
    Real.sqrt (1 - ρ) ≤ matrixSingularValue (dftSupportMatrixOne m Ω.val S) (S.card - 1) ∧
      matrixSingularValue (dftSupportMatrixOne m Ω.val S) (S.card - 1) ≤
        matrixSingularValue (dftSupportMatrixOne m Ω.val S) 0 ∧
      matrixSingularValue (dftSupportMatrixOne m Ω.val S) 0 ≤ Real.sqrt (1 + ρ)

/-- The original scalar-index event is exactly the Cartesian event at `d = 1`,
including the quantifier over every admissible support. -/
theorem dftGridOneSingularValueEvent_iff {M m r : ℕ} {ρ : ℝ}
    (Ω : Sample (M + 1) m) :
    DFTGridSingularValueEvent r ρ (finiteSampleEquiv (dftOneIndexEquiv M) m Ω) ↔
      DFTGridOneSingularValueEvent r ρ Ω := by
  classical
  constructor
  · intro h S hS hSr
    have hh := h (S.map (dftOneIndexEquiv M).toEmbedding)
      (by simpa using hS) (by simpa using hSr)
    simpa only [finiteSampleEquiv_val, Finset.card_map,
      ← dftSupportMatrixOne_singularValue] using hh
  · intro h S hS hSr
    obtain ⟨T, rfl⟩ := (dftOneIndexEquiv M).finsetCongr.surjective S
    have hh := h T (by simpa [Equiv.finsetCongr_apply] using hS)
      (by simpa [Equiv.finsetCongr_apply] using hSr)
    simpa only [Equiv.finsetCongr_apply, finiteSampleEquiv_val,
      Finset.card_map, ← dftSupportMatrixOne_singularValue] using hh

/-- The original one-dimensional restricted-isometry energy event. -/
def DFTGridOneEnergyEvent {M m : ℕ} (r : ℕ) (ρ : ℝ)
    (Ω : Sample (M + 1) m) : Prop :=
  ∀ S : Finset (Fin (M + 1)), 1 ≤ S.card → S.card ≤ r →
    ∀ z : EuclideanSpace ℂ S,
      (1 - ρ) * ‖z‖ ^ 2 ≤ ‖(dftSupportMatrixOne m Ω.val S).toEuclideanLin z‖ ^ 2 ∧
      ‖(dftSupportMatrixOne m Ω.val S).toEuclideanLin z‖ ^ 2 ≤ (1 + ρ) * ‖z‖ ^ 2

/-- The one-dimensional singular-value and restricted-isometry formulations
are exactly equivalent, rather than separately estimated. -/
theorem dftGridOne_singularValueEvent_iff_energyEvent {M m r : ℕ} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (Ω : Sample (M + 1) m) :
    DFTGridOneSingularValueEvent r ρ Ω ↔ DFTGridOneEnergyEvent r ρ Ω := by
  classical
  unfold DFTGridOneSingularValueEvent DFTGridOneEnergyEvent
  apply forall_congr'
  intro S
  apply forall_congr'
  intro hS
  apply forall_congr'
  intro _
  simpa only [Fintype.card_coe] using
    matrixSingularValue_interval_iff_norm_sq_bounds (dftSupportMatrixOne m Ω.val S)
      (by simpa using hS) (by linarith : 0 ≤ 1 - ρ) (by linarith : 0 ≤ 1 + ρ)

/-- Manuscript corollary `thm:dft-grid-rip`: the original one-dimensional
DFT-grid statement, with precisely its original `log (4 M / η)` sampling rate,
is the Cartesian theorem specialized to `d = 1`. -/
theorem dftGridOne_singularValues {M m r : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) (hmM : m ≤ M + 1)
    (hr : 2 ≤ r) (hrM : r ≤ M + 1)
    {ρ η : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hsample : 4 * ((r : ℝ) - 1) ^ 2 / ρ ^ 2 *
      Real.log (4 * M / η) ≤ m) :
    1 - η ≤ probability (DFTGridOneSingularValueEvent (M := M) (m := m) r ρ) := by
  have h := dftGrid_singularValues (d := 1) (by decide) hM hm
    (by simpa using hmM) hr (by simpa using hrM) hρ0 hρ1 hη0 hη1 (by
      simpa only [pow_one, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hsample)
  rw [← probability_comp_equiv (finiteSampleEquiv (dftOneIndexEquiv M) m)] at h
  simpa only [dftGridOneSingularValueEvent_iff] using h

/-- The equivalent one-dimensional restricted-isometry corollary follows from
the same specialized Cartesian theorem. -/
theorem dftGridOne_restrictedIsometry {M m r : ℕ}
    (hM : 1 ≤ M) (hm : 1 ≤ m) (hmM : m ≤ M + 1)
    (hr : 2 ≤ r) (hrM : r ≤ M + 1)
    {ρ η : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hsample : 4 * ((r : ℝ) - 1) ^ 2 / ρ ^ 2 *
      Real.log (4 * M / η) ≤ m) :
    1 - η ≤ probability (DFTGridOneEnergyEvent (M := M) (m := m) r ρ) := by
  apply (dftGridOne_singularValues hM hm hmM hr hrM hρ0 hρ1 hη0 hη1 hsample).trans
  exact probability_mono (fun Ω hΩ =>
    (dftGridOne_singularValueEvent_iff_energyEvent hρ0.le hρ1.le Ω).mp hΩ)

end

end LeanNumDetect.RandSamp
