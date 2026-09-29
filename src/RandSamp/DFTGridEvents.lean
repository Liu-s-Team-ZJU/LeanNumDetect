import RandSamp.DFTGridModel
import General.MatrixAnalysis.Coherence
import General.MatrixAnalysis.SpectralInterval

/-! The simultaneous support events in the Cartesian DFT-grid theorem. -/

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- Restrict the normalized sampled DFT matrix to an actual set of columns. -/
def dftSupportMatrix {d N : ℕ} [NeZero N] (m : ℕ)
    (Ω S : Finset (DFTIndex d N)) : Matrix Ω S ℂ :=
  fun k j => dftSampledMatrix m Ω k j.val

/-- The singular-value statement is simultaneous over every nonempty support
of at most `r` grid points, inside one probability event. -/
def DFTGridSingularValueEvent {d N m : ℕ} [NeZero N] (r : ℕ) (ρ : ℝ)
    (Ω : FiniteSample (DFTIndex d N) m) : Prop :=
  ∀ S : Finset (DFTIndex d N), 1 ≤ S.card → S.card ≤ r →
    Real.sqrt (1 - ρ) ≤ matrixSingularValue (dftSupportMatrix m Ω.val S) (S.card - 1) ∧
      matrixSingularValue (dftSupportMatrix m Ω.val S) (S.card - 1) ≤
        matrixSingularValue (dftSupportMatrix m Ω.val S) 0 ∧
      matrixSingularValue (dftSupportMatrix m Ω.val S) 0 ≤ Real.sqrt (1 + ρ)

/-- The order-`r` restricted-isometry condition, with its usual action-energy
meaning and the same simultaneous support quantifier as the manuscript. -/
def DFTGridEnergyEvent {d N m : ℕ} [NeZero N] (r : ℕ) (ρ : ℝ)
    (Ω : FiniteSample (DFTIndex d N) m) : Prop :=
  ∀ S : Finset (DFTIndex d N), 1 ≤ S.card → S.card ≤ r →
    ∀ z : EuclideanSpace ℂ S,
      (1 - ρ) * ‖z‖ ^ 2 ≤ ‖(dftSupportMatrix m Ω.val S).toEuclideanLin z‖ ^ 2 ∧
      ‖(dftSupportMatrix m Ω.val S).toEuclideanLin z‖ ^ 2 ≤ (1 + ρ) * ‖z‖ ^ 2

/-- The manuscript's singular-value event is exactly the order-`r` restricted
isometry event, not merely a sufficient condition for it. -/
theorem dftGridSingularValueEvent_iff_energy {d N m r : ℕ} [NeZero N]
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (Ω : FiniteSample (DFTIndex d N) m) :
    DFTGridSingularValueEvent r ρ Ω ↔ DFTGridEnergyEvent r ρ Ω := by
  classical
  constructor
  · intro h S hS hSr
    apply (matrixSingularValue_interval_iff_norm_sq_bounds
      (dftSupportMatrix m Ω.val S) (by simpa using hS)
      (by linarith : 0 ≤ 1 - ρ) (by linarith : 0 ≤ 1 + ρ)).mp
    simpa only [Fintype.card_coe] using h S hS hSr
  · intro h S hS hSr
    simpa only [Fintype.card_coe] using
      (matrixSingularValue_interval_iff_norm_sq_bounds
        (dftSupportMatrix m Ω.val S) (by simpa using hS)
        (by linarith : 0 ≤ 1 - ρ) (by linarith : 0 ≤ 1 + ρ)).mpr (h S hS hSr)

/-- Control of all nonzero character offsets controls every submatrix. -/
theorem dftGridSingularValueEvent_of_coherence {d N m r : ℕ} [NeZero N]
    (hm : 1 ≤ m) (hr : 2 ≤ r) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (Ω : FiniteSample (DFTIndex d N) m)
    (hcoh : ∀ q : DFTIndex d N, q ≠ 0 →
      ‖(m : ℂ)⁻¹ * ∑ k ∈ Ω.val, dftCharacter q k‖ ≤ ρ / ((r : ℝ) - 1)) :
    DFTGridSingularValueEvent r ρ Ω := by
  classical
  intro S hS hSr
  have hdiag (j : S) :
      ((dftSupportMatrix m Ω.val S)ᴴ * dftSupportMatrix m Ω.val S) j j = 1 := by
    exact dftSampledMatrix_gram_self hm Ω j.val
  have hoff (i j : S) (hij : i ≠ j) :
      ‖((dftSupportMatrix m Ω.val S)ᴴ * dftSupportMatrix m Ω.val S) i j‖ ≤
        ρ / ((r : ℝ) - 1) := by
    change ‖∑ k : Ω.val, star (dftSampledMatrix m Ω.val k i.val) *
      dftSampledMatrix m Ω.val k j.val‖ ≤ _
    rw [dftSampledMatrix_gram]
    exact hcoh (j.val - i.val) (sub_ne_zero.mpr (fun h => hij (Subtype.ext h.symm)))
  simpa only [Fintype.card_coe] using
    matrixSingularValue_bounds_of_coherence (dftSupportMatrix m Ω.val S)
      (by simpa using hS) hr (by simpa using hSr) hρ0 hρ1 hdiag hoff

end

end LeanNumDetect.RandSamp
