import RandSamp.DFTGridEvents
import RandSamp.DFTGridSamplingRate
import General.Probability.FiniteScalarConcentration
import General.Probability.FiniteUnion

/-! The Cartesian DFT-grid theorem, uniform over all supports of a prescribed
maximum size. All probability bounds concern uniform sampling without
replacement from the actual multidimensional grid. -/

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The union bound counts nonzero offsets, rather than pairs of grid columns. -/
theorem dftGrid_coherence_probability {d N m : ℕ} [NeZero N]
    (hm : 1 ≤ m) (hmL : m ≤ N ^ d) {u : ℝ} (hu : 0 < u) :
    1 - (((N ^ d : ℕ) : ℝ) - 1) *
      (4 * Real.exp (-(m : ℝ) * u ^ 2 / 4)) ≤
      probability (fun Ω : FiniteSample (DFTIndex d N) m =>
        ∀ q : DFTIndex d N, q ≠ 0 →
          ‖(m : ℂ)⁻¹ * ∑ k ∈ Ω.val, dftCharacter q k‖ ≤ u) := by
  classical
  letI : Nonempty (FiniteSample (DFTIndex d N) m) :=
    finiteSample_nonempty (by simpa using hmL)
  have h := probability_forall_finset_ge
    ((Finset.univ : Finset (DFTIndex d N)).erase 0)
    (fun q (Ω : FiniteSample (DFTIndex d N) m) =>
      ‖(m : ℂ)⁻¹ * ∑ k ∈ Ω.val, dftCharacter q k‖ ≤ u)
    (b := 4 * Real.exp (-(m : ℝ) * u ^ 2 / 4)) (by
      intro q hq
      simpa only [not_le] using finiteSample_complex_norm_probability_le hm
        (by simpa using hmL) (dftCharacter q) (by intro k; simp)
        (sum_dftCharacter_eq_zero (Finset.mem_erase.mp hq).1) hu)
  have hL : 1 ≤ N ^ d := by
    have : 0 < N ^ d := by
      simpa using (Fintype.card_pos : 0 < Fintype.card (DFTIndex d N))
    omega
  simpa [Finset.card_erase_of_mem, Nat.cast_sub hL] using h

/-- Manuscript `thm:dft-grid-rip-higher-dimensional`, with exactly the stated
sampling threshold and a single event covering every nonempty support. -/
theorem dftGrid_singularValues {d M m r : ℕ}
    (_hd : 1 ≤ d) (_hM : 1 ≤ M) (hm : 1 ≤ m) (hmL : m ≤ (M + 1) ^ d)
    (hr : 2 ≤ r) (hrL : r ≤ (M + 1) ^ d)
    {ρ η : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη0 : 0 < η) (_hη1 : η < 1)
    (hsample : 4 * ((r : ℝ) - 1) ^ 2 / ρ ^ 2 *
      Real.log (4 * ((((M + 1) ^ d : ℕ) : ℝ) - 1) / η) ≤ m) :
    1 - η ≤ probability (DFTGridSingularValueEvent (d := d) (N := M + 1) (m := m) r ρ) := by
  classical
  have hr' : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hL : (1 : ℝ) < ((M + 1) ^ d : ℕ) := by
    exact_mod_cast (show 1 < (M + 1) ^ d by omega)
  have hu : 0 < ρ / ((r : ℝ) - 1) := div_pos hρ0 (sub_pos.mpr hr')
  have hprob := dftGrid_coherence_probability (d := d) (N := M + 1) hm hmL hu
  have htail := dft_failure_bound_of_sample_size hL hr' hρ0 hη0 hsample
  exact (sub_le_sub_left htail 1).trans (hprob.trans
    (probability_mono (fun Ω hΩ =>
      dftGridSingularValueEvent_of_coherence hm hr hρ0.le hρ1.le Ω hΩ)))

/-- The identical probability theorem in the equivalent restricted-isometry
energy formulation appearing in the manuscript. -/
theorem dftGrid_restrictedIsometry {d M m r : ℕ}
    (hd : 1 ≤ d) (hM : 1 ≤ M) (hm : 1 ≤ m) (hmL : m ≤ (M + 1) ^ d)
    (hr : 2 ≤ r) (hrL : r ≤ (M + 1) ^ d)
    {ρ η : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hsample : 4 * ((r : ℝ) - 1) ^ 2 / ρ ^ 2 *
      Real.log (4 * ((((M + 1) ^ d : ℕ) : ℝ) - 1) / η) ≤ m) :
    1 - η ≤ probability (DFTGridEnergyEvent (d := d) (N := M + 1) (m := m) r ρ) := by
  apply (dftGrid_singularValues hd hM hm hmL hr hrL hρ0 hρ1 hη0 hη1 hsample).trans
  exact probability_mono (fun Ω hΩ => (dftGridSingularValueEvent_iff_energy hρ0.le hρ1.le Ω).mp hΩ)

end

end LeanNumDetect.RandSamp
