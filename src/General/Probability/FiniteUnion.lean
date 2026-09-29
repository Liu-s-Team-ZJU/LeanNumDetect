import General.Probability.FiniteMatrixSampling

/-! Finite union bounds for exact uniform counting probability. -/

set_option autoImplicit false

namespace LeanNumDetect.FiniteMatrixSampling

/-- The probability of a union indexed by a finite set is at most the sum of
the individual probabilities, without any independence assumption. -/
theorem probability_exists_finset_le {α ι : Type*} [Fintype α]
    (s : Finset ι) (P : ι → α → Prop) :
    probability (fun x => ∃ i ∈ s, P i x) ≤ ∑ i ∈ s, probability (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [probability]
  | @insert i s hi ih =>
    have heq : (fun x => ∃ j ∈ insert i s, P j x) =
        (fun x => P i x ∨ ∃ j ∈ s, P j x) := by
      funext x
      simp
    rw [heq, Finset.sum_insert hi]
    exact (probability_or_le _ _).trans (add_le_add le_rfl ih)

/-- A uniform bound for each bad event yields a simultaneous success bound. -/
theorem probability_forall_finset_ge {α ι : Type*} [Fintype α] [Nonempty α]
    (s : Finset ι) (P : ι → α → Prop) {b : ℝ}
    (hP : ∀ i ∈ s, probability (fun x => ¬ P i x) ≤ b) :
    1 - (s.card : ℝ) * b ≤ probability (fun x => ∀ i ∈ s, P i x) := by
  classical
  have hbad := (probability_exists_finset_le s (fun i x => ¬ P i x)).trans
    (Finset.sum_le_sum hP)
  simp only [Finset.sum_const, nsmul_eq_mul] at hbad
  have heq : (fun x => ∃ i ∈ s, ¬ P i x) =
      (fun x => ¬ (∀ i ∈ s, P i x)) := by
    funext x
    simp
  rw [heq, probability_not] at hbad
  linarith

end LeanNumDetect.FiniteMatrixSampling
