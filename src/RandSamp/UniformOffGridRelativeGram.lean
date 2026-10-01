import RandSamp.OffGridAtomicEvent
import RandSamp.OffGridSeparatedBounds
import RandSamp.OffGridSamplingRate
import General.Probability.BoundedAtomicSampling

/-!
# Uniform off-grid relative Gram estimates

Manuscript `thm:uniform-offgrid-relative-gram` and
`cor:separated-offgrid-relative-gram`. The existential sampling constant is
universal. The event quantifies over every node tuple and coefficient vector
inside one uniform fixed-cardinality sampling probability.

The sole external dependency is the original BDJR bounded-row theorem,
registered in `External/README.md`. Every finite-law, normalization,
without-replacement, separation, and sample-rate conversion is proved.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

theorem probability_eq_one_of_forall {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) (hP : ∀ x, P x) : probability P = 1 := by
  classical
  have hfilter : Finset.univ.filter P = (Finset.univ : Finset α) :=
    Finset.filter_eq_self.mpr (fun x _ => hP x)
  simp only [probability, hfilter, Finset.card_univ]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

theorem relativeGramEvent_fullSample {M s : ℕ} (Y : Fin s → ℝ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (Ω : Sample (M + 1) (M + 1)) :
    RelativeGramEvent Y ρ Ω := by
  have hΩ : Ω.val = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [Ω.property]
  have he : sampleMean (fourierPopulation Y) Ω = fullGram M Y := by
    simp only [sampleMean, sampleSum, hΩ, fullGram, mean]
  intro z
  rw [he]
  have hq : 0 ≤ FiniteMatrixSampling.quadratic (fullGram M Y) z := by
    rw [← norm_fullFourierSignal_sq]
    exact sq_nonneg _
  constructor <;> nlinarith [mul_nonneg hρ hq]

/-- Exactly manuscript `thm:uniform-offgrid-relative-gram`, including its
full-sampling alternative and its unrestricted positive lower endpoint. -/
theorem uniformOffGrid_relativeGram :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M s m : ℕ), 2 ≤ M → 2 ≤ s → 1 ≤ m → m ≤ M + 1 →
      ∀ (a ρ η : ℝ), 0 < a → 0 < ρ → ρ < 1 → 0 < η → η < 1 →
      (m = M + 1 ∨ C * (s : ℝ) / (a * ρ ^ 2) *
        offGridSamplingLogFactor M s a ρ η ≤ (m : ℝ)) →
      1 - η ≤ probability (fun Ω : Sample (M + 1) m =>
        ∀ Y : Fin s → ℝ,
          (∀ z : EuclideanSpace ℂ (Fin s),
            a * ‖z‖ ^ 2 ≤ FiniteMatrixSampling.quadratic (fullGram M Y) z) →
          RelativeGramEvent Y ρ Ω) := by
  obtain ⟨C₀, hC₀, hprob⟩ := boundedAtomicSample_concentration
  obtain ⟨L, hL, hcomparison⟩ := offGrid_atomic_logFactor_le
  refine ⟨4 * C₀ * L, by positivity, ?_⟩
  intro M s m hM hs hm hmN a ρ η ha hρ0 hρ1 hη0 hη1 hsample
  letI : Nonempty (Sample (M + 1) m) := sample_nonempty hmN
  by_cases hfull : m = M + 1
  · subst m
    rw [probability_eq_one_of_forall]
    · linarith
    · intro Ω Y _
      exact relativeGramEvent_fullSample Y hρ0.le Ω
  by_cases hclass : ∃ Y : Fin s → ℝ,
      ∀ z : EuclideanSpace ℂ (Fin s), a * ‖z‖ ^ 2 ≤ FiniteMatrixSampling.quadratic (fullGram M Y) z
  · obtain ⟨Y₀, hY₀⟩ := hclass
    have ha1 : a ≤ 1 := fullGram_lower_le_one (by omega) Y₀ hY₀
    have hS : 1 ≤ 4 * (s : ℝ) / a := by
      have hsr : (2 : ℝ) ≤ s := by exact_mod_cast hs
      apply (le_div_iff₀ ha).2
      nlinarith
    have hrate : C₀ * (4 * (s : ℝ) / a) / ρ ^ 2 *
        boundedAtomicSamplingLogFactor (4 * (s : ℝ) / a)
          (fourierAtomicGridSize M) ρ η ≤ (m : ℝ) := by
      have hlog := hcomparison M s a ρ η hM hs ha ha1 hρ0 hρ1 hη0 hη1
      calc
        _ ≤ C₀ * (4 * (s : ℝ) / a) / ρ ^ 2 *
            (L * offGridSamplingLogFactor M s a ρ η) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = (4 * C₀ * L) * (s : ℝ) / (a * ρ ^ 2) *
            offGridSamplingLogFactor M s a ρ η := by ring
        _ ≤ _ := hsample.resolve_left hfull
    have hp := hprob (M + 1) (fourierAtomicGridSize M) m (by omega)
      (fourierAtomicGridSize_pos M) (by omega) hmN (4 * (s : ℝ) / a) ρ η
      hS hρ0 hρ1 hη0 hη1 (rawFourierGridRow M) (rawFourierGridRow_bound M) hrate
    apply hp.trans
    apply probability_mono
    intro Ω hΩ Y hY
    exact relativeGramEvent_of_atomicGridDeviation Y ha Ω hΩ hY
  · rw [probability_eq_one_of_forall]
    · linarith
    · intro Ω Y hY
      exact (hclass ⟨Y, hY⟩).elim

end

end LeanNumDetect.RandSamp
