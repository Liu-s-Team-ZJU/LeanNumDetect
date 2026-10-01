import RandSamp.UniformOffGridRelativeGram

/-!
# Separated off-grid relative Gram and singular-value estimates

Manuscript `cor:separated-offgrid-relative-gram`. The separation endpoints
and sampling rate are exactly those used in the manuscript. Both the
relative Gram estimate and the singular-value bounds hold on one event,
simultaneously for every separated node tuple.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The strict Rayleigh-scale separation assumption makes the improved
deterministic full-Gram lower endpoint positive. -/
theorem uniformSeparatedLower_pos_of_separation (M : ℕ) {Δ : ℝ}
    (hΔ : 2 * Real.pi / ((M : ℝ) + 3 / 2) < Δ) :
    0 < uniformSeparatedLower M Δ := by
  have hden : 0 < (M : ℝ) + 3 / 2 := by positivity
  have hΔ0 : 0 < Δ :=
    (div_pos (by positivity : 0 < 2 * Real.pi) hden).trans hΔ
  have hnum : 2 * Real.pi < ((M : ℝ) + 3 / 2) * Δ := by
    simpa only [mul_comm] using (div_lt_iff₀ hden).mp hΔ
  have hquot : 2 * Real.pi / Δ < (M : ℝ) + 3 / 2 :=
    (div_lt_iff₀ hΔ0).mpr hnum
  exact div_pos (sub_pos.mpr hquot) (by positivity)

/-- The universal sampling property in the unrestricted lower-endpoint
theorem, viewed as a predicate of its one universal constant. -/
def UniformRelativeGramSamplingConstant (C : ℝ) : Prop :=
  ∀ (M s m : ℕ), 2 ≤ M → 2 ≤ s → 1 ≤ m → m ≤ M + 1 →
  ∀ (a ρ η : ℝ), 0 < a → 0 < ρ → ρ < 1 → 0 < η → η < 1 →
  (m = M + 1 ∨ C * (s : ℝ) / (a * ρ ^ 2) *
    offGridSamplingLogFactor M s a ρ η ≤ (m : ℝ)) →
  1 - η ≤ probability (fun Ω : Sample (M + 1) m =>
    ∀ Y : Fin s → ℝ,
      (∀ z : EuclideanSpace ℂ (Fin s),
        a * ‖z‖ ^ 2 ≤ FiniteMatrixSampling.quadratic (fullGram M Y) z) →
      RelativeGramEvent Y ρ Ω)

/-- The separated sampling property, including the singular-value bounds,
with the sampling constant kept explicit. -/
def SeparatedRelativeGramSamplingConstant (C : ℝ) : Prop :=
  ∀ (M s m : ℕ), 2 ≤ M → 2 ≤ s → 1 ≤ m → m ≤ M + 1 →
  ∀ (Δ ρ η : ℝ), 0 < ρ → ρ < 1 → 0 < η → η < 1 →
  2 * Real.pi / ((M : ℝ) + 3 / 2) < Δ →
  Δ ≤ 2 * Real.pi / (s : ℝ) →
  (m = M + 1 ∨ C * (s : ℝ) / (uniformSeparatedLower M Δ * ρ ^ 2) *
    offGridSamplingLogFactor M s (uniformSeparatedLower M Δ) ρ η ≤ (m : ℝ)) →
  1 - η ≤ probability (fun Ω : Sample (M + 1) m =>
    ∀ Y : Fin s → ℝ, AngularSeparated Δ Y →
      RelativeGramEvent Y ρ Ω ∧
      SingularValueEvent Y (uniformSeparatedLower M Δ) (separatedUpper M Δ) ρ Ω)

/-- Specializing a uniform sampling constant to separated tuples preserves
that exact constant. -/
theorem separatedRelativeGramSamplingConstant_of_uniform (C : ℝ)
    (hprob : UniformRelativeGramSamplingConstant C) :
    SeparatedRelativeGramSamplingConstant C := by
  intro M s m hM hs hm hmN Δ ρ η hρ0 hρ1 hη0 hη1 hΔlow hΔhigh hsample
  have ha : 0 < uniformSeparatedLower M Δ :=
    uniformSeparatedLower_pos_of_separation M hΔlow
  have hΔ0 : 0 < Δ :=
    (div_pos (by positivity : 0 < 2 * Real.pi) (by positivity)).trans hΔlow
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hΔupper : Δ ≤ 2 * Real.pi :=
    hΔhigh.trans (div_le_self (by positivity) hsr)
  have hp := hprob M s m hM hs hm hmN (uniformSeparatedLower M Δ) ρ η
    ha hρ0 hρ1 hη0 hη1 hsample
  apply hp.trans
  apply probability_mono
  intro Ω hΩ Y hsep
  have hgram := uniformSeparated_fullGram_bounds (by omega : 1 ≤ M)
    hΔ0 hΔupper Y hsep
  have hrelative : RelativeGramEvent Y ρ Ω := hΩ Y (fun z => (hgram z).1)
  exact ⟨hrelative, singularValueEvent_of_relativeGramEvent (by omega : 0 < s)
    Y ha.le hρ0.le hρ1.le Ω hgram hrelative⟩

/-- One positive universal constant simultaneously satisfies the full
off-grid theorem and its separated singular-value corollary. -/
theorem uniformOffGrid_and_uniformSeparated_sameConstant :
    ∃ C : ℝ, 0 < C ∧ UniformRelativeGramSamplingConstant C ∧
      SeparatedRelativeGramSamplingConstant C := by
  obtain ⟨C, hC, hprob⟩ := uniformOffGrid_relativeGram
  exact ⟨C, hC, hprob, separatedRelativeGramSamplingConstant_of_uniform C hprob⟩

/-- The separated specialization of the uniform off-grid theorem, with
the exact improved lower endpoint and multiplicative singular-value
endpoints. The probability event is uniform over all separated tuples. -/
theorem uniformSeparated_relativeGram_singularValues :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M s m : ℕ), 2 ≤ M → 2 ≤ s → 1 ≤ m → m ≤ M + 1 →
      ∀ (Δ ρ η : ℝ), 0 < ρ → ρ < 1 → 0 < η → η < 1 →
      2 * Real.pi / ((M : ℝ) + 3 / 2) < Δ →
      Δ ≤ 2 * Real.pi / (s : ℝ) →
      (m = M + 1 ∨ C * (s : ℝ) / (uniformSeparatedLower M Δ * ρ ^ 2) *
        offGridSamplingLogFactor M s (uniformSeparatedLower M Δ) ρ η ≤ (m : ℝ)) →
      1 - η ≤ probability (fun Ω : Sample (M + 1) m =>
        ∀ Y : Fin s → ℝ, AngularSeparated Δ Y →
          RelativeGramEvent Y ρ Ω ∧
          SingularValueEvent Y (uniformSeparatedLower M Δ) (separatedUpper M Δ) ρ Ω) := by
  obtain ⟨C, hC, _, hseparated⟩ := uniformOffGrid_and_uniformSeparated_sameConstant
  exact ⟨C, hC, hseparated⟩

/-- A relative Gram event combined with a deterministic bias estimate gives
the manuscript's absolute RIP constant `ρ + (1 + ρ) * γ`, in its equivalent
quadratic-form formulation. -/
theorem relativeGramEvent_bias_bound {M s m : ℕ} (Y : Fin s → ℝ)
    {ρ γ : ℝ} (hρ : 0 ≤ ρ) (Ω : Sample (M + 1) m)
    (hrelative : RelativeGramEvent Y ρ Ω)
    (hbias : ∀ z : EuclideanSpace ℂ (Fin s),
      |FiniteMatrixSampling.quadratic (fullGram M Y) z - ‖z‖ ^ 2| ≤ γ * ‖z‖ ^ 2)
    (z : EuclideanSpace ℂ (Fin s)) :
    |FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z - ‖z‖ ^ 2| ≤
      (ρ + (1 + ρ) * γ) * ‖z‖ ^ 2 := by
  have hdiff :
      |FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z -
        FiniteMatrixSampling.quadratic (fullGram M Y) z| ≤
          ρ * FiniteMatrixSampling.quadratic (fullGram M Y) z := by
    rcases hrelative z with ⟨hlo, hhi⟩
    apply abs_le.mpr
    constructor <;> linarith
  have hfull : FiniteMatrixSampling.quadratic (fullGram M Y) z ≤
      (1 + γ) * ‖z‖ ^ 2 := by
    have h := (abs_le.mp (hbias z)).2
    linarith
  calc
    _ = |(FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z -
        FiniteMatrixSampling.quadratic (fullGram M Y) z) +
        (FiniteMatrixSampling.quadratic (fullGram M Y) z - ‖z‖ ^ 2)| := by
      congr 1
      ring
    _ ≤ |FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z -
        FiniteMatrixSampling.quadratic (fullGram M Y) z| +
        |FiniteMatrixSampling.quadratic (fullGram M Y) z - ‖z‖ ^ 2| := abs_add_le _ _
    _ ≤ ρ * FiniteMatrixSampling.quadratic (fullGram M Y) z + γ * ‖z‖ ^ 2 :=
      add_le_add hdiff (hbias z)
    _ ≤ ρ * ((1 + γ) * ‖z‖ ^ 2) + γ * ‖z‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hfull hρ) (le_refl _)
    _ = (ρ + (1 + ρ) * γ) * ‖z‖ ^ 2 := by ring

end

end LeanNumDetect.RandSamp
