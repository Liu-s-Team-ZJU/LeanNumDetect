import RandSamp.SeparatedOffGridRelativeGram
import General.MatrixAnalysis.HermitianOperatorNorm

/-!
# Euclidean operator-norm bias and Rayleigh-scale constants

The absolute quadratic-form bias of a Hermitian Gram matrix is equivalent
to its Euclidean operator-norm bias. This converts the relative Gram event
into the manuscript's operator RIP estimate. The final scalar lemma gives
a positive lower endpoint uniform in bandwidth under `Δ ≥ C₀/M`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

theorem fourierFullGram_isHermitian {s : ℕ} (M : ℕ) (Y : Fin s → ℝ) :
    (fullGram M Y).IsHermitian := by
  have hsum : (∑ k : Fin (M + 1), fourierPopulation Y k).IsHermitian :=
    isSelfAdjoint_sum Finset.univ (fun k _ => (fourierRowGram_posSemidef Y k.val).1)
  exact hsum.smul (by simp [IsSelfAdjoint])

theorem fourierSampleGram_isHermitian {N s m : ℕ} (Y : Fin s → ℝ) (Ω : Sample N m) :
    (sampleMean (fourierPopulation Y) Ω).IsHermitian := by
  have hsum : (∑ k ∈ Ω.val, fourierPopulation Y k).IsHermitian :=
    isSelfAdjoint_sum Ω.val (fun k _ => (fourierRowGram_posSemidef Y k.val).1)
  exact hsum.smul (by simp [IsSelfAdjoint])

/-- The manuscript's ordinary operator RIP bias follows exactly from
the relative Gram event and the deterministic full-Gram operator bias. -/
theorem relativeGramEvent_operator_bias_bound {M s m : ℕ} (Y : Fin s → ℝ)
    {ρ γ : ℝ} (hρ : 0 ≤ ρ) (Ω : Sample (M + 1) m)
    (hrelative : RelativeGramEvent Y ρ Ω)
    (hbias : ‖(fullGram M Y - 1).toEuclideanLin.toContinuousLinearMap‖ ≤ γ) :
    ‖(sampleMean (fourierPopulation Y) Ω - 1).toEuclideanLin.toContinuousLinearMap‖ ≤
      ρ + (1 + ρ) * γ := by
  have hγ : 0 ≤ γ := (norm_nonneg _).trans hbias
  have hfull := (hermitian_operatorBias_le_iff_quadratic_bias_le
    (fullGram M Y) (fourierFullGram_isHermitian M Y) hγ).mp hbias
  apply (hermitian_operatorBias_le_iff_quadratic_bias_le
    (sampleMean (fourierPopulation Y) Ω) (fourierSampleGram_isHermitian Y Ω)
    (by positivity : 0 ≤ ρ + (1 + ρ) * γ)).mpr
  exact relativeGramEvent_bias_bound Y hρ Ω hrelative hfull

/-- Separation by a fixed strict Rayleigh multiple gives a positive
uniform lower Gram endpoint, independently of the bandwidth. -/
theorem uniformSeparatedLower_rayleigh_scale_bound {M : ℕ} (hM : 1 ≤ M)
    {Δ C₀ : ℝ} (hC₀ : 2 * Real.pi < C₀) (hΔ : C₀ / (M : ℝ) ≤ Δ) :
    0 < 1 - 2 * Real.pi / C₀ ∧
      1 - 2 * Real.pi / C₀ ≤ uniformSeparatedLower M Δ := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hC0 : 0 < C₀ := (by positivity : 0 < 2 * Real.pi).trans hC₀
  have hΔ0 : 0 < Δ := (div_pos hC0 hM0).trans_le hΔ
  have hfrac : 2 * Real.pi / C₀ < 1 := (div_lt_one hC0).mpr hC₀
  refine ⟨by linarith, ?_⟩
  have hquot : 2 * Real.pi / Δ ≤ 2 * Real.pi * (M : ℝ) / C₀ := by
    calc
      _ ≤ 2 * Real.pi / (C₀ / M) :=
        div_le_div_of_nonneg_left (by positivity) (div_pos hC0 hM0) hΔ
      _ = _ := by simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]; ring
  unfold uniformSeparatedLower
  apply (le_div_iff₀ (by positivity : 0 < (M : ℝ) + 1)).mpr
  have hnonneg : 0 ≤ 2 * Real.pi / C₀ := by positivity
  calc
    (1 - 2 * Real.pi / C₀) * ((M : ℝ) + 1) ≤
        (M : ℝ) + 3 / 2 - (2 * Real.pi / C₀) * M := by
      have he : (M : ℝ) + 3 / 2 - (2 * Real.pi / C₀) * M =
          (1 - 2 * Real.pi / C₀) * ((M : ℝ) + 1) + (1 / 2 + 2 * Real.pi / C₀) := by ring
      rw [he]
      exact le_add_of_nonneg_right (by linarith)
    _ ≤ (M : ℝ) + 3 / 2 - 2 * Real.pi / Δ := by
      apply sub_le_sub_left _ _
      simpa only [div_mul_eq_mul_div, mul_assoc] using hquot

end

end LeanNumDetect.RandSamp
