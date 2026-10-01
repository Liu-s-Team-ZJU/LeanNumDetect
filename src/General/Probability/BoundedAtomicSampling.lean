import General.Probability.BoundedAtomicConcentration
import General.Probability.BoundedAtomicSamplingRate
import General.Probability.RestrictedDeviationHinge

/-! Uniform restricted Gram control for finite bounded dictionaries under
sampling without replacement. The BDJR theorem is used only for independent
samples; the entire conversion to fixed-size subsets is proved by convex
comparison of positive-part deviations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section

theorem boundedAtomicSample_concentration :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N Q m : ℕ), 0 < N → 0 < Q → 0 < m → m ≤ N →
      ∀ (S ρ η : ℝ), 1 ≤ S → 0 < ρ → ρ < 1 → 0 < η → η < 1 →
      ∀ (row : Fin N → Fin Q → ℂ), (∀ k j, ‖row k j‖ ≤ 1) →
      C * S / ρ ^ 2 * boundedAtomicSamplingLogFactor S Q ρ η ≤ (m : ℝ) →
      1 - η ≤ probability (fun Ω : Sample N m =>
        atomicGramDeviation S row (sampleMean (atomicRowGram row) Ω) ≤ ρ) := by
  obtain ⟨κ, c₀, c₁, hκ, hc₀, hc₁, hind⟩ := boundedAtomicIid_concentration
  obtain ⟨C, hC, hrate⟩ := boundedAtomic_universal_rate hκ hc₀ hc₁
  refine ⟨C, hC, ?_⟩
  intro N Q m hN hQ hm hmN S ρ η hS hρ0 hρ1 hη0 hη1 row hrow hsample
  let δ := boundedAtomicAccuracyScale κ c₁ * ρ
  obtain ⟨hδ0, hδκ, hδρ, hsource, htailη⟩ :=
    hrate S Q ρ η m hS (by exact_mod_cast hQ) hρ0 hρ1 hη0 hη1 hsample
  have hsource' : c₀ * δ⁻¹ ^ 2 * S * Real.log (Real.exp 1 * (Q : ℝ)) *
      Real.log (S / δ) ^ 2 ≤ (m : ℝ) := by
    convert hsource using 1
    simp only [div_eq_mul_inv, inv_pow]
    ring
  have hind' := hind N Q m hN hQ hm S δ (by linarith) hδ0 hδκ row hrow hsource'
  have hiid : probability (fun ω : Fin m → Fin N =>
      ρ / 2 < atomicGramDeviation S row (atomicIidMeanGram row ω)) ≤
        2 * Real.exp (-(δ ^ 2 * (m : ℝ) / S)) :=
    (probability_mono fun ω hω => lt_of_le_of_lt hδρ hω).trans hind'
  let T : Matrix (Fin Q) (Fin Q) ℂ →ᵃ[ℝ] Matrix (Fin Q) (Fin Q) ℂ :=
    (m : ℝ)⁻¹ • (LinearMap.id : Matrix (Fin Q) (Fin Q) ℂ →ₗ[ℝ]
      Matrix (Fin Q) (Fin Q) ℂ).toAffineMap -
      AffineMap.const ℝ _ (mean (atomicRowGram row))
  have hbound : ∀ ω : Fin m → Fin N,
      restrictedAbsoluteSup (atomicCoefficientTests S row)
        (T (∑ i, atomicRowGram row (ω i))) ≤ S + 1 := by
    intro ω
    exact atomicIidGramDeviation_le (by linarith) row hrow ω
  have hiid' : probability (fun ω : Fin m → Fin N =>
      ρ / 2 < restrictedAbsoluteSup (atomicCoefficientTests S row)
        (T (∑ i, atomicRowGram row (ω i)))) ≤
        2 * Real.exp (-(δ ^ 2 * (m : ℝ) / S)) := hiid
  have hprob := finiteSample_restrictedDeviation_probability_ge
    (by simpa using hmN) (atomicRowGram row) (atomicCoefficientTests S row)
    (atomicCoefficientTests_bddAbove S row) T (div_pos hρ0 (by norm_num))
    (by linarith : 0 ≤ S + 1) hbound hiid'
  have hpenalty : ((S + 1) / (ρ / 2)) *
      (2 * Real.exp (-(δ ^ 2 * (m : ℝ) / S))) ≤ η := by
    have htailη' : (8 * S / ρ) * Real.exp (-(δ ^ 2 * (m : ℝ) / S)) ≤ η := htailη
    apply le_trans ?_ htailη'
    have he := Real.exp_nonneg (-(δ ^ 2 * (m : ℝ) / S))
    have hs : S + 1 ≤ 2 * S := by linarith
    calc
      _ ≤ ((2 * S) / (ρ / 2)) *
          (2 * Real.exp (-(δ ^ 2 * (m : ℝ) / S))) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hs (by positivity)) (by positivity)
      _ = _ := by
        have hf : (2 * S) / (ρ / 2) * 2 = 8 * S / ρ := by
          field_simp
          ring
        calc
          _ = ((2 * S) / (ρ / 2) * 2) *
              Real.exp (-(δ ^ 2 * (m : ℝ) / S)) := by ring
          _ = _ := by rw [hf]
  apply (sub_le_sub_left hpenalty 1).trans (hprob.trans _)
  apply probability_mono
  intro Ω hΩ
  have hmreal : sampleMean (atomicRowGram row) Ω =
      (m : ℝ)⁻¹ • ∑ k ∈ Ω.val, atomicRowGram row k := by
    simp only [sampleMean, sampleSum, ← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    rfl
  change atomicGramDeviation S row (sampleMean (atomicRowGram row) Ω) ≤ ρ
  rw [atomicGramDeviation, hmreal]
  change restrictedAbsoluteSup (atomicCoefficientTests S row)
    ((m : ℝ)⁻¹ • ∑ k ∈ Ω.val, atomicRowGram row k - mean (atomicRowGram row)) ≤
      2 * (ρ / 2) at hΩ
  convert hΩ using 1
  ring

end

end LeanNumDetect.FiniteMatrixSampling
