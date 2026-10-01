import General.Probability.BoundedAtomicRows
import RandSamp.OffGridAtomicRepresentation

/-!
# From a finite dictionary event to every admissible off-grid Gram estimate

The dictionary event is independent of the off-grid tuple. Exact expansions
place each normalized full Fourier signal in the bounded coefficient class,
so the same event gives a relative Gram estimate for every tuple satisfying
the stated full-Gram lower bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open WithLp
open scoped BigOperators

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The unnormalized finite Fourier dictionary, indexed by frequency rows. -/
def rawFourierGridRow (M : ℕ) (k : Fin (M + 1))
    (j : Fin (fourierAtomicGridSize M)) : ℂ := fourierAtomicGrid M j k

@[simp] theorem norm_rawFourierGridRow (M : ℕ) (k : Fin (M + 1))
    (j : Fin (fourierAtomicGridSize M)) : ‖rawFourierGridRow M k j‖ = 1 :=
  norm_fourierAtomicGrid M j k

theorem rawFourierGridRow_bound (M : ℕ) :
    ∀ k j, ‖rawFourierGridRow M k j‖ ≤ 1 := by simp

/-- The raw dictionary energy retains exactly the ambient dimension factor. -/
theorem rawFourierGridRow_energy_of_expansion (M : ℕ)
    (f : EuclideanSpace ℂ (Fin (M + 1))) (b : Fin (fourierAtomicGridSize M) → ℂ)
    (hb : f = ∑ j, b j • normalizedFourierGridAtom M j) (k : Fin (M + 1)) :
    atomicRowEnergy (rawFourierGridRow M) k (toLp 2 b) =
      ((M + 1 : ℕ) : ℝ) * ‖f k‖ ^ 2 := by
  have hk := congrArg (fun v : EuclideanSpace ℂ (Fin (M + 1)) => ofLp v k) hb
  simp only [ofLp_sum, ofLp_smul, normalizedFourierGridAtom,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk
  have hk' : f k = (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
      ∑ j, rawFourierGridRow M k j * b j := by
    rw [hk, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold rawFourierGridRow
    ring
  rw [hk']
  simp only [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg (M + 1)), atomicRowEnergy]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- The full dictionary average is exactly the squared full-signal norm. -/
theorem atomicMeanEnergy_rawFourierGrid_of_expansion (M : ℕ)
    (f : EuclideanSpace ℂ (Fin (M + 1))) (b : Fin (fourierAtomicGridSize M) → ℂ)
    (hb : f = ∑ j, b j • normalizedFourierGridAtom M j) :
    atomicMeanEnergy (rawFourierGridRow M) (toLp 2 b) = ‖f‖ ^ 2 := by
  unfold atomicMeanEnergy finiteAverage
  simp only [Fintype.card_fin, smul_eq_mul]
  simp_rw [rawFourierGridRow_energy_of_expansion M f b hb]
  rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

/-- Sampling raw dictionary energies gives exactly the sampled Fourier Gram
energy whenever its represented signal is the full Fourier signal. -/
theorem quadratic_rawFourierGrid_sample_of_expansion {M s m : ℕ}
    (Y : Fin s → ℝ) (z : EuclideanSpace ℂ (Fin s))
    (b : Fin (fourierAtomicGridSize M) → ℂ)
    (hb : fullFourierSignal M Y z = ∑ j, b j • normalizedFourierGridAtom M j)
    (Ω : Sample (M + 1) m) :
    FiniteMatrixSampling.quadratic (sampleMean (atomicRowGram (rawFourierGridRow M)) Ω)
      (toLp 2 b) =
      FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z := by
  rw [quadratic_atomicSampleMean]
  simp_rw [rawFourierGridRow_energy_of_expansion M (fullFourierSignal M Y z) b hb]
  rw [← Finset.mul_sum, ← sampled_fullFourierSignal_energy]
  simp only [div_eq_mul_inv]
  ring

/-- Exact unit-signal normalization puts its expansion in the coefficient
class with radius squared `4s/a`. -/
theorem normalized_expansion_mem_atomicCoefficientClass {M s : ℕ}
    (Y : Fin s → ℝ) (z : EuclideanSpace ℂ (Fin s)) {a : ℝ} (_ha : 0 < a)
    (b : Fin (fourierAtomicGridSize M) → ℂ)
    (hb : fullFourierSignal M Y z = ∑ j, b j • normalizedFourierGridAtom M j)
    (hm : (∑ j, ‖b j‖) ≤
      2 * Real.sqrt ((s : ℝ) / a) * ‖fullFourierSignal M Y z‖)
    (hf : fullFourierSignal M Y z ≠ 0) :
    ((‖fullFourierSignal M Y z‖⁻¹ : ℝ) : ℂ) • toLp 2 b ∈
      atomicCoefficientClass (4 * (s : ℝ) / a) (rawFourierGridRow M) := by
  have hn : 0 < ‖fullFourierSignal M Y z‖ := norm_pos_iff.mpr hf
  have hrad : Real.sqrt (4 * (s : ℝ) / a) = 2 * Real.sqrt ((s : ℝ) / a) := by
    rw [show 4 * (s : ℝ) / a = 4 * ((s : ℝ) / a) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  constructor
  · simp only [ofLp_smul, Pi.smul_apply, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
    rw [← Finset.mul_sum, hrad]
    have h := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hn.le)
    have he : ‖fullFourierSignal M Y z‖⁻¹ *
        (2 * Real.sqrt ((s : ℝ) / a) * ‖fullFourierSignal M Y z‖) =
        2 * Real.sqrt ((s : ℝ) / a) := by field_simp
    exact h.trans_eq he
  · rw [← quadratic_atomicMeanGram, quadratic_real_smul, quadratic_atomicMeanGram,
      atomicMeanEnergy_rawFourierGrid_of_expansion M (fullFourierSignal M Y z) b hb]
    have he : ‖fullFourierSignal M Y z‖⁻¹ ^ 2 * ‖fullFourierSignal M Y z‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hn.ne', one_pow]
    exact he.le

/-- A single finite-dictionary event controls an individual off-grid signal
with precisely the relative energy normalization. -/
theorem relativeGram_bounds_of_atomicGridDeviation {M s m : ℕ}
    (Y : Fin s → ℝ) (z : EuclideanSpace ℂ (Fin s)) {a ρ : ℝ} (ha : 0 < a)
    (Ω : Sample (M + 1) m)
    (hdev : atomicGramDeviation (4 * (s : ℝ) / a) (rawFourierGridRow M)
      (sampleMean (atomicRowGram (rawFourierGridRow M)) Ω) ≤ ρ)
    (hgram : a * ‖z‖ ^ 2 ≤ FiniteMatrixSampling.quadratic (fullGram M Y) z) :
    (1 - ρ) * FiniteMatrixSampling.quadratic (fullGram M Y) z ≤
      FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z ∧
    FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z ≤
      (1 + ρ) * FiniteMatrixSampling.quadratic (fullGram M Y) z := by
  by_cases hf : fullFourierSignal M Y z = 0
  · have he : FiniteMatrixSampling.quadratic (fullGram M Y) z = 0 := by
      rw [← norm_fullFourierSignal_sq, hf, norm_zero, zero_pow (by norm_num)]
    have hz : ‖z‖ = 0 := by
      rw [he] at hgram
      have hsq : ‖z‖ ^ 2 ≤ 0 :=
        le_of_mul_le_mul_left (by simpa only [mul_zero] using hgram) ha
      nlinarith [norm_nonneg z]
    have hz' : z = 0 := norm_eq_zero.mp hz
    subst z
    simp
  · obtain ⟨b, hb, hm⟩ := exists_fullFourierSignal_atomic_expansion_of_fullGram_lower Y z ha hgram
    let x : atomicCoefficientClass (4 * (s : ℝ) / a) (rawFourierGridRow M) :=
      ⟨((‖fullFourierSignal M Y z‖⁻¹ : ℝ) : ℂ) • toLp 2 b,
        normalized_expansion_mem_atomicCoefficientClass Y z ha b hb hm hf⟩
    have hp := (atomicGramDeviation_le_iff _ _ _ ρ).mp hdev x
    change |FiniteMatrixSampling.quadratic
        (sampleMean (atomicRowGram (rawFourierGridRow M)) Ω)
          (((‖fullFourierSignal M Y z‖⁻¹ : ℝ) : ℂ) • toLp 2 b) -
        atomicMeanEnergy (rawFourierGridRow M)
          (((‖fullFourierSignal M Y z‖⁻¹ : ℝ) : ℂ) • toLp 2 b)| ≤ ρ at hp
    rw [quadratic_real_smul, ← quadratic_atomicMeanGram, quadratic_real_smul,
      quadratic_atomicMeanGram,
      atomicMeanEnergy_rawFourierGrid_of_expansion M (fullFourierSignal M Y z) b hb,
      quadratic_rawFourierGrid_sample_of_expansion Y z b hb Ω] at hp
    have hn : ‖fullFourierSignal M Y z‖ ≠ 0 := (norm_pos_iff.mpr hf).ne'
    have hscale : ‖fullFourierSignal M Y z‖⁻¹ ^ 2 * ‖fullFourierSignal M Y z‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hn, one_pow]
    have hp' := mul_le_mul_of_nonneg_right hp (sq_nonneg ‖fullFourierSignal M Y z‖)
    have he :
        (‖fullFourierSignal M Y z‖⁻¹ ^ 2 *
          FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z -
          ‖fullFourierSignal M Y z‖⁻¹ ^ 2 * ‖fullFourierSignal M Y z‖ ^ 2) *
          ‖fullFourierSignal M Y z‖ ^ 2 =
        FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z -
          ‖fullFourierSignal M Y z‖ ^ 2 := by
      calc
        _ = (‖fullFourierSignal M Y z‖⁻¹ ^ 2 * ‖fullFourierSignal M Y z‖ ^ 2) *
            (FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z -
              ‖fullFourierSignal M Y z‖ ^ 2) := by ring
        _ = _ := by rw [hscale, one_mul]
    have hpm :
        |(‖fullFourierSignal M Y z‖⁻¹ ^ 2 *
          FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z -
          ‖fullFourierSignal M Y z‖⁻¹ ^ 2 * ‖fullFourierSignal M Y z‖ ^ 2) *
          ‖fullFourierSignal M Y z‖ ^ 2| ≤ ρ * ‖fullFourierSignal M Y z‖ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖fullFourierSignal M Y z‖)]
      exact hp'
    rw [he] at hpm
    apply relativeGram_of_fullFourierSignal_deviation Y z Ω ρ
    rw [sampled_fullFourierSignal_energy]
    exact hpm

/-- The finite-dictionary event implies the off-grid event for every node
tuple whose full Gram matrix has lower endpoint `a > 0`. -/
theorem relativeGramEvent_of_atomicGridDeviation {M s m : ℕ}
    (Y : Fin s → ℝ) {a ρ : ℝ} (ha : 0 < a) (Ω : Sample (M + 1) m)
    (hdev : atomicGramDeviation (4 * (s : ℝ) / a) (rawFourierGridRow M)
      (sampleMean (atomicRowGram (rawFourierGridRow M)) Ω) ≤ ρ)
    (hgram : ∀ z : EuclideanSpace ℂ (Fin s),
      a * ‖z‖ ^ 2 ≤ FiniteMatrixSampling.quadratic (fullGram M Y) z) :
    RelativeGramEvent Y ρ Ω := by
  intro z
  exact relativeGram_bounds_of_atomicGridDeviation Y z ha Ω hdev (hgram z)

end

end LeanNumDetect.RandSamp
