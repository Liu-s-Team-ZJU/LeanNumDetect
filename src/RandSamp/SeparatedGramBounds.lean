import RandSamp.RandomGram
import RandSamp.SeparatedFullGram

/-! Explicit normalized full-Gram bounds at angular Rayleigh separation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open WithLp
open scoped BigOperators

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

def separatedLower (M : ℕ) (Δ : ℝ) : ℝ :=
  ((M : ℝ) - 2 * Real.pi / Δ) / (M + 1)

def separatedUpper (M : ℕ) (Δ : ℝ) : ℝ :=
  ((M : ℝ) + 2 * Real.pi / Δ) / (M + 1)

theorem separatedLower_pos {M : ℕ} (hM : 0 < M) {Δ : ℝ}
    (hΔ : 2 * Real.pi / M < Δ) : 0 < separatedLower M Δ := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hΔpos : 0 < Δ := (by positivity : 0 < 2 * Real.pi / M).trans hΔ
  have hw : 2 * Real.pi / Δ < M := by
    apply (div_lt_iff₀ hΔpos).2
    simpa only [mul_comm] using (div_lt_iff₀ hMr).1 hΔ
  exact div_pos (sub_pos.mpr hw) (by positivity)

theorem separatedLower_le_upper (M : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) :
    separatedLower M Δ ≤ separatedUpper M Δ := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : 0 ≤ 2 * Real.pi / Δ := by positivity
  linarith

/-- Manuscript equation `eq:fixed-separated-full-gram`, in quadratic-form order.
The full population has `M+1` rows; the numerator has bandwidth `M`. -/
theorem separated_full_gram_bounds {M s : ℕ} (hM : 0 < M)
    (hs : 1 ≤ s) {Δ : ℝ} (hΔlow : 2 * Real.pi / M < Δ)
    (hΔhigh : Δ ≤ 2 * Real.pi / s)
    (Y : Fin s → ℝ) (hsep : AngularSeparated Δ Y)
    (z : EuclideanSpace ℂ (Fin s)) :
    separatedLower M Δ * ‖z‖ ^ 2 ≤
        FiniteMatrixSampling.quadratic (mean (fourierPopulation (N := M + 1) Y)) z ∧
      FiniteMatrixSampling.quadratic (mean (fourierPopulation (N := M + 1) Y)) z ≤
        separatedUpper M Δ * ‖z‖ ^ 2 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hΔ : 0 < Δ := (by positivity : 0 < 2 * Real.pi / M).trans hΔlow
  have hwidth : 2 * Real.pi ≤ Δ * M := ((div_lt_iff₀ hMr).1 hΔlow).le
  have hΔupper : Δ ≤ 2 * Real.pi := hΔhigh.trans
    (div_le_self (by positivity) hsr)
  have he := separated_full_energy_bounds hM hΔ hΔupper hwidth Y hsep (ofLp z)
  have hmean :
      FiniteMatrixSampling.quadratic (mean (fourierPopulation (N := M + 1) Y)) z =
        ((M + 1 : ℕ) : ℝ)⁻¹ * fullFourierEnergy M Y (ofLp z) := by
    rw [quadratic_fourier_mean]
    rfl
  rw [hmean, EuclideanSpace.norm_sq_eq]
  have hN : 0 ≤ ((M + 1 : ℕ) : ℝ)⁻¹ := by positivity
  constructor
  · calc
      separatedLower M Δ * (∑ j, ‖ofLp z j‖ ^ 2) =
          ((M + 1 : ℕ) : ℝ)⁻¹ *
            (((M : ℝ) - 2 * Real.pi / Δ) * (∑ j, ‖ofLp z j‖ ^ 2)) := by
        simp only [separatedLower, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he.1 hN
  · calc
      ((M + 1 : ℕ) : ℝ)⁻¹ * fullFourierEnergy M Y (ofLp z) ≤
          ((M + 1 : ℕ) : ℝ)⁻¹ *
            (((M : ℝ) + 2 * Real.pi / Δ) * (∑ j, ‖ofLp z j‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left he.2 hN
      _ = separatedUpper M Δ * (∑ j, ‖ofLp z j‖ ^ 2) := by
        simp only [separatedUpper, Nat.cast_add, Nat.cast_one]
        ring

end

end LeanNumDetect.RandSamp
