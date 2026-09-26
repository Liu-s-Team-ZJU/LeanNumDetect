import RandSamp.CubeRandomModel
import RandSamp.CubeFullGram
import RandSamp.CubeConstants

/-! The normalized full-Gram bounds for a separated node set in any dimension. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open WithLp
open scoped BigOperators

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- Manuscript `eq:fixed-separated-higher-dimensional-full-gram`. The full
frequency cube has exactly `(M+1)^d` rows. -/
theorem cube_separated_full_gram_bounds {d M s : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M)
    {Δ : ℝ} (hΔlow : 2 * Real.pi * (2 * (d : ℝ) - 1) / M < Δ)
    (hΔhigh : Δ ≤ Real.pi) (Y : Fin s → Fin d → ℝ)
    (hsep : CubeAngularSeparated Δ Y) (z : EuclideanSpace ℂ (Fin s)) :
    cubeSeparatedLower d M Δ * ‖z‖ ^ 2 ≤
        FiniteMatrixSampling.quadratic (cubeFullGram M Y) z ∧
      FiniteMatrixSampling.quadratic (cubeFullGram M Y) z ≤
        cubeSeparatedUpper d M Δ * ‖z‖ ^ 2 := by
  have hΔ := cube_separation_pos hd hM hΔlow
  have hwidth := cube_separation_width hd hM hΔlow
  have hΔupper : Δ ≤ 2 * Real.pi := hΔhigh.trans (by linarith [Real.pi_pos])
  have he := cube_separated_full_energy_bounds hd (by omega) hΔ hΔupper hwidth
    Y hsep (ofLp z)
  have hmean : FiniteMatrixSampling.quadratic (cubeFullGram M Y) z =
      (((M : ℝ) + 1) ^ d)⁻¹ * cubeFullFourierEnergy M Y (ofLp z) := by
    rw [cubeFullGram, quadratic_cubeFourier_mean]
    rfl
  rw [hmean, EuclideanSpace.norm_sq_eq]
  have hN : 0 ≤ (((M : ℝ) + 1) ^ d)⁻¹ := by positivity
  constructor
  · calc
      cubeSeparatedLower d M Δ * (∑ j, ‖ofLp z j‖ ^ 2) =
          (((M : ℝ) + 1) ^ d)⁻¹ *
            ((((M : ℝ) + 2 * Real.pi / Δ) ^ (d - 1) *
              ((M : ℝ) - (2 * (d : ℝ) - 1) * (2 * Real.pi / Δ))) *
              (∑ j, ‖ofLp z j‖ ^ 2)) := by
        unfold cubeSeparatedLower
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he.1 hN
  · calc
      (((M : ℝ) + 1) ^ d)⁻¹ * cubeFullFourierEnergy M Y (ofLp z) ≤
          (((M : ℝ) + 1) ^ d)⁻¹ *
            (((M : ℝ) + 2 * Real.pi / Δ) ^ d * (∑ j, ‖ofLp z j‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left he.2 hN
      _ = cubeSeparatedUpper d M Δ * (∑ j, ‖ofLp z j‖ ^ 2) := by
        unfold cubeSeparatedUpper
        ring

end

end LeanNumDetect.RandSamp
