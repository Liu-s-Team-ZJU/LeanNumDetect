import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic

/-!
# Explicit aperture scaling

These arithmetic facts give the floor, half-power, normalization, and
no-wrap steps in `cor:subrayleigh-scaled-product` and `lem:sv-md-array`.
-/

set_option autoImplicit false

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- At aperture at least twice the source count, decimation loses at most two. -/
theorem aperture_quotient_lower (N n : ℕ) (hn : 0 < n) (hN : 2 * n ≤ N) :
    (N : ℝ) / (2 * n) ≤ ((N / n : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnN : n ≤ N := by omega
  have hm : 1 ≤ N / n := Nat.div_pos hnN hn
  have hmR : (1 : ℝ) ≤ (N / n : ℕ) := by exact_mod_cast hm
  have hlt : (N : ℝ) < (n : ℝ) * ((N / n : ℕ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ N hn
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
  nlinarith

/-- The dimension half-power respects the explicit decimation estimate. -/
theorem aperture_half_power_lower (d N n : ℕ) (hn : 0 < n)
    (hN : 2 * n ≤ N) :
    ((N : ℝ) / (2 * n)) ^ ((d : ℝ) / 2) ≤
      (((N / n : ℕ) : ℝ)) ^ ((d : ℝ) / 2) :=
  Real.rpow_le_rpow (by positivity) (aperture_quotient_lower N n hn hN) (by positivity)

/-- Normalization of the uniform norming constant `η = 1 / 2`. -/
theorem half_norming_sqrt_normalization (n : ℝ) :
    Real.sqrt (1 / 2 : ℝ) / Real.sqrt n = 1 / Real.sqrt (2 * n) := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
    div_div, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- Both aperture factors can be replaced at once in the final lower bound. -/
theorem aperture_scaled_factors_lower (d N n : ℕ) (hn : 0 < n)
    (hN : 2 * n ≤ N) {θ : ℝ} (hθ : 0 ≤ θ) :
    ((N : ℝ) / (2 * n)) ^ ((d : ℝ) / 2) *
        ((N : ℝ) * θ / (2 * Real.pi * n)) ^ (n - 1) ≤
      (((N / n : ℕ) : ℝ)) ^ ((d : ℝ) / 2) *
        ((((N / n : ℕ) : ℝ)) * θ / Real.pi) ^ (n - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hquot := aperture_quotient_lower N n hn hN
  have hsep : (N : ℝ) * θ / (2 * Real.pi * n) ≤
      (((N / n : ℕ) : ℝ)) * θ / Real.pi := by
    calc
      _ = ((N : ℝ) / (2 * n)) * θ / Real.pi := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hquot hθ) Real.pi_pos.le
  exact mul_le_mul (aperture_half_power_lower d N n hn hN)
    (pow_le_pow_left₀ (by positivity) hsep (n - 1))
    (by positivity) (Real.rpow_nonneg (by positivity) _)

/-- The localization diameter and `n ≥ 4` guarantee no wrap after decimation. -/
theorem aperture_quotient_mul_diameter_le_pi (N n : ℕ) (hn : 4 ≤ n)
    {Ω D : ℝ} (hΩ : 0 < Ω) (hNΩ : (N : ℝ) ≤ Ω)
    (hD : D ≤ 4 * Real.pi / Ω) :
    (((N / n : ℕ) : ℝ)) * D ≤ Real.pi := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnFour : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hquot : (((N / n : ℕ) : ℝ)) ≤ Ω / n :=
    Nat.cast_div_le.trans (div_le_div_of_nonneg_right hNΩ hnR.le)
  calc
    _ ≤ (((N / n : ℕ) : ℝ)) * (4 * Real.pi / Ω) :=
      mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _)
    _ ≤ (Ω / n) * (4 * Real.pi / Ω) :=
      mul_le_mul_of_nonneg_right hquot (by positivity)
    _ = 4 * Real.pi / n := by field_simp
    _ ≤ Real.pi := (div_le_iff₀ hnR).2 (by nlinarith [Real.pi_pos])

end
end LeanNumDetect.MultiTuran
