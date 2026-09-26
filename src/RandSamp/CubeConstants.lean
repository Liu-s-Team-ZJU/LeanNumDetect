import RandSamp.SeparatedGramBounds

/-! Explicit constants and positive separation thresholds for a Fourier cube.
The dimension dependence is the one in the RandSamp manuscript. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect.RandSamp

noncomputable section

/-- Normalized lower full-Gram bound for a `d`-dimensional frequency cube. -/
def cubeSeparatedLower (d M : ℕ) (Δ : ℝ) : ℝ :=
  ((M : ℝ) + 2 * Real.pi / Δ) ^ (d - 1) *
    ((M : ℝ) - (2 * (d : ℝ) - 1) * (2 * Real.pi / Δ)) / ((M : ℝ) + 1) ^ d

/-- Normalized upper full-Gram bound for a `d`-dimensional frequency cube. -/
def cubeSeparatedUpper (d M : ℕ) (Δ : ℝ) : ℝ :=
  ((M : ℝ) + 2 * Real.pi / Δ) ^ d / ((M : ℝ) + 1) ^ d

theorem cube_separation_pos {d M : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M) {Δ : ℝ}
    (hΔ : 2 * Real.pi * (2 * (d : ℝ) - 1) / M < Δ) : 0 < Δ := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hfactor : 0 < 2 * (d : ℝ) - 1 := by linarith
  exact (by positivity : 0 < 2 * Real.pi * (2 * (d : ℝ) - 1) / M).trans hΔ

theorem cube_separation_width {d M : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M) {Δ : ℝ}
    (hΔ : 2 * Real.pi * (2 * (d : ℝ) - 1) / M < Δ) :
    2 * Real.pi ≤ Δ * M := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hwidth := (div_lt_iff₀ hMr).1 hΔ
  have hfactor : 1 ≤ 2 * (d : ℝ) - 1 := by linarith
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have h := mul_le_mul_of_nonneg_left hfactor hπ
  linarith

theorem cubeSeparatedLower_pos {d M : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M) {Δ : ℝ}
    (hΔ : 2 * Real.pi * (2 * (d : ℝ) - 1) / M < Δ) :
    0 < cubeSeparatedLower d M Δ := by
  have hΔpos := cube_separation_pos hd hM hΔ
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hgap : (2 * (d : ℝ) - 1) * (2 * Real.pi / Δ) < M := by
    rw [← mul_div_assoc, div_lt_iff₀ hΔpos]
    have h := (div_lt_iff₀ hMr).1 hΔ
    nlinarith
  unfold cubeSeparatedLower
  exact div_pos (mul_pos (pow_pos (by positivity) _) (sub_pos.mpr hgap)) (by positivity)

theorem cubeSeparatedLower_le_upper {d M : ℕ} (hd : 1 ≤ d) {Δ : ℝ}
    (hΔ : 0 < Δ) : cubeSeparatedLower d M Δ ≤ cubeSeparatedUpper d M Δ := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hc : 0 ≤ 2 * Real.pi / Δ := by positivity
  have hbase : 0 ≤ (M : ℝ) + 2 * Real.pi / Δ := by positivity
  have hfactor : 0 ≤ 2 * (d : ℝ) - 1 := by linarith
  have hcoeff : (M : ℝ) - (2 * (d : ℝ) - 1) * (2 * Real.pi / Δ) ≤
      M + 2 * Real.pi / Δ := by nlinarith
  unfold cubeSeparatedLower cubeSeparatedUpper
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ((M : ℝ) + 2 * Real.pi / Δ) ^ (d - 1) * (M + 2 * Real.pi / Δ) :=
      mul_le_mul_of_nonneg_left hcoeff (pow_nonneg hbase _)
    _ = ((M : ℝ) + 2 * Real.pi / Δ) ^ d := by
      rw [← pow_succ, Nat.sub_add_cancel hd]

/-- The high-dimensional constants specialize exactly to the one-dimensional
constants, not just to weaker estimates. -/
@[simp] theorem cubeSeparatedLower_one (M : ℕ) (Δ : ℝ) :
    cubeSeparatedLower 1 M Δ = separatedLower M Δ := by
  norm_num [cubeSeparatedLower, separatedLower]

@[simp] theorem cubeSeparatedUpper_one (M : ℕ) (Δ : ℝ) :
    cubeSeparatedUpper 1 M Δ = separatedUpper M Δ := by
  simp [cubeSeparatedUpper, separatedUpper]

theorem cubeSeparated_lower_bound_pos {d M : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M)
    {Δ δ : ℝ} (hΔ : 2 * Real.pi * (2 * (d : ℝ) - 1) / M < Δ)
    (hδ : δ < 1) : 0 < Real.sqrt ((1 - δ) * cubeSeparatedLower d M Δ) :=
  Real.sqrt_pos.mpr (mul_pos (sub_pos.mpr hδ) (cubeSeparatedLower_pos hd hM hΔ))

end

end LeanNumDetect.RandSamp
