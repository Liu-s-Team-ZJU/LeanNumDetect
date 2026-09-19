import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! The scalar frequency-quantization argument of NumDetect
`lem:freq_quantization`. In dimension one no signed recentering is necessary:
the nonnegative integer frequency works for either sign of the difference. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SegmentedVDM

theorem sin_quarter_chord {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ Real.pi / 4) :
    (2 * Real.sqrt 2 / Real.pi) * x ≤ Real.sin x := by
  let t := x / (Real.pi / 4)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := (div_le_one (by positivity)).2 hx'
  have h := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by constructor <;> positivity)
    (show Real.pi / 4 ∈ Set.Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos])
    (sub_nonneg.mpr ht1) ht (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero, Real.sin_pi_div_four] at h
  have he : t * (Real.pi / 4) = x := div_mul_cancel₀ _ (by positivity)
  rw [he] at h
  convert! h using 1
  all_goals
    dsimp [t] at *
    try field_simp
    ring

theorem exp_sub_one_norm_abs (x : ℝ) (hx : |x| ≤ Real.pi) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ = 2 * Real.sin (|x| / 2) := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsin : 0 ≤ Real.sin (|x| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg h] at hsin ⊢
    rw [abs_of_nonneg hsin]
  · have hn : x ≤ 0 := le_of_not_ge h
    rw [abs_of_nonpos hn, neg_div, Real.sin_neg] at hsin ⊢
    rw [abs_of_nonpos (by linarith : Real.sin (x / 2) ≤ 0)]

/-- The phase lower bound is evaluated before applying the sine chord; this
retains the factor √2 in the original proof. -/
theorem exp_sub_one_lower {x b : ℝ} (hb : 0 ≤ b) (hbπ : b ≤ Real.pi / 2)
    (hbx : b ≤ |x|) (hx : |x| ≤ Real.pi) :
    2 * Real.sqrt 2 / Real.pi * b ≤ ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ := by
  rw [exp_sub_one_norm_abs x hx]
  have hchord := sin_quarter_chord (by linarith : 0 ≤ b / 2) (by linarith)
  have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ b / 2)
    (by linarith : |x| / 2 ≤ Real.pi / 2) (by linarith : b / 2 ≤ |x| / 2)
  linarith

theorem floor_ge_half {t : ℝ} (ht : 2 ≤ t) : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one t
  have hfloor : (1 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by
    exact_mod_cast (show 1 ≤ ⌊t⌋₊ by exact Nat.le_floor (by norm_num; linarith))
  linarith

/-- Scalar version of the three frequency-quantization inequalities. -/
theorem scalar_frequency_quantization {D α u : ℝ}
    (hD : 0 < D) (hα : 0 < α) (hu : 0 < |u|)
    (huα : |u| ≤ 2 * Real.pi * α) (hαD : α ≤ 1 / (4 * D)) :
    ∃ k : ℕ, (k : ℝ) ≤ 1 / (2 * D * α) ∧
      |u| / (4 * α) ≤ D * |(k : ℝ) * u| ∧
      D * |(k : ℝ) * u| ≤ Real.pi ∧
      Real.sqrt 2 / (2 * Real.pi * α) * |u| ≤
        ‖1 - Complex.exp (Complex.I * ((D * k * u : ℝ) : ℂ))‖ := by
  let t := 1 / (2 * D * α)
  have h4 := (le_div_iff₀ (by positivity : 0 < 4 * D)).mp hαD
  have ht : 2 ≤ t := (le_div_iff₀ (by positivity : 0 < 2 * D * α)).2 (by nlinarith)
  let k := ⌊t⌋₊
  have hk : (k : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hkh : t / 2 ≤ (k : ℝ) := floor_ge_half ht
  have hphase : |D * k * u| = D * (k : ℝ) * |u| := by
    rw [abs_mul, abs_mul, abs_of_pos hD, abs_of_nonneg (Nat.cast_nonneg _)]
  have hscale : D * t * |u| = |u| / (2 * α) := by dsimp [t]; field_simp
  have hlo : |u| / (4 * α) ≤ |D * k * u| := by
    rw [hphase]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkh hD.le) hu.le
    have he : D * (t / 2) * |u| = |u| / (4 * α) := by
      dsimp [t]
      field_simp
      <;> ring
    rwa [he] at hh
  have hhi : |D * k * u| ≤ Real.pi := by
    rw [hphase]
    calc
      _ ≤ D * t * |u| := by gcongr
      _ = |u| / (2 * α) := hscale
      _ ≤ Real.pi := (div_le_iff₀ (by positivity)).2 (by nlinarith)
  have hbπ : |u| / (4 * α) ≤ Real.pi / 2 :=
    (div_le_iff₀ (by positivity)).2 (by nlinarith)
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · simpa only [abs_mul, abs_of_pos hD, mul_assoc] using hlo
  · simpa only [abs_mul, abs_of_pos hD, mul_assoc] using hhi
  · rw [norm_sub_rev]
    have h := exp_sub_one_lower (by positivity : 0 ≤ |u| / (4 * α)) hbπ hlo hhi
    convert! h using 1
    field_simp
    <;> ring

end SegmentedVDM
