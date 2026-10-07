import General.Probability.AtomicPrefixEntropy

/-! Explicit logarithmic parameters for the causal shell construction.
These bounds retain the squared source logarithm and do not introduce a
dimension-dependent or sample-dependent absolute constant. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace LeanNumDetect.BoundedRieszConcentration

noncomputable def shellLevelCount (p δ : ℝ) : ℕ := ⌈Real.log (p / δ)⌉₊ + 1
noncomputable def shellWordBaseLength (p δ : ℝ) : ℕ := ⌈8192 * Real.log (p / δ)⌉₊

theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)
  rw [Real.log_inv] at h
  linarith

theorem one_le_log_four : (1 : ℝ) ≤ Real.log 4 := by
  have h := half_le_log_two
  have he : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

theorem shell_log_lower {p δ : ℝ} (hδ : 0 < δ) (hpδ : 4 * δ ≤ p) :
    1 ≤ Real.log (p / δ) := by
  exact one_le_log_four.trans (Real.log_le_log (by norm_num)
    ((le_div_iff₀ hδ).mpr (by linarith)))

theorem shellLevelCount_pos (p δ : ℝ) : 0 < shellLevelCount p δ := by
  unfold shellLevelCount
  omega

theorem shellLevelCount_le_log {p δ : ℝ} (hδ : 0 < δ) (hpδ : 4 * δ ≤ p) :
    (shellLevelCount p δ : ℝ) ≤ 3 * Real.log (p / δ) := by
  have hl := shell_log_lower hδ hpδ
  have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.log (p / δ) by linarith)
  unfold shellLevelCount
  push_cast
  linarith

theorem shellWordBaseLength_pos {p δ : ℝ} (hδ : 0 < δ) (hpδ : 4 * δ ≤ p) :
    0 < shellWordBaseLength p δ := by
  exact Nat.ceil_pos.mpr (by have h := shell_log_lower hδ hpδ; linarith)

theorem shellWordBaseLength_bounds {p δ : ℝ} (hδ : 0 < δ) (hpδ : 4 * δ ≤ p) :
    8192 * Real.log (p / δ) ≤ (shellWordBaseLength p δ : ℝ) ∧
      (shellWordBaseLength p δ : ℝ) ≤ 8193 * Real.log (p / δ) := by
  have hl := shell_log_lower hδ hpδ
  constructor
  · exact Nat.le_ceil _
  · have hc := Nat.ceil_lt_add_one (show 0 ≤ 8192 * Real.log (p / δ) by linarith)
    change (⌈8192 * Real.log (p / δ)⌉₊ : ℝ) ≤ _
    linarith

theorem shell_last_radius_sq_le {p δ : ℝ} (hδ : 0 < δ) (hpδ : 4 * δ ≤ p) :
    p / (4 : ℝ) ^ (shellLevelCount p δ - 1) ≤ δ := by
  have hp : 0 < p := by linarith
  have hr : 0 < p / δ := div_pos hp hδ
  have hl := shell_log_lower hδ hpδ
  have hk := Nat.le_ceil (Real.log (p / δ))
  have hk0 : 0 ≤ (⌈Real.log (p / δ)⌉₊ : ℝ) := Nat.cast_nonneg _
  have hlog : Real.log (p / δ) ≤ Real.log ((4 : ℝ) ^ ⌈Real.log (p / δ)⌉₊) := by
    rw [Real.log_pow]
    exact hk.trans (le_mul_of_one_le_right hk0 one_le_log_four)
  have hrpow := (Real.log_le_log_iff hr (by positivity)).mp hlog
  unfold shellLevelCount
  simp only [Nat.add_sub_cancel_right]
  apply (div_le_iff₀ (by positivity : 0 < (4 : ℝ) ^ ⌈Real.log (p / δ)⌉₊)).mpr
  have h := (div_le_iff₀ hδ).mp hrpow
  nlinarith

theorem shell_bad_budget_le {p δ m : ℝ} (hδ : 0 < δ) (hpδ : 4 * δ ≤ p)
    (hm : 0 ≤ m) :
    4 * p * m * (shellLevelCount p δ : ℝ) *
      Real.exp (-(shellWordBaseLength p δ : ℝ) / 512) ≤ δ * m := by
  have hp : 0 < p := by linarith
  let r := p / δ
  have hr : 0 < r := div_pos hp hδ
  have hr4 : 4 ≤ r := (le_div_iff₀ hδ).mpr (by linarith)
  have hl := shell_log_lower hδ hpδ
  have hlr : Real.log r ≤ r := Real.log_le_self hr.le
  have hell : (shellLevelCount p δ : ℝ) ≤ 3 * r :=
    (shellLevelCount_le_log hδ hpδ).trans (by dsimp [r] at hlr ⊢; linarith)
  have hbase := (shellWordBaseLength_bounds hδ hpδ).1
  have he : Real.exp (-(shellWordBaseLength p δ : ℝ) / 512) ≤ r⁻¹ ^ 16 := by
    calc
      _ ≤ Real.exp (-16 * Real.log r) := Real.exp_le_exp.mpr (by dsimp [r]; linarith)
      _ = r⁻¹ ^ 16 := by
        rw [show -16 * Real.log r = (16 : ℕ) * (-Real.log r) by norm_num]
        rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hr]
  have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  have hsmall : 12 * r ^ 2 * r⁻¹ ^ 16 ≤ 1 := by
    have hpow : 12 ≤ r ^ 14 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hr4 14
      norm_num at hh ⊢
      linarith
    have heq : r ^ 2 * r⁻¹ ^ 16 = (r ^ 14)⁻¹ := by
      field_simp
    rw [show 12 * r ^ 2 * r⁻¹ ^ 16 = 12 * (r ^ 2 * r⁻¹ ^ 16) by ring, heq]
    rw [← div_eq_mul_inv]
    exact (div_le_one (by positivity : 0 < r ^ 14)).mpr hpow
  have hpr : p = δ * r := by dsimp [r]; field_simp
  calc
    _ ≤ 4 * p * m * (3 * r) * (r⁻¹ ^ 16) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hell (by positivity)) he (by positivity) (by positivity)
    _ = δ * m * (12 * r ^ 2 * r⁻¹ ^ 16) := by rw [hpr]; ring
    _ ≤ δ * m := by simpa using mul_le_mul_of_nonneg_left hsmall (mul_nonneg hδ.le hm)

theorem shell_dimension_logs {N : ℕ} (hN : 0 < N) :
    1 ≤ Real.log (Real.exp 1 * (N : ℝ)) ∧
      Real.log (2 * (N : ℝ)) ≤ Real.log (Real.exp 1 * (N : ℝ)) ∧
      Real.log 2 ≤ Real.log (Real.exp 1 * (N : ℝ)) ∧
      Real.log (4 * (N : ℝ) + 1) ≤ 4 * Real.log (Real.exp 1 * (N : ℝ)) := by
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hn0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hn
  have htwo : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he : Real.log (Real.exp 1 * (N : ℝ)) = 1 + Real.log (N : ℝ) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hn0.ne', Real.log_exp]
  have ht : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log (N : ℝ) :=
    Real.log_mul (by norm_num) hn0.ne'
  have h8 : Real.log 8 ≤ 3 := by
    have hlog : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hbig := Real.log_le_log (by positivity : 0 < 4 * (N : ℝ) + 1)
    (show 4 * (N : ℝ) + 1 ≤ 8 * (N : ℝ) by linarith)
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hn0.ne'] at hbig
  rw [he]
  constructor
  · linarith
  constructor
  · rw [ht]; linarith
  constructor <;> linarith

theorem shell_total_budget_le {N : ℕ} (hN : 0 < N) {p δ : ℝ}
    (hδ : 0 < δ) (hpδ : 4 * δ ≤ p) :
    (shellLevelCount p δ : ℝ) * p *
      (16384 * Real.log (2 * (N : ℝ)) + 40960 * Real.log 2 +
        81920 * (shellWordBaseLength p δ : ℝ) * Real.log (4 * (N : ℝ) + 1)) ≤
      10000000000 * p * Real.log (Real.exp 1 * (N : ℝ)) * Real.log (p / δ) ^ 2 := by
  let a := Real.log (Real.exp 1 * (N : ℝ))
  let l := Real.log (p / δ)
  have hp : 0 ≤ p := by linarith
  have hl : 1 ≤ l := shell_log_lower hδ hpδ
  have ha : 1 ≤ a := (shell_dimension_logs hN).1
  have hell : (shellLevelCount p δ : ℝ) ≤ 3 * l := shellLevelCount_le_log hδ hpδ
  have hbase : (shellWordBaseLength p δ : ℝ) ≤ 8193 * l := (shellWordBaseLength_bounds hδ hpδ).2
  obtain ⟨_, ht, htwo, hbig⟩ := shell_dimension_logs hN
  have ht0 : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by
    have hn : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    linarith)
  have htwo0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hbig0 : 0 ≤ Real.log (4 * (N : ℝ) + 1) := Real.log_nonneg (by
    have hn := Nat.cast_nonneg (α := ℝ) N
    linarith)
  have hinner : 16384 * Real.log (2 * (N : ℝ)) + 40960 * Real.log 2 +
      81920 * (shellWordBaseLength p δ : ℝ) * Real.log (4 * (N : ℝ) + 1) ≤
      (57344 + 327680 * 8193) * a * l := by
    have hb0 : 0 ≤ (shellWordBaseLength p δ : ℝ) := Nat.cast_nonneg _
    have hprod := mul_le_mul hbase hbig
      (Real.log_nonneg (by have hn := Nat.cast_nonneg (α := ℝ) N; linarith))
      (by dsimp [l]; linarith : 0 ≤ 8193 * l)
    have hal : a ≤ a * l := le_mul_of_one_le_right (by linarith) hl
    dsimp [a, l] at *
    nlinarith
  calc
    _ ≤ (3 * l) * p * ((57344 + 327680 * 8193) * a * l) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hell hp) hinner
        (by positivity) (by positivity)
    _ = 8054218752 * p * a * l ^ 2 := by ring
    _ ≤ 10000000000 * p * a * l ^ 2 := by gcongr <;> norm_num

end LeanNumDetect.BoundedRieszConcentration
