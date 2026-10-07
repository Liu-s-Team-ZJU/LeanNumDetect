import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Small positive test scales distinguish natural power orders. This is
the elementary final step in sharpness proofs using collapsing node families. -/

set_option autoImplicit false

namespace LeanNumDetect.PowerOrderSharpness

/-- The same comparison for arbitrary real exponents, needed to exclude
fractional improvements of a claimed sharp natural exponent. -/
theorem exists_small_scale_strict_rpow_bound {p q : ℝ} (hpq : p < q)
    {B c τ : ℝ} (hB : 0 < B) (hc : 0 < c) (hτ : 0 < τ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ τ ∧ B * t ^ q < c * t ^ p := by
  let a := c / (2 * B)
  have ha : 0 < a := by dsimp [a]; positivity
  have he : 0 < q - p := sub_pos.mpr hpq
  let T := a ^ (q - p)⁻¹
  have hT : 0 < T := Real.rpow_pos_of_pos ha _
  let t := min τ T
  have ht : 0 < t := lt_min hτ hT
  have hpow : t ^ (q - p) ≤ a := by
    have h := Real.rpow_le_rpow ht.le (min_le_right τ T) he.le
    simpa only [T, Real.rpow_inv_rpow ha.le he.ne'] using h
  have hBt : B * t ^ (q - p) ≤ c / 2 := by
    have h := mul_le_mul_of_nonneg_left hpow hB.le
    dsimp [a] at h
    have heq : B * (c / (2 * B)) = c / 2 := by field_simp
    rwa [heq] at h
  have hsplit : t ^ q = t ^ (q - p) * t ^ p := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  refine ⟨t, ht, min_le_left _ _, ?_⟩
  rw [hsplit]
  calc
    B * (t ^ (q - p) * t ^ p) = (B * t ^ (q - p)) * t ^ p := by ring
    _ ≤ (c / 2) * t ^ p := mul_le_mul_of_nonneg_right hBt (Real.rpow_pos_of_pos ht _).le
    _ < c * t ^ p := mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos ht _)

/-- At an arbitrarily small positive scale, a higher power is smaller than
any prescribed positive multiple of a lower power. -/
theorem exists_small_scale_strict_power_bound {p q : ℕ} (hpq : p < q)
    {B c τ : ℝ} (hB : 0 < B) (hc : 0 < c) (hτ : 0 < τ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ τ ∧ B * t ^ q < c * t ^ p := by
  let t := min 1 (min τ (c / (2 * B)))
  have ht : 0 < t := lt_min (by norm_num) (lt_min hτ (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htτ : t ≤ τ := (min_le_right _ _).trans (min_le_left _ _)
  have htc : t ≤ c / (2 * B) := (min_le_right _ _).trans (min_le_right _ _)
  have hBt : B * t ≤ c / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * B)).1 htc
    nlinarith
  have hpow : t ^ q ≤ t ^ (p + 1) :=
    pow_le_pow_of_le_one ht.le ht1 (by omega)
  refine ⟨t, ht, htτ, ?_⟩
  calc
    B * t ^ q ≤ B * t ^ (p + 1) := mul_le_mul_of_nonneg_left hpow hB.le
    _ = (B * t) * t ^ p := by ring
    _ ≤ (c / 2) * t ^ p := mul_le_mul_of_nonneg_right hBt (by positivity)
    _ < c * t ^ p := mul_lt_mul_of_pos_right (by linarith) (pow_pos ht _)

/-- A family with a higher-power upper bound cannot have a positive uniform
lower bound with a smaller exponent on a punctured interval. -/
theorem not_uniform_lower_power {p q : ℕ} (hpq : p < q)
    {B τ : ℝ} (hB : 0 < B) (hτ : 0 < τ) (f : ℝ → ℝ)
    (hupper : ∀ t, 0 < t → t ≤ τ → f t ≤ B * t ^ q) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ t, 0 < t → t ≤ τ → c * t ^ p ≤ f t := by
  rintro ⟨c, hc, hlower⟩
  obtain ⟨t, ht, htτ, hlt⟩ := exists_small_scale_strict_power_bound hpq hB hc hτ
  exact (not_lt_of_ge ((hlower t ht htτ).trans (hupper t ht htτ))) hlt

end LeanNumDetect.PowerOrderSharpness
