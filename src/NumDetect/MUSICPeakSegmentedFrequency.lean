import NumDetect.Matrices

set_option autoImplicit false

open WithLp
open scoped InnerProductSpace

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Cauchy--Schwarz for the real Fourier phase. -/
theorem abs_dot_le_euclidean_norm_mul
    {d : ℕ} (x u : Point d) :
    |dot x u| ≤ ‖toLp 2 x‖ * ‖toLp 2 u‖ := by
  have heq : dot x u = ⟪toLp 2 x, toLp 2 u⟫_ℝ := by
    simp [dot, EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]
  rw [heq]
  exact abs_real_inner_le_norm _ _

/-- A Euclidean bound on every sampled frequency gives the directional phase
bound used by the normalized Fourier derivative estimates. -/
theorem fourierPhase_le_of_frequency_norm_le
    {d : ℕ} {ι : Type*} (frequency : ι → Point d)
    (Ω : ℝ) (hfreq : ∀ i, ‖toLp 2 (frequency i)‖ ≤ Ω)
    (u : Point d) (i : ι) :
    |dot (frequency i) u| ≤ Ω * ‖toLp 2 u‖ := by
  exact (abs_dot_le_euclidean_norm_mul (frequency i) u).trans
    (mul_le_mul_of_nonneg_right (hfreq i) (norm_nonneg _))

/-- A coordinate bound controls the Euclidean norm with the sharp square-root
dimension factor. -/
theorem norm_toLp_le_sqrt_card_mul_of_abs_le
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hx : ∀ i, |x i| ≤ B) :
    ‖toLp 2 x‖ ≤ Real.sqrt (Fintype.card ι : ℝ) * B := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hB)).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : ι, B ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
    _ = (Fintype.card ι : ℝ) * B ^ 2 := by simp

/-- Every segmented row frequency lies in the coordinate cube of radius
`rD+m`. -/
theorem segmentedFrequency_coordinate_le_cutoff
    {d m r D : ℕ} (α : SegmentedIndex d m r) (k : Fin d) :
    (segmentedFrequency d m r D α k : ℝ) ≤ segmentedCutoff m r D := by
  have hblock : ((α k).1 : ℕ) ≤ r := by omega
  have hoffset : ((α k).2 : ℕ) ≤ m := by omega
  have hmul := Nat.mul_le_mul_left D hblock
  have hnat : D * ((α k).1 : ℕ) + ((α k).2 : ℕ) ≤ r * D + m := by
    nlinarith
  change ((D * ((α k).1 : ℕ) + ((α k).2 : ℕ) : ℕ) : ℝ) ≤
    ((r * D + m : ℕ) : ℝ)
  exact_mod_cast hnat

/-- The maximum Euclidean norm of a segmented row frequency is bounded by
`√d (rD+m)`, as used in the peak-stability noise threshold. -/
theorem segmentedFrequency_euclidean_norm_le
    {d m r D : ℕ} (α : SegmentedIndex d m r) :
    ‖toLp 2 (segmentedFrequency d m r D α)‖ ≤
      Real.sqrt d * (segmentedCutoff m r D : ℝ) := by
  have h := norm_toLp_le_sqrt_card_mul_of_abs_le
    (segmentedFrequency d m r D α) (segmentedCutoff m r D : ℝ)
    (Nat.cast_nonneg _) (by
      intro k
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact segmentedFrequency_coordinate_le_cutoff α k)
  simpa only [Fintype.card_fin] using h

/-- Directional phases for the segmented array obey the manuscript's sharp
frequency scale `√d (rD+m)`. -/
theorem segmentedFrequency_phase_le
    {d m r D : ℕ} (α : SegmentedIndex d m r) (u : Point d) :
    |dot (segmentedFrequency d m r D α) u| ≤
      (Real.sqrt d * (segmentedCutoff m r D : ℝ)) * ‖toLp 2 u‖ := by
  exact fourierPhase_le_of_frequency_norm_le
    (segmentedFrequency d m r D)
    (Real.sqrt d * (segmentedCutoff m r D : ℝ))
    segmentedFrequency_euclidean_norm_le u α

theorem segmentedFrequency_phase_le_of_unit
    {d m r D : ℕ} (α : SegmentedIndex d m r) (u : Point d)
    (hu : ‖toLp 2 u‖ = 1) :
    |dot (segmentedFrequency d m r D α) u| ≤
      Real.sqrt d * (segmentedCutoff m r D : ℝ) := by
  simpa only [hu, mul_one] using segmentedFrequency_phase_le α u

/-- The manuscript's `d^(3/2)` radius condition is the mixed-third-derivative
condition with the segmented frequency norm `√d Ω`. -/
theorem segmented_peak_radius_condition
    (d : ℕ) (Ω ρ c : ℝ)
    (hρ : 8 * (d : ℝ) ^ (3 / 2 : ℝ) * Ω ^ 3 * ρ ≤ c ^ 2) :
    8 * (Real.sqrt d * Ω) ^ 3 * ρ ≤ c ^ 2 := by
  have hpow : Real.sqrt (d : ℝ) ^ 3 =
      (d : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg d)]
    congr 1
    ring
  calc
    8 * (Real.sqrt d * Ω) ^ 3 * ρ =
        8 * (d : ℝ) ^ (3 / 2 : ℝ) * Ω ^ 3 * ρ := by
      rw [mul_pow, hpow]
      ring
    _ ≤ c ^ 2 := hρ

/-- The manuscript's explicit noise threshold implies the abstract Hessian
smallness condition. -/
theorem segmented_peak_noise_condition
    (d : ℕ) (Ω c ε : ℝ)
    (hd : 0 < d) (hΩ : 0 < Ω)
    (hε : ε < c ^ 2 / (8 * d * Ω ^ 2)) :
    4 * (Real.sqrt d * Ω) ^ 2 * ε < c ^ 2 / 2 := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hdenom : 0 < 8 * (d : ℝ) * Ω ^ 2 := by positivity
  have hprod : ε * (8 * (d : ℝ) * Ω ^ 2) < c ^ 2 :=
    (lt_div_iff₀ hdenom).mp hε
  have heq : 4 * (Real.sqrt d * Ω) ^ 2 * ε =
      (ε * (8 * (d : ℝ) * Ω ^ 2)) / 2 := by
    rw [mul_pow, Real.sq_sqrt hdreal.le]
    ring
  rw [heq]
  linarith

end
end NumDetect
end LeanNumDetect
