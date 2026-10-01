import NumDetect.MUSICPeakRegularity

set_option autoImplicit false

open WithLp

namespace LeanNumDetect
namespace NumDetect

noncomputable section

theorem norm_toLp_pointwise_mul_le
    {ι : Type*} [Fintype ι]
    (a v : ι → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ‖toLp 2 (fun i => a i * v i)‖ ≤ C * ‖toLp 2 v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
  calc
    ∑ i, ‖a i * v i‖ ^ 2 ≤ ∑ i, C ^ 2 * ‖v i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (ha i) 2) (sq_nonneg _)
    _ = C ^ 2 * ∑ i, ‖v i‖ ^ 2 := by rw [Finset.mul_sum]

theorem norm_fourier_directional_derivative_vector_le
    {d k : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (frequency : ι → Point d) (y u : Point d) (Ω : ℝ)
    (hΩ : 0 ≤ Ω)
    (hphase : ∀ i, |dot (frequency i) u| ≤ Ω) :
    ‖toLp 2 (fun i =>
      (Complex.I * (dot (frequency i) u : ℂ)) ^ k *
        normalizedSteering frequency y i)‖ ≤ Ω ^ k := by
  have ha (i : ι) :
      ‖(Complex.I * (dot (frequency i) u : ℂ)) ^ k‖ ≤ Ω ^ k := by
    rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    exact pow_le_pow_left₀ (abs_nonneg _) (hphase i) k
  have h := norm_toLp_pointwise_mul_le
    (fun i => (Complex.I * (dot (frequency i) u : ℂ)) ^ k)
    (normalizedSteering frequency y) (Ω ^ k) (pow_nonneg hΩ _) ha
  simpa only [norm_normalizedSteering, mul_one] using h

theorem norm_fourier_mixed_derivative_vector_le
    {d k : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (frequency : ι → Point d) (y : Point d)
    (u : Fin k → Point d) (Ω : Fin k → ℝ)
    (hΩ : ∀ j, 0 ≤ Ω j)
    (hphase : ∀ i j, |dot (frequency i) (u j)| ≤ Ω j) :
    ‖toLp 2 (fun i =>
      (∏ j, Complex.I * (dot (frequency i) (u j) : ℂ)) *
        normalizedSteering frequency y i)‖ ≤ ∏ j, Ω j := by
  have hΩprod : 0 ≤ ∏ j, Ω j :=
    Finset.prod_nonneg (by intro j _; exact hΩ j)
  have ha (i : ι) :
      ‖∏ j, Complex.I * (dot (frequency i) (u j) : ℂ)‖ ≤ ∏ j, Ω j := by
    rw [norm_prod]
    apply Finset.prod_le_prod
    · intro j _
      exact norm_nonneg _
    · intro j _
      simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
        using hphase i j
  have h := norm_toLp_pointwise_mul_le
    (fun i => ∏ j, Complex.I * (dot (frequency i) (u j) : ℂ))
    (normalizedSteering frequency y) (∏ j, Ω j) hΩprod ha
  simpa only [norm_normalizedSteering, mul_one] using h

end
end NumDetect
end LeanNumDetect
