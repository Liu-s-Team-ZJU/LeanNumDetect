import MultiTuran.Turan.SpectralCentering

/-! Exact logarithmic-derivative identities connecting actual prunings with
centered exponential sums and their entire complex extensions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The real derivative of an imaginary exponential sum is exactly the
complex derivative of its entire extension restricted to the real line. -/
theorem deriv_exponentialSum_eq_complex_deriv_imaginary {n : ℕ}
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) (t : ℝ) :
    deriv (ExponentialSumEstimates.exponentialSum frequency c) t =
      deriv (complexExponentialSum (imaginaryExponents frequency) c) (t : ℂ) := by
  have h := (differentiable_complexExponentialSum (imaginaryExponents frequency) c
    (t : ℂ)).hasDerivAt.comp_ofReal
  have he : (fun s : ℝ => complexExponentialSum (imaginaryExponents frequency) c (s : ℂ)) =
      ExponentialSumEstimates.exponentialSum frequency c :=
    funext (complexExponentialSum_imaginary frequency c)
  rw [he] at h
  exact h.deriv

/-- Differentiating the actual demodulated sum factors out its unit phase. -/
theorem deriv_exponentialSum_frequency_sub {n : ℕ}
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) (a t : ℝ) :
    deriv (ExponentialSumEstimates.exponentialSum (fun j => frequency j-a) c) t =
      Complex.exp (Complex.I*((-t*a : ℝ) : ℂ)) *
        (deriv (ExponentialSumEstimates.exponentialSum frequency c) t -
          (Complex.I*(a : ℂ))*ExponentialSumEstimates.exponentialSum frequency c t) := by
  let phase : ℝ → ℂ := fun s => Complex.exp (Complex.I*((s*(-a) : ℝ) : ℂ))
  have hphase : HasDerivAt phase (phase t*(Complex.I*((-a : ℝ) : ℂ))) t := by
    have heone : ExponentialSumEstimates.exponentialSum (fun _ : Fin 1 => -a) (fun _ => (1:ℂ)) = phase := by
      funext s
      simp only [ExponentialSumEstimates.exponentialSum,Fin.sum_univ_one,one_mul,phase]
    have h := ExponentialSumEstimates.hasDerivAt_exponentialSum
      (fun _ : Fin 1 => -a) (fun _ => (1:ℂ)) t
    rw [heone] at h
    simpa only [Fin.sum_univ_one,one_mul,phase] using h
  have hP := (ExponentialSumEstimates.differentiable_exponentialSum frequency c t).hasDerivAt
  have hprod := hphase.mul hP
  have he : ExponentialSumEstimates.exponentialSum (fun j => frequency j-a) c =
      (fun s => phase s*ExponentialSumEstimates.exponentialSum frequency c s) := by
    funext s
    rw [exponentialSum_frequency_sub]
    dsimp [phase]
    congr 2
    push_cast
    ring
  change HasDerivAt (fun s => phase s*ExponentialSumEstimates.exponentialSum frequency c s) _ _ at hprod
  rw [← he] at hprod
  rw [hprod.deriv]
  have ht : phase t = Complex.exp (Complex.I*((-t*a : ℝ) : ℂ)) := by
    dsimp [phase]
    congr 2
    ring
  rw [ht,Complex.ofReal_neg]
  ring

/-- The logarithmic derivative is unchanged by the common phase except for
the selected frequency. This identity remains valid at zeros via field division. -/
theorem logarithmicDerivative_frequency_sub {n : ℕ}
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) (a t : ℝ) :
    deriv (ExponentialSumEstimates.exponentialSum (fun j => frequency j-a) c) t /
      ExponentialSumEstimates.exponentialSum (fun j => frequency j-a) c t =
    (deriv (ExponentialSumEstimates.exponentialSum frequency c) t -
      (Complex.I*(a : ℂ))*ExponentialSumEstimates.exponentialSum frequency c t) /
        ExponentialSumEstimates.exponentialSum frequency c t := by
  rw [deriv_exponentialSum_frequency_sub,exponentialSum_frequency_sub]
  exact mul_div_mul_left _ _ (Complex.exp_ne_zero _)

/-- The normalized pruning quotient is exactly the logarithmic derivative of
the centered entire sum, divided by the actual spectral scale. -/
theorem pruned_quotient_eq_centered_complex_logarithmicDerivative {n : ℕ}
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) (a : Fin n) (ρ t : ℝ) :
    prunedExponentialSum frequency c a ρ t /
      ExponentialSumEstimates.exponentialSum frequency c t =
    (deriv (complexExponentialSum
        (imaginaryExponents (fun j => frequency j-frequency a)) c) (t : ℂ) /
      complexExponentialSum (imaginaryExponents (fun j => frequency j-frequency a)) c (t : ℂ)) /
        (ρ : ℂ) := by
  rw [complexExponentialSum_imaginary,← deriv_exponentialSum_eq_complex_deriv_imaginary,
    logarithmicDerivative_frequency_sub]
  unfold prunedExponentialSum
  ring

/-- The exact scalar norm relation used to rescale the weak logarithmic
 derivative threshold from `uρ` to `u`. -/
theorem norm_pruned_quotient_eq {n : ℕ} (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    (a : Fin n) {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    ‖prunedExponentialSum frequency c a ρ t /
        ExponentialSumEstimates.exponentialSum frequency c t‖ =
      ‖deriv (complexExponentialSum
          (imaginaryExponents (fun j => frequency j-frequency a)) c) (t : ℂ) /
        complexExponentialSum (imaginaryExponents (fun j => frequency j-frequency a)) c (t : ℂ)‖ / ρ := by
  rw [pruned_quotient_eq_centered_complex_logarithmicDerivative,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hρ]

end
end LeanNumDetect.MultiTuran
