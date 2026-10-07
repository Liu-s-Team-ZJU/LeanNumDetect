import General.Fourier.PolynomialCrossCorrelation

/-! A separated angular pair can be distinguished by an integer frequency
within a prescribed bandwidth. This finite geometric-sum argument needs no
choice of principal angular representatives. -/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.SeparatedAngularFrequency
noncomputable section

/-- A unit complex number whose first powers remain close to one has a large
geometric sum. -/
theorem real_part_half_lt_of_chord_lt_one {z : ℂ} (hz : ‖z‖ = 1)
    (hchord : ‖z - 1‖ < 1) : (1 : ℝ) / 2 < z.re := by
  have heq : ‖z - 1‖ ^ 2 = 2 - 2 * z.re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq, hz]
    norm_num
  nlinarith [norm_nonneg (z - 1)]

/-- Winding separation at scale `η` and a bandwidth covering `2π/η` yield
an integer phase multiplier with chord at least one. -/
theorem exists_separated_integer_frequency (θ η : ℝ) (hη : 0 < η)
    (hsep : ∀ p : ℤ, η ≤ |θ - 2 * Real.pi * p|)
    (Q : ℕ) (hQ : 0 < Q) (hband : 2 * Real.pi ≤ (Q + 1 : ℝ) * η) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧
      1 ≤ ‖Complex.exp (Complex.I * (((q : ℝ) * θ : ℝ) : ℂ)) - 1‖ := by
  classical
  by_contra hex
  push Not at hex
  let f : Fin (Q + 1) → ℂ := fun k =>
    Complex.exp (Complex.I * (((k.val : ℝ) * θ : ℝ) : ℂ))
  have hchord (k : Fin (Q + 1)) : ‖f k - 1‖ < 1 := by
    by_cases hk : k.val = 0
    · simp [f, hk]
    · exact hex k.val (by omega) (by omega)
  have hre (k : Fin (Q + 1)) : (1 : ℝ) / 2 < (f k).re :=
    real_part_half_lt_of_chord_lt_one
      (Complex.norm_exp_I_mul_ofReal _) (hchord k)
  have hlarge : (Q + 1 : ℝ) / 2 < (∑ k, f k).re := by
    have hsum : (∑ k, f k).re = ∑ k, (f k).re :=
      map_sum Complex.reAddGroupHom f Finset.univ
    rw [hsum]
    have h := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty)
      (fun k (_ : k ∈ (Finset.univ : Finset (Fin (Q + 1)))) => hre k)
    simpa [div_eq_mul_inv] using h
  have hsmall : ‖∑ k, f k‖ ≤ Real.pi / η := by
    simpa [f] using
      PolynomialCrossCorrelation.fourier_normalized_monomial_norm_le θ η hη hsep Q hQ 0
  have hquot : Real.pi / η ≤ (Q + 1 : ℝ) / 2 := by
    apply (div_le_iff₀ hη).2
    nlinarith
  have hrele : (∑ k, f k).re ≤ ‖∑ k, f k‖ := Complex.re_le_norm _
  linarith

/-- A short angular representative gives a linear chord bound at a fixed
integer frequency; the chosen principal interval prevents phase aliasing. -/
theorem short_integer_frequency_chord_lower (Q : ℕ) (θ η : ℝ)
    (hgap : η ≤ |θ|) (hshort : |(Q : ℝ) * θ| ≤ Real.pi) :
    (2 / Real.pi) * (Q : ℝ) * η ≤
      ‖Complex.exp (Complex.I * (((Q : ℝ) * θ : ℝ) : ℂ)) - 1‖ := by
  have h := PolynomialCrossCorrelation.norm_exp_sub_one_lower hshort
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg Q)] at h
  calc
    (2 / Real.pi) * (Q : ℝ) * η ≤ (2 / Real.pi) * (Q : ℝ) * |θ| :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    _ = (2 / Real.pi) * ((Q : ℝ) * |θ|) := by ring
    _ ≤ _ := h

/-- Integer frequencies are invariant under changing a representative by
an integral number of turns. -/
theorem integer_frequency_phase_winding (Q : ℕ) (θ : ℝ) (p : ℤ) :
    Complex.exp (Complex.I * (((Q : ℝ) * (θ + 2 * Real.pi * p) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (((Q : ℝ) * θ : ℝ) : ℂ)) := by
  have he : Complex.I * (((Q : ℝ) * (θ + 2 * Real.pi * p) : ℝ) : ℂ) =
      Complex.I * (((Q : ℝ) * θ : ℝ) : ℂ) +
        ((Q : ℤ) * p : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end
end LeanNumDetect.SeparatedAngularFrequency
