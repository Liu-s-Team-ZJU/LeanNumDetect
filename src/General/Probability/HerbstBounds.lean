import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# A fully proved Herbst differential inequality

The apparent singularity of the normalized log moment at zero is removed
using the derivative there. The ordinary mean value theorem then integrates
an upper derivative bound; no concentration result is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology

namespace LeanNumDetect.HerbstBounds
noncomputable section

/-- The normalized log moment, extended by its derivative at zero. -/
def normalizedLogMoment (L : ℝ → ℝ) (p a : ℝ) (θ : ℝ) : ℝ :=
  (1 - p * θ) * Function.update (fun t => L t / t) 0 a θ

@[simp] theorem normalizedLogMoment_zero (L : ℝ → ℝ) (p a : ℝ) :
    normalizedLogMoment L p a 0 = a := by simp [normalizedLogMoment]

theorem normalizedLogMoment_of_ne_zero (L : ℝ → ℝ) (p a : ℝ)
    {θ : ℝ} (hθ : θ ≠ 0) :
    normalizedLogMoment L p a θ = (1 - p * θ) * (L θ / θ) := by
  simp only [normalizedLogMoment, Function.update_of_ne hθ]

/-- Differentiability of the original log moment removes the zero denominator. -/
theorem normalizedLogMoment_continuousAt_zero (L : ℝ → ℝ) (p a : ℝ)
    (hzero : L 0 = 0) (hderiv : HasDerivAt L a 0) :
    ContinuousAt (normalizedLogMoment L p a) 0 := by
  have hquotient : ContinuousAt (Function.update (fun t => L t / t) 0 a) 0 := by
    simpa only [hzero, sub_zero] using hderiv.continuousAt_div
  exact (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.mul hquotient

/-- Exact derivative of the normalized log moment away from zero. -/
theorem hasDerivAt_normalizedLogMoment (L : ℝ → ℝ) (p a : ℝ)
    {θ d : ℝ} (hθ : θ ≠ 0) (hderiv : HasDerivAt L d θ) :
    HasDerivAt (normalizedLogMoment L p a)
      ((θ * (1 - p * θ) * d - L θ) / θ ^ 2) θ := by
  have hraw : HasDerivAt (fun t : ℝ => (1 - p * t) * (L t / t))
      ((θ * (1 - p * θ) * d - L θ) / θ ^ 2) θ := by
    apply (((hasDerivAt_const θ (1 : ℝ)).sub
      ((hasDerivAt_id θ).const_mul p)).mul
      (hderiv.div (hasDerivAt_id θ) hθ)).congr_deriv
    dsimp only [Pi.div_apply, Pi.sub_apply, id_eq]
    field_simp [hθ]
    ring
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hθ] with t ht
  exact normalizedLogMoment_of_ne_zero L p a ht

/-- Integrate the Herbst inequality, retaining unrestricted real values of
both the initial derivative and the constant term. -/
theorem herbst_logMoment_bound (L d : ℝ → ℝ) {p a b : ℝ}
    (hp : 0 < p) (hzero : L 0 = 0) (hderiv0 : HasDerivAt L a 0)
    (hderiv : ∀ θ ∈ Ioo (0 : ℝ) (1 / p), HasDerivAt L (d θ) θ)
    (hdifferential : ∀ θ ∈ Ioo (0 : ℝ) (1 / p),
      θ * (1 - p * θ) * d θ - L θ ≤ b * θ ^ 2) :
    ∀ θ ∈ Ico (0 : ℝ) (1 / p),
      L θ ≤ θ * a + (p * a + b) * θ ^ 2 / (1 - p * θ) := by
  intro θ hθ
  by_cases hθ0 : θ = 0
  · simp [hθ0, hzero]
  have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
  let H := normalizedLogMoment L p a
  have hHderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (1 / p)) :
      HasDerivAt H ((t * (1 - p * t) * d t - L t) / t ^ 2) t :=
    hasDerivAt_normalizedLogMoment L p a ht.1.ne' (hderiv t ht)
  have hHbound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (1 / p)) :
      (t * (1 - p * t) * d t - L t) / t ^ 2 ≤ b :=
    (div_le_iff₀ (sq_pos_of_pos ht.1)).2 (hdifferential t ht)
  have hHcont : ContinuousOn H (Icc (0 : ℝ) θ) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      exact (normalizedLogMoment_continuousAt_zero L p a hzero hderiv0).continuousWithinAt
    · exact (hHderiv t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2.trans_lt hθ.2⟩).continuousAt.continuousWithinAt
  have hHdiff : DifferentiableOn ℝ H (Ioo (0 : ℝ) θ) := by
    intro t ht
    exact (hHderiv t ⟨ht.1, ht.2.trans hθ.2⟩).differentiableAt.differentiableWithinAt
  obtain ⟨t, ht, hslope⟩ := exists_deriv_eq_slope H hθpos hHcont hHdiff
  have hti : t ∈ Ioo (0 : ℝ) (1 / p) := ⟨ht.1, ht.2.trans hθ.2⟩
  rw [(hHderiv t hti).deriv] at hslope
  have hnormalized : H θ ≤ a + b * θ := by
    have h := hHbound t hti
    rw [hslope, sub_zero] at h
    have hh := (div_le_iff₀ hθpos).1 h
    simp only [H, normalizedLogMoment_zero] at hh
    linarith
  have hden : 0 < 1 - p * θ := by
    have h := (lt_div_iff₀ hp).1 hθ.2
    nlinarith
  have hproduct : (1 - p * θ) * L θ ≤ θ * (a + b * θ) := by
    have h := mul_le_mul_of_nonneg_right hnormalized hθpos.le
    dsimp only [H] at h
    rw [normalizedLogMoment_of_ne_zero L p a hθ0] at h
    have heq : (1 - p * θ) * (L θ / θ) * θ = (1 - p * θ) * L θ := by
      field_simp
    rw [heq] at h
    simpa only [mul_comm] using h
  have hbound : L θ ≤ θ * (a + b * θ) / (1 - p * θ) :=
    (le_div_iff₀ hden).2 (by simpa only [mul_comm] using hproduct)
  apply hbound.trans_eq
  have heq : θ * a * (1 - p * θ) + (p * a + b) * θ ^ 2 = θ * (a + b * θ) := by ring
  rw [← heq, add_div, mul_div_cancel_right₀ _ hden.ne']

/-- The centered form used directly in exponential-moment concentration. -/
theorem herbst_centered_logMoment_bound (L d : ℝ → ℝ) {p a b : ℝ}
    (hp : 0 < p) (hzero : L 0 = 0) (hderiv0 : HasDerivAt L a 0)
    (hderiv : ∀ θ ∈ Ioo (0 : ℝ) (1 / p), HasDerivAt L (d θ) θ)
    (hdifferential : ∀ θ ∈ Ioo (0 : ℝ) (1 / p),
      θ * (1 - p * θ) * d θ - L θ ≤ b * θ ^ 2) :
    ∀ θ ∈ Ico (0 : ℝ) (1 / p),
      L θ - θ * a ≤ (p * a + b) * θ ^ 2 / (1 - p * θ) := by
  intro θ hθ
  have h := herbst_logMoment_bound L d hp hzero hderiv0 hderiv hdifferential θ hθ
  linarith

end
end LeanNumDetect.HerbstBounds
