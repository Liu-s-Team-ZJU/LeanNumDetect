import NumDetect.MUSICPeakRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped RealInnerProductSpace InnerProductSpace
namespace LeanNumDetect
namespace NumDetect
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E →L[ℝ] E) (x x₁ x₂ x₃ : ℝ → E)

private theorem projected_hasDerivAt
    {f g : ℝ → E} {t : ℝ} (h : HasDerivAt f (g t) t) :
    HasDerivAt (fun s => T (f s)) (T (g t)) t := by
  exact T.hasFDerivAt.comp_hasDerivAt t h

theorem projected_normSq_hasDerivAt
    {t : ℝ} (h : HasDerivAt x (x₁ t) t) :
    HasDerivAt (fun s => ‖T (x s)‖ ^ 2)
      (2 * ⟪T (x t), T (x₁ t)⟫_ℝ) t := by
  exact (projected_hasDerivAt T h).norm_sq

theorem projected_normSq_first_hasDerivAt
    {t : ℝ} (h₀ : HasDerivAt x (x₁ t) t)
    (h₁ : HasDerivAt x₁ (x₂ t) t) :
    HasDerivAt (fun s => 2 * ⟪T (x s), T (x₁ s)⟫_ℝ)
      (2 * ⟪T (x t), T (x₂ t)⟫_ℝ +
        2 * ⟪T (x₁ t), T (x₁ t)⟫_ℝ) t := by
  simpa only [mul_add] using
    (((projected_hasDerivAt T h₀).inner ℝ
      (projected_hasDerivAt T h₁)).const_mul 2)

theorem projected_normSq_second_hasDerivAt
    {t : ℝ} (h₀ : HasDerivAt x (x₁ t) t)
    (h₁ : HasDerivAt x₁ (x₂ t) t)
    (h₂ : HasDerivAt x₂ (x₃ t) t) :
    HasDerivAt (fun s =>
      2 * ⟪T (x s), T (x₂ s)⟫_ℝ +
        2 * ⟪T (x₁ s), T (x₁ s)⟫_ℝ)
      (2 * ⟪T (x t), T (x₃ t)⟫_ℝ +
        6 * ⟪T (x₁ t), T (x₂ t)⟫_ℝ) t := by
  have h := (((projected_hasDerivAt T h₀).inner ℝ
      (projected_hasDerivAt T h₂)).const_mul 2).add
    (((projected_hasDerivAt T h₁).inner ℝ
      (projected_hasDerivAt T h₁)).const_mul 2)
  change HasDerivAt
      ((fun s => 2 * ⟪T (x s), T (x₂ s)⟫_ℝ) +
        (fun s => 2 * ⟪T (x₁ s), T (x₁ s)⟫_ℝ))
      (2 * (⟪T (x t), T (x₃ t)⟫_ℝ +
        ⟪T (x₁ t), T (x₂ t)⟫_ℝ) +
        2 * (⟪T (x₁ t), T (x₂ t)⟫_ℝ +
        ⟪T (x₂ t), T (x₁ t)⟫_ℝ)) t at h
  have he :
      2 * (⟪T (x t), T (x₃ t)⟫_ℝ +
        ⟪T (x₁ t), T (x₂ t)⟫_ℝ) +
        2 * (⟪T (x₁ t), T (x₂ t)⟫_ℝ +
        ⟪T (x₂ t), T (x₁ t)⟫_ℝ) =
      2 * ⟪T (x t), T (x₃ t)⟫_ℝ +
        6 * ⟪T (x₁ t), T (x₂ t)⟫_ℝ := by
    rw [real_inner_comm (T (x₂ t)) (T (x₁ t))]
    ring
  rw [he] at h
  have hfun :
      ((fun s => 2 * ⟪T (x s), T (x₂ s)⟫_ℝ) +
        (fun s => 2 * ⟪T (x₁ s), T (x₁ s)⟫_ℝ)) =
      (fun s => 2 * ⟪T (x s), T (x₂ s)⟫_ℝ +
        2 * ⟪T (x₁ s), T (x₁ s)⟫_ℝ) := by
    funext s
    rfl
  rw [hfun] at h
  exact h

/-- The derivative of the Hessian in a possibly different direction. -/
theorem projected_mixed_third_hasDerivAt
    (xu xuu xv xuv xuuv : ℝ → E)
    {t : ℝ} (hv : HasDerivAt x (xv t) t)
    (huu : HasDerivAt xuu (xuuv t) t)
    (huv : HasDerivAt xu (xuv t) t) :
    HasDerivAt (fun s =>
      2 * ⟪T (x s), T (xuu s)⟫_ℝ +
        2 * ⟪T (xu s), T (xu s)⟫_ℝ)
      (2 * (⟪T (x t), T (xuuv t)⟫_ℝ +
        ⟪T (xv t), T (xuu t)⟫_ℝ) +
        2 * (⟪T (xu t), T (xuv t)⟫_ℝ +
        ⟪T (xuv t), T (xu t)⟫_ℝ)) t := by
  have h := (((projected_hasDerivAt T hv).inner ℝ
      (projected_hasDerivAt T huu)).const_mul 2).add
    (((projected_hasDerivAt T huv).inner ℝ
      (projected_hasDerivAt T huv)).const_mul 2)
  have hfun :
      ((fun s => 2 * ⟪T (x s), T (xuu s)⟫_ℝ) +
        (fun s => 2 * ⟪T (xu s), T (xu s)⟫_ℝ)) =
      (fun s => 2 * ⟪T (x s), T (xuu s)⟫_ℝ +
        2 * ⟪T (xu s), T (xu s)⟫_ℝ) := by
    funext s
    rfl
  rw [hfun] at h
  exact h

/-- Four projected Fourier derivative pairings give the mixed third-derivative bound. -/
theorem projected_mixed_third_abs_le
    (hT : ∀ z, ‖T z‖ ≤ ‖z‖)
    (Ω : ℝ) (hΩ : 0 ≤ Ω)
    (a au auu av auv auuv : E)
    (ha : ‖a‖ ≤ 1) (hau : ‖au‖ ≤ Ω)
    (hauu : ‖auu‖ ≤ Ω ^ 2) (hav : ‖av‖ ≤ Ω)
    (hauv : ‖auv‖ ≤ Ω ^ 2) (hauuv : ‖auuv‖ ≤ Ω ^ 3) :
    |2 * (⟪T a, T auuv⟫_ℝ + ⟪T av, T auu⟫_ℝ) +
      2 * (⟪T au, T auv⟫_ℝ + ⟪T auv, T au⟫_ℝ)| ≤
      8 * Ω ^ 3 := by
  have hpair (z w : E) (A B : ℝ) (hz : ‖z‖ ≤ A) (hw : ‖w‖ ≤ B)
      (hB : 0 ≤ B) :
      |⟪T z, T w⟫_ℝ| ≤ A * B := by
    calc
      |⟪T z, T w⟫_ℝ| ≤ ‖T z‖ * ‖T w‖ := abs_real_inner_le_norm _ _
      _ ≤ A * B := by
        exact mul_le_mul ((hT z).trans hz) ((hT w).trans hw)
          (norm_nonneg _) ((norm_nonneg z).trans hz)
  let A := ⟪T a, T auuv⟫_ℝ
  let B := ⟪T av, T auu⟫_ℝ
  let C := ⟪T au, T auv⟫_ℝ
  let D := ⟪T auv, T au⟫_ℝ
  have hA : |A| ≤ Ω ^ 3 := by
    simpa only [A, one_mul] using
      hpair a auuv 1 (Ω ^ 3) ha hauuv (pow_nonneg hΩ _)
  have hB : |B| ≤ Ω ^ 3 := by
    simpa only [B, show Ω * Ω ^ 2 = Ω ^ 3 by ring] using
      hpair av auu Ω (Ω ^ 2) hav hauu (sq_nonneg Ω)
  have hC : |C| ≤ Ω ^ 3 := by
    simpa only [C, show Ω * Ω ^ 2 = Ω ^ 3 by ring] using
      hpair au auv Ω (Ω ^ 2) hau hauv (sq_nonneg Ω)
  have hD : |D| ≤ Ω ^ 3 := by
    simpa only [D, show Ω ^ 2 * Ω = Ω ^ 3 by ring] using
      hpair auv au (Ω ^ 2) Ω hauv hau hΩ
  have h₁ : |A + B| ≤ |A| + |B| := abs_add_le A B
  have h₂ : |C + D| ≤ |C| + |D| := abs_add_le C D
  have h₃ : |2 * (A + B) + 2 * (C + D)| ≤
      |2 * (A + B)| + |2 * (C + D)| := abs_add_le _ _
  have h₄ : |2 * (A + B)| = 2 * |A + B| := by simp
  have h₅ : |2 * (C + D)| = 2 * |C + D| := by simp
  change |2 * (A + B) + 2 * (C + D)| ≤ 8 * Ω ^ 3
  rw [h₄, h₅] at h₃
  nlinarith

/-- The mixed bound keeps track of a shorter radial direction separately. -/
theorem projected_mixed_third_abs_le_twoRadii
    (hT : ∀ z, ‖T z‖ ≤ ‖z‖)
    (Ωu Ωv : ℝ) (hΩu : 0 ≤ Ωu) (hΩv : 0 ≤ Ωv)
    (a au auu av auv auuv : E)
    (ha : ‖a‖ ≤ 1) (hau : ‖au‖ ≤ Ωu)
    (hauu : ‖auu‖ ≤ Ωu ^ 2) (hav : ‖av‖ ≤ Ωv)
    (hauv : ‖auv‖ ≤ Ωu * Ωv)
    (hauuv : ‖auuv‖ ≤ Ωu ^ 2 * Ωv) :
    |2 * (⟪T a, T auuv⟫_ℝ + ⟪T av, T auu⟫_ℝ) +
      2 * (⟪T au, T auv⟫_ℝ + ⟪T auv, T au⟫_ℝ)| ≤
      8 * Ωu ^ 2 * Ωv := by
  have hpair (z w : E) (A B : ℝ) (hz : ‖z‖ ≤ A) (hw : ‖w‖ ≤ B) :
      |⟪T z, T w⟫_ℝ| ≤ A * B := by
    calc
      |⟪T z, T w⟫_ℝ| ≤ ‖T z‖ * ‖T w‖ := abs_real_inner_le_norm _ _
      _ ≤ A * B :=
        mul_le_mul ((hT z).trans hz) ((hT w).trans hw)
          (norm_nonneg _) ((norm_nonneg z).trans hz)
  let A := ⟪T a, T auuv⟫_ℝ
  let B := ⟪T av, T auu⟫_ℝ
  let C := ⟪T au, T auv⟫_ℝ
  let D := ⟪T auv, T au⟫_ℝ
  have hA : |A| ≤ Ωu ^ 2 * Ωv := by
    simpa only [A, one_mul] using
      hpair a auuv 1 (Ωu ^ 2 * Ωv) ha hauuv
  have hB : |B| ≤ Ωu ^ 2 * Ωv := by
    convert hpair av auu Ωv (Ωu ^ 2) hav hauu using 1 <;> ring
  have hC : |C| ≤ Ωu ^ 2 * Ωv := by
    convert hpair au auv Ωu (Ωu * Ωv) hau hauv using 1 <;> ring
  have hD : |D| ≤ Ωu ^ 2 * Ωv := by
    convert hpair auv au (Ωu * Ωv) Ωu hauv hau using 1 <;> ring
  have h₁ : |A + B| ≤ |A| + |B| := abs_add_le A B
  have h₂ : |C + D| ≤ |C| + |D| := abs_add_le C D
  have h₃ : |2 * (A + B) + 2 * (C + D)| ≤
      |2 * (A + B)| + |2 * (C + D)| := abs_add_le _ _
  have h₄ : |2 * (A + B)| = 2 * |A + B| := by simp
  have h₅ : |2 * (C + D)| = 2 * |C + D| := by simp
  change |2 * (A + B) + 2 * (C + D)| ≤ 8 * Ωu ^ 2 * Ωv
  rw [h₄, h₅] at h₃
  nlinarith

/-- A projected quadratic curvature has controlled radial derivative. -/
theorem projected_curvature_radial_deriv_abs_le
    (hT : ∀ z, ‖T z‖ ≤ ‖z‖)
    (xu xuu xv xuv xuuv : ℝ → E)
    (H : ℝ → ℝ) (Ωu Ωv : ℝ)
    (hΩu : 0 ≤ Ωu) (hΩv : 0 ≤ Ωv)
    (hH : H = fun s =>
      2 * ⟪T (x s), T (xuu s)⟫_ℝ +
        2 * ⟪T (xu s), T (xu s)⟫_ℝ)
    (hv : ∀ t, HasDerivAt x (xv t) t)
    (huu : ∀ t, HasDerivAt xuu (xuuv t) t)
    (huv : ∀ t, HasDerivAt xu (xuv t) t)
    (ha : ∀ t, ‖x t‖ ≤ 1)
    (hau : ∀ t, ‖xu t‖ ≤ Ωu)
    (hauu : ∀ t, ‖xuu t‖ ≤ Ωu ^ 2)
    (hav : ∀ t, ‖xv t‖ ≤ Ωv)
    (hauv : ∀ t, ‖xuv t‖ ≤ Ωu * Ωv)
    (hauuv : ∀ t, ‖xuuv t‖ ≤ Ωu ^ 2 * Ωv) :
    ∀ t, |deriv H t| ≤ 8 * Ωu ^ 2 * Ωv := by
  intro t
  rw [hH]
  have hder := projected_mixed_third_hasDerivAt T x xu xuu xv xuv xuuv
    (hv t) (huu t) (huv t)
  rw [hder.deriv]
  exact projected_mixed_third_abs_le_twoRadii T hT Ωu Ωv hΩu hΩv
    (x t) (xu t) (xuu t) (xv t) (xuv t) (xuuv t)
    (ha t) (hau t) (hauu t) (hav t) (hauv t) (hauuv t)

/-- A bound on projector difference controls the Hessian of the squared residual. -/
theorem projected_hessian_perturb_abs_le
    (D : E →L[ℝ] E) (p Ω : ℝ) (hp : 0 ≤ p) (hΩ : 0 ≤ Ω)
    (hD : ∀ z, ‖D z‖ ≤ p * ‖z‖)
    (a au auu : E) (ha : ‖a‖ ≤ 1)
    (hau : ‖au‖ ≤ Ω) (hauu : ‖auu‖ ≤ Ω ^ 2) :
    |2 * ⟪a, D auu⟫_ℝ + 2 * ⟪au, D au⟫_ℝ| ≤ 4 * p * Ω ^ 2 := by
  have hpair (z w : E) (A B : ℝ) (hz : ‖z‖ ≤ A) (hw : ‖w‖ ≤ B) :
      |⟪z, D w⟫_ℝ| ≤ A * (p * B) := by
    have hDw : ‖D w‖ ≤ p * B :=
      (hD w).trans (mul_le_mul_of_nonneg_left hw hp)
    calc
      |⟪z, D w⟫_ℝ| ≤ ‖z‖ * ‖D w‖ := abs_real_inner_le_norm _ _
      _ ≤ A * (p * B) :=
        mul_le_mul hz hDw (norm_nonneg _) ((norm_nonneg z).trans hz)
  have hA : |⟪a, D auu⟫_ℝ| ≤ p * Ω ^ 2 := by
    simpa only [one_mul] using hpair a auu 1 (Ω ^ 2) ha hauu
  have hB : |⟪au, D au⟫_ℝ| ≤ p * Ω ^ 2 := by
    convert hpair au au Ω Ω hau hau using 1 <;> ring
  have h₁ := abs_add_le (2 * ⟪a, D auu⟫_ℝ)
    (2 * ⟪au, D au⟫_ℝ)
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h₁
  nlinarith

/-- First derivative of the quadratic form of a real self-adjoint operator. -/
theorem selfAdjoint_quadratic_first_hasDerivAt
    (D : E →L[ℝ] E)
    (hsa : ∀ z w, ⟪z, D w⟫_ℝ = ⟪D z, w⟫_ℝ)
    (a au : ℝ → E) {t : ℝ}
    (ha : HasDerivAt a (au t) t) :
    HasDerivAt (fun s => ⟪a s, D (a s)⟫_ℝ)
      (2 * ⟪a t, D (au t)⟫_ℝ) t := by
  have h := ha.inner ℝ (projected_hasDerivAt D ha)
  have he : ⟪a t, D (au t)⟫_ℝ + ⟪au t, D (a t)⟫_ℝ =
      2 * ⟪a t, D (au t)⟫_ℝ := by
    rw [hsa (au t) (a t), real_inner_comm (D (au t)) (a t)]
    ring
  rw [he] at h
  exact h

/-- Second derivative of the quadratic form of a real self-adjoint operator. -/
theorem selfAdjoint_quadratic_second_hasDerivAt
    (D : E →L[ℝ] E)
    (a au auu : ℝ → E) {t : ℝ}
    (ha : HasDerivAt a (au t) t)
    (hau : HasDerivAt au (auu t) t) :
    HasDerivAt (fun s => 2 * ⟪a s, D (au s)⟫_ℝ)
      (2 * ⟪a t, D (auu t)⟫_ℝ +
        2 * ⟪au t, D (au t)⟫_ℝ) t := by
  simpa only [mul_add] using
    ((ha.inner ℝ (projected_hasDerivAt D hau)).const_mul 2)

end
end NumDetect
end LeanNumDetect
