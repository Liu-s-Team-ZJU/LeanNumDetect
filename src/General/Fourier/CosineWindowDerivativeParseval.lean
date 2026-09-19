import General.Fourier.CosineWindowDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace LeanNumDetect

noncomputable def translatedWindowSlope {q : ℕ} (s : ℕ) (eta : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ) (x : ℝ) : ℂ :=
  ∑ h, d h * (cosineWindowSlope s eta (x - xi h) : ℂ)

theorem translatedWindow_deriv_ae {q : ℕ} (s : ℕ) (eta : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ) :
    deriv (translatedWindowSum s eta xi d) =ᵐ[volume] translatedWindowSlope s eta xi d := by
  have hn : ∀ᵐ x : ℝ, ∀ h, x ≠ xi h - eta / 2 ∧ x ≠ xi h + eta / 2 := by
    rw [ae_all_iff]
    intro h
    have ha (a : ℝ) : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff]
    filter_upwards [ha (xi h - eta / 2), ha (xi h + eta / 2)] with x hx hy
    exact ⟨hx, hy⟩
  filter_upwards [hn] with x hx
  have hh (h : Fin q) : HasDerivAt (fun y : ℝ =>
      d h * (cosineWindow s eta (y - xi h) : ℂ))
      (d h * (cosineWindowSlope s eta (x - xi h) : ℂ)) x := by
    have hl : x - xi h ≠ -eta / 2 := by intro he; apply (hx h).1; linarith
    have hr : x - xi h ≠ eta / 2 := by intro he; apply (hx h).2; linarith
    have hd := ((cosineWindow_hasDerivAt_of_ne s eta (x - xi h) hl hr).comp x
      ((hasDerivAt_id x).sub_const (xi h))).ofReal_comp.const_mul (d h)
    simpa only [mul_one, Function.comp_def, id_eq] using hd
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun h _ => hh h)).deriv

theorem cosineWindowSlope_abs_le (s : ℕ) (eta x : ℝ) :
    |cosineWindowSlope s eta x| ≤ |(2 * s : ℝ) * (Real.pi / eta)| := by
  classical
  by_cases hx : x ∈ Set.Icc (-eta/2) (eta/2)
  · rw [cosineWindowSlope, Set.indicator_of_mem hx]
    have hc := pow_le_one₀ (abs_nonneg (Real.cos (Real.pi * x / eta)))
      (Real.abs_cos_le_one (Real.pi * x / eta)) (n := 2 * s - 1)
    have hs := Real.abs_sin_le_one (Real.pi * x / eta)
    calc
      _ = |(2 * s : ℝ) * (Real.pi / eta)| * |Real.sin (Real.pi * x / eta)| *
          |Real.cos (Real.pi * x / eta)| ^ (2 * s - 1) := by
        simp only [cosineProfileSlope, abs_mul, abs_neg, abs_pow]
      _ ≤ |(2 * s : ℝ) * (Real.pi / eta)| * 1 * 1 := by gcongr
      _ = _ := by ring
  · simp only [cosineWindowSlope, Set.indicator_of_notMem hx, abs_zero, abs_nonneg]

theorem translatedWindowSlope_integrable {q : ℕ} (s : ℕ) (eta : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ) : Integrable (translatedWindowSlope s eta xi d) := by
  apply integrable_finsetSum
  intro h _
  have hf : Integrable (fun x : ℝ => (cosineWindowSlope s eta x : ℂ)) :=
    (cosineWindowSlope_integrable s eta).ofReal
  exact (hf.comp_sub_right (xi h)).const_mul (d h)

theorem translatedWindowSlope_norm_le {q : ℕ} (s : ℕ) (eta : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ) (x : ℝ) :
    ‖translatedWindowSlope s eta xi d x‖ ≤
      ∑ h, ‖d h‖ * |(2 * s : ℝ) * (Real.pi / eta)| := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro h _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (cosineWindowSlope_abs_le s eta _) (norm_nonneg _)

theorem translatedWindowSlope_memLp_interval {q : ℕ} (s : ℕ) (eta a b : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ) :
    MemLp (translatedWindowSlope s eta xi d) 2 (volume.restrict (Set.Ioc a b)) := by
  apply MemLp.of_bound
    ((translatedWindowSlope_integrable s eta xi d).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self) (∑ h, ‖d h‖ * |(2 * s : ℝ) * (Real.pi / eta)|)
  exact Filter.Eventually.of_forall (translatedWindowSlope_norm_le s eta xi d)

theorem translatedWindowSlope_support {q : ℕ} (s : ℕ) (eta lo hi : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ) (hxi : ∀ h, lo ≤ xi h ∧ xi h ≤ hi) :
    Function.support (translatedWindowSlope s eta xi d) ⊆
      Set.Icc (lo - eta/2) (hi + eta/2) := by
  intro x hx
  by_contra hout
  apply hx
  unfold translatedWindowSlope
  apply Finset.sum_eq_zero
  intro h _
  have hm : x - xi h ∉ Set.Icc (-eta/2) (eta/2) := by
    intro hm
    apply hout
    constructor <;> linarith [(hxi h).1, (hxi h).2, hm.1, hm.2]
  simp only [cosineWindowSlope, Set.indicator_of_notMem hm, Complex.ofReal_zero, mul_zero]

theorem windowSlope_kernel_integrable (s : ℕ) (eta t xi : ℝ) :
    Integrable (fun x : ℝ => (cosineWindowSlope s eta (x - xi) : ℂ) *
      Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) := by
  have hf : Integrable (fun x : ℝ => (cosineWindowSlope s eta x : ℂ)) volume :=
    (cosineWindowSlope_integrable s eta).ofReal
  have hs : Integrable (fun x : ℝ => (cosineWindowSlope s eta (x - xi) : ℂ)) volume :=
    hf.comp_sub_right xi
  refine hs.mul_bdd (g := fun x : ℝ => Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)))
    (c := 1) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · exact Filter.Eventually.of_forall (fun x => by simp [Complex.norm_exp, Complex.mul_re])

theorem windowSlope_transform_translation {s : ℕ} (hs : 1 ≤ s) {eta : ℝ}
    (heta : 0 < eta) (t xi : ℝ) :
    (∫ x : ℝ, (cosineWindowSlope s eta (x - xi) : ℂ) *
      Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) =
      (-(Complex.I * (t : ℂ)) * windowTransform s eta t) *
        Complex.exp (Complex.I * ((t * xi : ℝ) : ℂ)) := by
  rw [← integral_add_right_eq_self (fun x : ℝ => (cosineWindowSlope s eta (x - xi) : ℂ) *
    Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) xi]
  have he (x : ℝ) : Complex.I * ((t * (x + xi) : ℝ) : ℂ) =
      Complex.I * ((t * x : ℝ) : ℂ) + Complex.I * ((t * xi : ℝ) : ℂ) := by
    push_cast; ring
  simp only [add_sub_cancel_right, he, Complex.exp_add, ← mul_assoc]
  rw [integral_mul_const, cosineWindowSlope_transform hs heta]

theorem translatedWindowSlope_transform {q s : ℕ} (hs : 1 ≤ s) {eta : ℝ}
    (heta : 0 < eta) (xi : Fin q → ℝ) (d : Fin q → ℂ) (t : ℝ) :
    (∫ x : ℝ, translatedWindowSlope s eta xi d x *
      Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) =
      -(Complex.I * (t : ℂ)) * windowTransform s eta t * exponentialSum xi d t := by
  simp only [translatedWindowSlope, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum Finset.univ (fun h _ =>
    (windowSlope_kernel_integrable s eta t (xi h)).const_mul (d h))]
  simp only [integral_const_mul, windowSlope_transform_translation hs heta,
    exponentialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- The derivative Parseval identity, expressed using the actual derivative of H. -/
theorem translatedWindow_derivative_parseval {q s : ℕ} (hs : 1 ≤ s) {eta : ℝ}
    (heta : 0 < eta) (lo hi shift : ℝ) (xi : Fin q → ℝ) (d : Fin q → ℂ)
    (hxi : ∀ h, lo ≤ xi h ∧ xi h ≤ hi) (hwidth : hi - lo + eta < 2 * Real.pi) :
    HasSum (fun k : ℤ => ((k : ℝ) - shift) ^ 2 *
      ‖windowTransform s eta ((k : ℝ) - shift)‖ ^ 2 *
      ‖exponentialSum xi d ((k : ℝ) - shift)‖ ^ 2)
      ((2 * Real.pi) * ∫ x : ℝ, ‖deriv (translatedWindowSum s eta xi d) x‖ ^ 2) := by
  let a := (lo + hi) / 2 - Real.pi
  have hz (x : ℝ) (hx : x ∉ Set.Ioc a (a + 2 * Real.pi)) :
      translatedWindowSlope s eta xi d x = 0 := by
    by_contra hn
    have hh := translatedWindowSlope_support s eta lo hi xi d hxi hn
    apply hx
    dsimp [a]
    constructor <;> linarith [hh.1, hh.2]
  have hh := hasSum_angularTransform_of_support a shift (translatedWindowSlope s eta xi d)
    (translatedWindowSlope_memLp_interval s eta a (a + 2 * Real.pi) xi d) hz
  have hn : (∫ x : ℝ, ‖translatedWindowSlope s eta xi d x‖ ^ 2) =
      ∫ x : ℝ, ‖deriv (translatedWindowSum s eta xi d) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [translatedWindow_deriv_ae s eta xi d] with x hx
    rw [hx]
  simpa only [translatedWindowSlope_transform hs heta, norm_mul, norm_neg, Complex.norm_I,
    one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hn] using hh
end LeanNumDetect
