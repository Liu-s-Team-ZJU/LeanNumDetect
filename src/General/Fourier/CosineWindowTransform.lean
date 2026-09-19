import General.Fourier.CosineWindow
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace LeanNumDetect

theorem window_kernel_integrable (s : ℕ) (eta t xi : ℝ) :
    Integrable (fun x : ℝ => (cosineWindow s eta (x - xi) : ℂ) *
      Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) := by
  have hf : Integrable (fun x : ℝ => (cosineWindow s eta x : ℂ)) volume :=
    (cosineWindow_integrable s eta).ofReal
  have hs : Integrable (fun x : ℝ => (cosineWindow s eta (x - xi) : ℂ)) volume :=
    hf.comp_sub_right xi
  refine hs.mul_bdd (g := fun x : ℝ => Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)))
    (c := 1) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · exact Filter.Eventually.of_forall (fun x => by
      simp [Complex.norm_exp, Complex.mul_re])

/-- The positive-sign, angular-frequency Fourier translation formula. -/
theorem windowTransform_translation (s : ℕ) (eta t xi : ℝ) :
    (∫ x : ℝ, (cosineWindow s eta (x - xi) : ℂ) *
      Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) =
      windowTransform s eta t * Complex.exp (Complex.I * ((t * xi : ℝ) : ℂ)) := by
  rw [← integral_add_right_eq_self (fun x : ℝ => (cosineWindow s eta (x - xi) : ℂ) *
    Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) xi]
  have he (x : ℝ) :
      Complex.I * ((t * (x + xi) : ℝ) : ℂ) =
        Complex.I * ((t * x : ℝ) : ℂ) + Complex.I * ((t * xi : ℝ) : ℂ) := by
    push_cast
    ring
  simp only [add_sub_cancel_right, he, Complex.exp_add, ← mul_assoc]
  exact integral_mul_const _ _

noncomputable def translatedWindowSum {q : ℕ} (s : ℕ) (eta : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ) (x : ℝ) : ℂ :=
  ∑ h, d h * (cosineWindow s eta (x - xi h) : ℂ)

noncomputable def exponentialSum {q : ℕ} (xi : Fin q → ℝ) (d : Fin q → ℂ) (t : ℝ) : ℂ :=
  ∑ h, d h * Complex.exp (Complex.I * ((t * xi h : ℝ) : ℂ))

theorem translatedWindowSum_integrable {q : ℕ} (s : ℕ) (eta : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ) :
    Integrable (translatedWindowSum s eta xi d) := by
  apply integrable_finsetSum
  intro h _
  exact ((show Integrable (fun x : ℝ => (cosineWindow s eta x : ℂ)) from
    (cosineWindow_integrable s eta).ofReal).comp_sub_right (xi h)).const_mul (d h)

/-- Compact support of the actual translated sum, including both end intervals. -/
theorem translatedWindowSum_support {q : ℕ} (s : ℕ) (eta lo hi : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ)
    (hxi : ∀ h, lo ≤ xi h ∧ xi h ≤ hi) :
    Function.support (translatedWindowSum s eta xi d) ⊆
      Set.Icc (lo - eta / 2) (hi + eta / 2) := by
  intro x hx
  by_contra hout
  apply hx
  unfold translatedWindowSum
  apply Finset.sum_eq_zero
  intro h _
  have hnot : x - xi h ∉ Set.Icc (-eta / 2) (eta / 2) := by
    intro hm
    apply hout
    constructor <;> linarith [(hxi h).1, (hxi h).2, hm.1, hm.2]
  simp only [cosineWindow, Set.indicator_of_notMem hnot, Complex.ofReal_zero, mul_zero]

theorem translatedWindowSum_tsupport {q : ℕ} (s : ℕ) (eta lo hi : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ)
    (hxi : ∀ h, lo ≤ xi h ∧ xi h ≤ hi) :
    tsupport (translatedWindowSum s eta xi d) ⊆
      Set.Icc (lo - eta / 2) (hi + eta / 2) :=
  closure_minimal (translatedWindowSum_support s eta lo hi xi d hxi) isClosed_Icc

/-- The actual Fourier integral of the translated window sum is F(t) g(t). -/
theorem translatedWindowSum_transform {q : ℕ} (s : ℕ) (eta : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ) (t : ℝ) :
    (∫ x : ℝ, translatedWindowSum s eta xi d x *
      Complex.exp (Complex.I * ((t * x : ℝ) : ℂ))) =
      windowTransform s eta t * exponentialSum xi d t := by
  simp only [translatedWindowSum, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum Finset.univ (fun h _ =>
    (window_kernel_integrable s eta t (xi h)).const_mul (d h))]
  simp only [integral_const_mul, windowTransform_translation, exponentialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

end LeanNumDetect
