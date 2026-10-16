import MultiTuran.ConsecutiveWindow.InterpolationGeometry
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # The actual holomorphic regularization of the pulled-back Cauchy kernel

The exponential divided slope is entire.  On a strip of imaginary width
less than `2π` it has no zero.  This removes the single apparent pole without
assuming any interpolation formula or any node separation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter
open scoped Topology

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

theorem exponential_dslope_analyticAt (a w : ℂ) :
    AnalyticAt ℂ (dslope Complex.exp a) w := by
  by_cases h : w=a
  · subst w
    obtain ⟨p,hp⟩ := (analyticAt_cexp : AnalyticAt ℂ Complex.exp a)
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  · have hden : w-a ≠ 0 := sub_ne_zero.mpr h
    have hf : AnalyticAt ℂ (fun z : ℂ => (Complex.exp z-Complex.exp a)/(z-a)) w := by
      fun_prop
    apply hf.congr
    filter_upwards [eventually_ne_nhds h] with z hz
    simp [dslope_of_ne _ hz,slope_def_module,smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem exponential_dslope_ne_zero_of_strip (a w : ℂ)
    (ha : -Real.pi<a.im ∧ a.im≤Real.pi)
    (hw : -Real.pi<w.im ∧ w.im≤Real.pi) : dslope Complex.exp a w ≠ 0 := by
  by_cases h : w=a
  · subst w
    simp only [dslope_same,Complex.deriv_exp]
    exact Complex.exp_ne_zero a
  · have hne : Complex.exp w ≠ Complex.exp a := by
      intro he
      apply h
      calc
        w = Complex.log (Complex.exp w) := (Complex.log_exp hw.1 hw.2).symm
        _ = Complex.log (Complex.exp a) := congrArg Complex.log he
        _ = a := Complex.log_exp ha.1 ha.2
    rw [dslope_of_ne _ h,slope_def_module,smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr h)) (sub_ne_zero.mpr hne)

def windowPullbackRegular (t : ℝ) (a w : ℂ) : ℂ :=
  Complex.exp ((t : ℂ)*w)*Complex.exp w/dslope Complex.exp a w

theorem windowPullbackRegular_analyticAt (t : ℝ) (a w : ℂ)
    (ha : -Real.pi<a.im ∧ a.im≤Real.pi)
    (hw : -Real.pi<w.im ∧ w.im≤Real.pi) :
    AnalyticAt ℂ (windowPullbackRegular t a) w := by
  apply AnalyticAt.div _ (exponential_dslope_analyticAt a w)
    (exponential_dslope_ne_zero_of_strip a w ha hw)
  fun_prop

@[simp] theorem windowPullbackRegular_self (t : ℝ) (a : ℂ) :
    windowPullbackRegular t a a = Complex.exp ((t : ℂ)*a) := by
  unfold windowPullbackRegular
  rw [dslope_same,Complex.deriv_exp]
  exact mul_div_cancel_right₀ _ (Complex.exp_ne_zero a)

theorem windowPullbackRegular_div_sub (t : ℝ) (a w : ℂ) (hw : w≠a) :
    windowPullbackRegular t a w/(w-a) =
      Complex.exp ((t : ℂ)*w)*Complex.exp w/(Complex.exp w-Complex.exp a) := by
  unfold windowPullbackRegular
  rw [dslope_of_ne _ hw,slope_def_module,smul_eq_mul]
  field_simp

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
