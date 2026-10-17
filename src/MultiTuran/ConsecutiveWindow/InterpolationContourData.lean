import MultiTuran.ConsecutiveWindow.InterpolationKernel
import MultiTuran.ConsecutiveWindow.RectangleCauchy

/-! # The actual sector contour and its Newton coefficients -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
open Set Complex MeasureTheory

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

def windowContourLower (n : ℕ) : ℂ := ⟨Real.log (1-1/(n : ℝ)),-windowContourAngle n⟩
def windowContourUpper (n : ℕ) : ℂ := ⟨Real.log (1+1/(n : ℝ)),windowContourAngle n⟩

def WindowBoundary (n : ℕ) (w : ℂ) : Prop :=
  Real.log (1-1/(n : ℝ)) ≤ w.re ∧ w.re ≤ Real.log (1+1/(n : ℝ)) ∧
  -windowContourAngle n ≤ w.im ∧ w.im ≤ windowContourAngle n ∧
  (w.re=Real.log (1-1/(n : ℝ)) ∨ w.re=Real.log (1+1/(n : ℝ)) ∨
    w.im= -windowContourAngle n ∨ w.im=windowContourAngle n)

theorem windowContour_real_order {n : ℕ} (hn : 2 ≤ n) :
    Real.log (1-1/(n : ℝ)) < Real.log (1+1/(n : ℝ)) := by
  have hr := windowContourRadii_bounds hn
  apply Real.log_lt_log (by linarith [hr.1])
  linarith [hr.2.1,hr.2.2.1]

theorem windowBoundary_bottom {n : ℕ} (hn : 2 ≤ n) {x : ℝ}
    (hx : x ∈ Icc (Real.log (1-1/(n : ℝ))) (Real.log (1+1/(n : ℝ)))) :
    WindowBoundary n (x+(-windowContourAngle n)*I) := by
  have hA := windowContourAngle_bounds hn
  simp only [WindowBoundary, Complex.add_re, Complex.add_im, Complex.mul_I_re,
    Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, neg_zero, add_zero, zero_add]
  exact ⟨hx.1, hx.2, le_rfl, by linarith, Or.inr (Or.inr (Or.inl True.intro))⟩

theorem windowBoundary_top {n : ℕ} (hn : 2 ≤ n) {x : ℝ}
    (hx : x ∈ Icc (Real.log (1-1/(n : ℝ))) (Real.log (1+1/(n : ℝ)))) :
    WindowBoundary n (x+windowContourAngle n*I) := by
  have hA := windowContourAngle_bounds hn
  simp only [WindowBoundary, Complex.add_re, Complex.add_im, Complex.mul_I_re,
    Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero, add_zero, zero_add]
  exact ⟨hx.1, hx.2, by linarith, le_rfl, Or.inr (Or.inr (Or.inr True.intro))⟩

theorem windowBoundary_right {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : y ∈ Icc (-windowContourAngle n) (windowContourAngle n)) :
    WindowBoundary n (Real.log (1+1/(n : ℝ))+y*I) := by
  simp only [WindowBoundary, Complex.add_re, Complex.add_im, Complex.mul_I_re,
    Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero, add_zero, zero_add]
  exact ⟨(windowContour_real_order hn).le, le_rfl, hy.1, hy.2, Or.inr (Or.inl True.intro)⟩

theorem windowBoundary_left {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : y ∈ Icc (-windowContourAngle n) (windowContourAngle n)) :
    WindowBoundary n (Real.log (1-1/(n : ℝ))+y*I) := by
  simp only [WindowBoundary, Complex.add_re, Complex.add_im, Complex.mul_I_re,
    Complex.mul_I_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero, add_zero, zero_add]
  exact ⟨le_rfl, (windowContour_real_order hn).le, hy.1, hy.2, Or.inl True.intro⟩

theorem windowBoundary_distance_lower {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : |y| ≤ Real.pi-Real.pi/(n : ℝ)) {w : ℂ} (hw : WindowBoundary n w) :
    1/(n : ℝ) ≤ ‖Complex.exp w-angularPhase y‖ := by
  have hr := windowContourRadii_bounds hn
  have hr0 : 0 < 1-1/(n : ℝ) := by linarith [hr.1]
  have hR0 : 0 < 1+1/(n : ℝ) := by linarith [hr.2.2.1]
  rcases hw.2.2.2.2 with hleft | hright | hbottom | htop
  · have hnorm : ‖Complex.exp w‖=1-1/(n : ℝ) := by rw [Complex.norm_exp,hleft,Real.exp_log hr0]
    have h := norm_sub_norm_le (angularPhase y) (Complex.exp w)
    rw [angularPhase_norm,hnorm,norm_sub_rev] at h
    linarith
  · have hnorm : ‖Complex.exp w‖=1+1/(n : ℝ) := by rw [Complex.norm_exp,hright,Real.exp_log hR0]
    have h := norm_sub_norm_le (Complex.exp w) (angularPhase y)
    rw [angularPhase_norm,hnorm] at h
    linarith
  · exact window_log_radial_distance_lower hn hy hw.1 (Or.inr hbottom)
  · exact window_log_radial_distance_lower hn hy hw.1 (Or.inl htop)

def windowNodes {n : ℕ} (frequency : Fin n → ℝ) (i : ℕ) : ℂ :=
  if hi : i<n then angularPhase (frequency ⟨i,hi⟩) else 1

@[simp] theorem windowNodes_at {n : ℕ} (frequency : Fin n → ℝ) (j : Fin n) :
    windowNodes frequency j.val = angularPhase (frequency j) := by simp [windowNodes]

theorem windowNodes_norm_le {n : ℕ} (frequency : Fin n → ℝ) (i : ℕ) :
    ‖windowNodes frequency i‖ ≤ 1 := by
  unfold windowNodes
  split <;> simp

def windowNewtonKernel {n : ℕ} (frequency : Fin n → ℝ) (t : ℝ) (k : ℕ) (w : ℂ) : ℂ :=
  Complex.exp ((t : ℂ)*w)*Complex.exp w /
    ∏ i ∈ Finset.range (k+1), (Complex.exp w-windowNodes frequency i)

theorem windowNewtonKernel_denominator_ne_zero {n : ℕ} (hn : 2 ≤ n)
    (frequency : Fin n → ℝ) (hfrequency : ∀ j, |frequency j| ≤ Real.pi-Real.pi/(n : ℝ))
    {k : ℕ} (hk : k<n) {w : ℂ} (hw : WindowBoundary n w) :
    (∏ i ∈ Finset.range (k+1), (Complex.exp w-windowNodes frequency i)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hi' : i<n := by have h := Finset.mem_range.mp hi; omega
  have h := windowBoundary_distance_lower hn (hfrequency ⟨i,hi'⟩) hw
  simp only [windowNodes,hi',dif_pos] at *
  exact norm_pos_iff.mp ((by positivity : (0 : ℝ) < 1/(n : ℝ)).trans_le h)

theorem windowNewtonKernel_continuousWithinAt {n : ℕ} (hn : 2 ≤ n)
    (frequency : Fin n → ℝ) (hfrequency : ∀ j, |frequency j| ≤ Real.pi-Real.pi/(n : ℝ))
    (t : ℝ) {k : ℕ} (hk : k<n) {w : ℂ} (hw : WindowBoundary n w) :
    ContinuousAt (windowNewtonKernel frequency t k) w := by
  exact (by fun_prop : ContinuousAt (fun z : ℂ =>
    Complex.exp ((t : ℂ)*z)*Complex.exp z) w).div
    (by fun_prop : ContinuousAt (fun z : ℂ =>
      ∏ i ∈ Finset.range (k+1), (Complex.exp z-windowNodes frequency i)) w)
    (windowNewtonKernel_denominator_ne_zero hn frequency hfrequency hk hw)

theorem windowNewtonKernel_boundaryIntegrable {n : ℕ} (hn : 2 ≤ n)
    (frequency : Fin n → ℝ) (hfrequency : ∀ j, |frequency j| ≤ Real.pi-Real.pi/(n : ℝ))
    (t : ℝ) {k : ℕ} (hk : k<n) :
    RectangleBoundaryIntegrable (windowNewtonKernel frequency t k)
      (windowContourLower n) (windowContourUpper n) := by
  have hA := windowContourAngle_bounds hn
  constructor
  · change IntervalIntegrable (fun x : ℝ => windowNewtonKernel frequency t k
      ((x : ℂ) + ((-windowContourAngle n : ℝ) : ℂ)*I)) volume
        (Real.log (1-1/(n : ℝ))) (Real.log (1+1/(n : ℝ)))
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le (windowContour_real_order hn).le] at hx
    have hc : ContinuousAt (windowNewtonKernel frequency t k)
        ((x : ℂ)+((-windowContourAngle n : ℝ) : ℂ)*I) := by
      simpa only [Complex.ofReal_neg] using
        windowNewtonKernel_continuousWithinAt hn frequency hfrequency t hk (windowBoundary_bottom hn hx)
    exact (hc.comp
        (f := fun x : ℝ => (x : ℂ)+((-windowContourAngle n : ℝ) : ℂ)*I) (x := x)
        (by fun_prop : ContinuousAt
        (fun x : ℝ => (x : ℂ)+((-windowContourAngle n : ℝ) : ℂ)*I) x)).continuousWithinAt
  constructor
  · change IntervalIntegrable (fun x : ℝ => windowNewtonKernel frequency t k
      ((x : ℂ) + (windowContourAngle n : ℂ)*I)) volume
        (Real.log (1-1/(n : ℝ))) (Real.log (1+1/(n : ℝ)))
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [uIcc_of_le (windowContour_real_order hn).le] at hx
    exact ((windowNewtonKernel_continuousWithinAt hn frequency hfrequency t hk
      (windowBoundary_top hn hx)).comp
        (f := fun x : ℝ => (x : ℂ)+(windowContourAngle n : ℂ)*I) (x := x)
        (by fun_prop : ContinuousAt
        (fun x : ℝ => (x : ℂ)+(windowContourAngle n : ℂ)*I) x)).continuousWithinAt
  constructor
  · change IntervalIntegrable (fun y : ℝ => windowNewtonKernel frequency t k
      ((Real.log (1+1/(n : ℝ)) : ℂ)+(y : ℂ)*I)) volume (-windowContourAngle n) (windowContourAngle n)
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le (by linarith : -windowContourAngle n ≤ windowContourAngle n)] at hy
    exact ((windowNewtonKernel_continuousWithinAt hn frequency hfrequency t hk
      (windowBoundary_right hn hy)).comp
        (f := fun y : ℝ => (Real.log (1+1/(n : ℝ)) : ℂ)+(y : ℂ)*I) (x := y)
        (by fun_prop : ContinuousAt
        (fun y : ℝ => (Real.log (1+1/(n : ℝ)) : ℂ)+(y : ℂ)*I) y)).continuousWithinAt
  · change IntervalIntegrable (fun y : ℝ => windowNewtonKernel frequency t k
      ((Real.log (1-1/(n : ℝ)) : ℂ)+(y : ℂ)*I)) volume (-windowContourAngle n) (windowContourAngle n)
    apply ContinuousOn.intervalIntegrable
    intro y hy
    rw [uIcc_of_le (by linarith : -windowContourAngle n ≤ windowContourAngle n)] at hy
    exact ((windowNewtonKernel_continuousWithinAt hn frequency hfrequency t hk
      (windowBoundary_left hn hy)).comp
        (f := fun y : ℝ => (Real.log (1-1/(n : ℝ)) : ℂ)+(y : ℂ)*I) (x := y)
        (by fun_prop : ContinuousAt
        (fun y : ℝ => (Real.log (1-1/(n : ℝ)) : ℂ)+(y : ℂ)*I) y)).continuousWithinAt

theorem windowNewtonKernel_norm_le {n : ℕ} (hn : 2 ≤ n)
    (frequency : Fin n → ℝ) (hfrequency : ∀ j, |frequency j| ≤ Real.pi-Real.pi/(n : ℝ))
    {t : ℝ} (ht0 : 0 ≤ t) (htn : t≤n) {k : ℕ} (hk : k<n)
    {w : ℂ} (hw : WindowBoundary n w) :
    ‖windowNewtonKernel frequency t k w‖ ≤
      (1+1/(n : ℝ))^n*Real.exp w.re*(n : ℝ)^(k+1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr := windowContourRadii_bounds hn
  have hR0 : 0 < 1+1/(n : ℝ) := by linarith [hr.2.2.1]
  have hlog : 0 ≤ Real.log (1+1/(n : ℝ)) := (Real.log_pos hr.2.2.1).le
  have hnum : ‖Complex.exp ((t : ℂ)*w)‖ ≤ (1+1/(n : ℝ))^n := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    calc
      _ ≤ Real.exp ((n : ℝ)*Real.log (1+1/(n : ℝ))) :=
        Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hw.2.1 ht0).trans
          (mul_le_mul_of_nonneg_right htn hlog))
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log hR0]
  have hprod : (1/(n : ℝ))^(k+1) ≤
      ‖∏ i ∈ Finset.range (k+1), (Complex.exp w-windowNodes frequency i)‖ := by
    rw [norm_prod]
    calc
      _ = ∏ _i ∈ Finset.range (k+1), (1/(n : ℝ)) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity) (fun i hi => by
        have hi' : i<n := by have h := Finset.mem_range.mp hi; omega
        simpa only [windowNodes,hi',dif_pos] using windowBoundary_distance_lower hn (hfrequency ⟨i,hi'⟩) hw)
  have hprodpos : 0 < ‖∏ i ∈ Finset.range (k+1), (Complex.exp w-windowNodes frequency i)‖ :=
    (by positivity : (0 : ℝ) < (1/(n : ℝ))^(k+1)).trans_le hprod
  have hinv : 1/‖∏ i ∈ Finset.range (k+1), (Complex.exp w-windowNodes frequency i)‖ ≤ (n : ℝ)^(k+1) := by
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (1/(n : ℝ))^(k+1)) hprod
    simpa only [one_div,inv_pow,inv_inv] using h
  unfold windowNewtonKernel
  rw [norm_div,norm_mul,Complex.norm_exp w]
  calc
    _ = ‖Complex.exp ((t : ℂ)*w)‖*Real.exp w.re *
        (1/‖∏ i ∈ Finset.range (k+1), (Complex.exp w-windowNodes frequency i)‖) := by ring
    _ ≤ ((1+1/(n : ℝ))^n*Real.exp w.re)*(n : ℝ)^(k+1) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hnum (Real.exp_pos _).le) hinv
        (by positivity) (by positivity)
    _ = _ := rfl

def windowNewtonCoefficient {n : ℕ} (frequency : Fin n → ℝ) (t : ℝ) (k : Fin n) : ℂ :=
  (((2*Real.pi : ℝ) : ℂ)*I)⁻¹ *
    rectangleIntegral (windowNewtonKernel frequency t k.val)
      (windowContourLower n) (windowContourUpper n)

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
