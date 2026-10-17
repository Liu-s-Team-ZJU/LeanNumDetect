import MultiTuran.ConsecutiveWindow.InterpolationContourData

/-! # Exact reproduction by the pulled-back sector contour

The regularized exponential divided slope permits a direct application of
the fully proved rectangular Cauchy formula, including repeated nodes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Complex MeasureTheory

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

theorem window_node_inside_contour {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : |y| ≤ Real.pi - Real.pi / (n : ℝ)) :
    -windowContourAngle n < y ∧ y < windowContourAngle n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpi : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hnR
  have hquarter : Real.pi / (4 * (n : ℝ)) = (Real.pi / (n : ℝ)) / 4 := by ring
  have hylo := (abs_le.mp hy).1
  have hyhi := (abs_le.mp hy).2
  unfold windowContourAngle
  rw [hquarter]
  constructor <;> linarith

theorem windowBoundary_ne_pole {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : |y| ≤ Real.pi - Real.pi / (n : ℝ)) {w : ℂ}
    (hw : WindowBoundary n w) : w ≠ I * (y : ℂ) := by
  intro heq
  have hwre : w.re = 0 := by rw [heq]; simp
  have hi : w.im = y := by rw [heq]; simp
  have hyinside := window_node_inside_contour hn hy
  have hr := windowContourRadii_bounds hn
  have hr0 : 0 < 1-1/(n : ℝ) := by linarith [hr.1]
  have hlo : Real.log (1-1/(n : ℝ)) < 0 := Real.log_neg hr0 hr.2.1
  have hhi : 0 < Real.log (1+1/(n : ℝ)) := Real.log_pos hr.2.2.1
  rcases hw.2.2.2.2 with hleft | hright | hbottom | htop
  · rw [hleft] at hwre
    exact hlo.ne hwre
  · rw [hright] at hwre
    exact hhi.ne' hwre
  · rw [hbottom] at hi
    exact hyinside.1.ne hi
  · rw [htop] at hi
    exact hyinside.2.ne' hi

theorem windowPullback_cauchy {n : ℕ} (hn : 2 ≤ n) {y : ℝ}
    (hy : |y| ≤ Real.pi - Real.pi / (n : ℝ)) (t : ℝ) :
    rectangleIntegral (fun w => Complex.exp ((t : ℂ) * w) * Complex.exp w /
      (Complex.exp w - angularPhase y)) (windowContourLower n) (windowContourUpper n) =
        ((2 * Real.pi : ℂ) * I) * Complex.exp (I * ((t * y : ℝ) : ℂ)) := by
  let a : ℂ := I * (y : ℂ)
  let f : ℂ → ℂ := windowPullbackRegular t a
  have hA := windowContourAngle_bounds hn
  have hyinside := window_node_inside_contour hn hy
  have ha : -Real.pi < a.im ∧ a.im ≤ Real.pi := by
    dsimp [a]
    simp only [mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add]
    constructor <;> linarith
  have hf : AnalyticOnNhd ℂ f
      (Icc (windowContourLower n).re (windowContourUpper n).re ×ℂ
        Icc (windowContourLower n).im (windowContourUpper n).im) := by
    intro w hw
    apply windowPullbackRegular_analyticAt t a w ha
    simp only [windowContourLower, windowContourUpper, mem_reProdIm, mem_Icc] at hw
    constructor <;> linarith [hw.2.1, hw.2.2]
  have hr := windowContourRadii_bounds hn
  have hr0 : 0 < 1-1/(n : ℝ) := by linarith [hr.1]
  have hleft₀ : (windowContourLower n).re < a.re := by
    simpa [windowContourLower, a] using
      (Real.log_neg hr0 hr.2.1)
  have hright₀ : a.re < (windowContourUpper n).re := by
    simpa [windowContourUpper, a] using Real.log_pos hr.2.2.1
  have hbottom₀ : (windowContourLower n).im < a.im := by
    simpa [windowContourLower, a] using hyinside.1
  have htop₀ : a.im < (windowContourUpper n).im := by
    simpa [windowContourUpper, a] using hyinside.2
  have hc := rectangle_cauchy_of_analyticOnNhd f
    (windowContourLower n) (windowContourUpper n) a
    hleft₀ hright₀ hbottom₀ htop₀ hf
  have hpoint (w : ℂ) (hw : WindowBoundary n w) :
      Complex.exp ((t : ℂ) * w) * Complex.exp w / (Complex.exp w - angularPhase y) =
        f w / (w - a) := by
    exact (windowPullbackRegular_div_sub t a w (windowBoundary_ne_pole hn hy hw)).symm
  have hab : (windowContourLower n).re ≤ (windowContourUpper n).re :=
    (windowContour_real_order hn).le
  have habim : (windowContourLower n).im ≤ (windowContourUpper n).im := by
    dsimp [windowContourLower, windowContourUpper]
    linarith
  have hbottom : (∫ x : ℝ in (windowContourLower n).re..(windowContourUpper n).re,
      Complex.exp ((t : ℂ) * (x + (windowContourLower n).im * I)) *
        Complex.exp (x + (windowContourLower n).im * I) /
        (Complex.exp (x + (windowContourLower n).im * I) - angularPhase y)) =
      ∫ x : ℝ in (windowContourLower n).re..(windowContourUpper n).re,
        f (x + (windowContourLower n).im * I) / (x + (windowContourLower n).im * I - a) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    apply hpoint
    simpa only [windowContourLower, Complex.ofReal_neg] using windowBoundary_bottom hn hx
  have htop : (∫ x : ℝ in (windowContourLower n).re..(windowContourUpper n).re,
      Complex.exp ((t : ℂ) * (x + (windowContourUpper n).im * I)) *
        Complex.exp (x + (windowContourUpper n).im * I) /
        (Complex.exp (x + (windowContourUpper n).im * I) - angularPhase y)) =
      ∫ x : ℝ in (windowContourLower n).re..(windowContourUpper n).re,
        f (x + (windowContourUpper n).im * I) / (x + (windowContourUpper n).im * I - a) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact hpoint _ (windowBoundary_top hn hx)
  have hright : (∫ z : ℝ in (windowContourLower n).im..(windowContourUpper n).im,
      Complex.exp ((t : ℂ) * ((windowContourUpper n).re + z * I)) *
        Complex.exp ((windowContourUpper n).re + z * I) /
        (Complex.exp ((windowContourUpper n).re + z * I) - angularPhase y)) =
      ∫ z : ℝ in (windowContourLower n).im..(windowContourUpper n).im,
        f ((windowContourUpper n).re + z * I) / ((windowContourUpper n).re + z * I - a) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le habim] at hz
    exact hpoint _ (windowBoundary_right hn hz)
  have hleft : (∫ z : ℝ in (windowContourLower n).im..(windowContourUpper n).im,
      Complex.exp ((t : ℂ) * ((windowContourLower n).re + z * I)) *
        Complex.exp ((windowContourLower n).re + z * I) /
        (Complex.exp ((windowContourLower n).re + z * I) - angularPhase y)) =
      ∫ z : ℝ in (windowContourLower n).im..(windowContourUpper n).im,
        f ((windowContourLower n).re + z * I) / ((windowContourLower n).re + z * I - a) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le habim] at hz
    exact hpoint _ (windowBoundary_left hn hz)
  calc
    _ = rectangleIntegral (fun w => f w / (w - a))
        (windowContourLower n) (windowContourUpper n) := by
      simp only [rectangleIntegral, hbottom, htop, hright, hleft]
    _ = ((2 * Real.pi : ℂ) * I) * f a := hc
    _ = _ := by
      simp only [f, windowPullbackRegular_self]
      congr 2
      dsimp [a]
      push_cast
      ring

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
