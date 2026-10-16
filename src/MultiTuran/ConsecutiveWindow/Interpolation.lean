import MultiTuran.ConsecutiveWindow.InterpolationAlgebra
import MultiTuran.ConsecutiveWindow.InterpolationCoefficientBounds
import MultiTuran.ConsecutiveWindow.InterpolationPullback

/-! # Unconditional interpolation on a consecutive sampling window

Every coefficient is constructed from the actual sector contour.  The
Newton resolvent identity handles repeated coordinate nodes without any
minimum-separation input.  The final interface contains only the manuscript's
frequency chart and the range of the requested interpolation time.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
open Set Complex MeasureTheory Polynomial

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

theorem window_rectangleIntegral_congr {n : ℕ} (hn : 2 ≤ n) (f g : ℂ → ℂ)
    (hfg : ∀ w, WindowBoundary n w → f w=g w) :
    rectangleIntegral f (windowContourLower n) (windowContourUpper n) =
      rectangleIntegral g (windowContourLower n) (windowContourUpper n) := by
  have hA := windowContourAngle_bounds hn
  have hb : (∫ x : ℝ in Real.log (1/2 : ℝ)..Real.log (3/2 : ℝ),
      f (x+(-windowContourAngle n)*I)) =
    ∫ x : ℝ in Real.log (1/2 : ℝ)..Real.log (3/2 : ℝ), g (x+(-windowContourAngle n)*I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le windowContour_real_order.le] at hx
    exact hfg _ (windowBoundary_bottom hn hx)
  have ht : (∫ x : ℝ in Real.log (1/2 : ℝ)..Real.log (3/2 : ℝ),
      f (x+windowContourAngle n*I)) =
    ∫ x : ℝ in Real.log (1/2 : ℝ)..Real.log (3/2 : ℝ), g (x+windowContourAngle n*I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le windowContour_real_order.le] at hx
    exact hfg _ (windowBoundary_top hn hx)
  have hr : (∫ y : ℝ in -windowContourAngle n..windowContourAngle n,
      f (Real.log (3/2 : ℝ)+y*I)) =
    ∫ y : ℝ in -windowContourAngle n..windowContourAngle n, g (Real.log (3/2 : ℝ)+y*I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (by linarith : -windowContourAngle n ≤ windowContourAngle n)] at hy
    exact hfg _ (windowBoundary_right hy)
  have hl : (∫ y : ℝ in -windowContourAngle n..windowContourAngle n,
      f (Real.log (1/2 : ℝ)+y*I)) =
    ∫ y : ℝ in -windowContourAngle n..windowContourAngle n, g (Real.log (1/2 : ℝ)+y*I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le (by linarith : -windowContourAngle n ≤ windowContourAngle n)] at hy
    exact hfg _ (windowBoundary_left hy)
  dsimp only [rectangleIntegral,windowContourLower,windowContourUpper]
  simp only [Complex.ofReal_neg]
  rw [hb,ht,hr,hl]

theorem windowNewtonPolynomial_eval {n : ℕ} (hn : 2 ≤ n)
    (frequency : Fin n → ℝ) (hfrequency : ∀ j, |frequency j| ≤ Real.pi-Real.pi/(n : ℝ))
    (t : ℝ) (j : Fin n) :
    (newtonPolynomial n (windowNodes frequency) (windowNewtonCoefficient frequency t)).eval
      (angularPhase (frequency j)) = Complex.exp (I*((t*frequency j : ℝ) : ℂ)) := by
  let A (k : Fin n) : ℂ := ∏ i ∈ Finset.range k.val,
    (angularPhase (frequency j)-windowNodes frequency i)
  let K (k : Fin n) : ℂ → ℂ := windowNewtonKernel frequency t k.val
  let N : ℂ := (((2*Real.pi : ℝ) : ℂ)*I)⁻¹
  have hFK (k : Fin n) : RectangleBoundaryIntegrable (fun w => A k*K k w)
      (windowContourLower n) (windowContourUpper n) := by
    have h := windowNewtonKernel_boundaryIntegrable hn frequency hfrequency t k.isLt
    exact ⟨h.1.const_mul _,h.2.1.const_mul _,h.2.2.1.const_mul _,h.2.2.2.const_mul _⟩
  have hpoint (w : ℂ) (hw : WindowBoundary n w) :
      (∑ k : Fin n, A k*K k w) =
        Complex.exp ((t : ℂ)*w)*Complex.exp w/(Complex.exp w-angularPhase (frequency j)) := by
    have hnodes (i : ℕ) (hi : i<n) : Complex.exp w≠windowNodes frequency i := by
      have h := windowBoundary_distance_lower hn (hfrequency ⟨i,hi⟩) hw
      have hpos : 0 < 1/(n : ℝ) := by positivity
      simpa only [windowNodes,hi,dif_pos] using sub_ne_zero.mp (norm_pos_iff.mp (hpos.trans_le h))
    have h := newton_resolvent_at_node (windowNodes frequency) j (Complex.exp w) hnodes
    rw [← Fin.sum_univ_eq_sum_range] at h
    simp only [windowNodes_at] at h
    have hh := congrArg (fun v : ℂ => (Complex.exp ((t : ℂ)*w)*Complex.exp w)*v) h
    rw [Finset.mul_sum] at hh
    convert hh.symm using 1
    · apply Finset.sum_congr rfl
      intro k _
      dsimp [A,K,windowNewtonKernel]
      ring
    · ring
  calc
    _ = ∑ k : Fin n,
        (N*rectangleIntegral (K k) (windowContourLower n) (windowContourUpper n))*A k := by
      simp only [newtonPolynomial,eval_finsetSum,eval_mul,eval_C,newtonBasis_eval,
        windowNewtonCoefficient,A,K,N]
    _ = N*(∑ k : Fin n, rectangleIntegral (fun w => A k*K k w)
        (windowContourLower n) (windowContourUpper n)) := by
      simp only [rectangleIntegral_const_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = N*rectangleIntegral (fun w => ∑ k : Fin n, A k*K k w)
        (windowContourLower n) (windowContourUpper n) := by
      rw [rectangleIntegral_finset_sum Finset.univ (fun k w => A k*K k w)
        (windowContourLower n) (windowContourUpper n) (fun k _ => hFK k)]
    _ = N*rectangleIntegral (fun w =>
        Complex.exp ((t : ℂ)*w)*Complex.exp w/(Complex.exp w-angularPhase (frequency j)))
        (windowContourLower n) (windowContourUpper n) := by
      congr 1
      exact window_rectangleIntegral_congr hn _ _ hpoint
    _ = _ := by
      rw [windowPullback_cauchy hn (hfrequency j) t]
      dsimp [N]
      push_cast
      have hp : (Real.pi : ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
      rw [← mul_assoc,inv_mul_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num) hp) I_ne_zero),one_mul]

/-- Literal consecutive-window interpolation, with no separation or
distinctness assumption on the coordinate frequencies. -/
theorem exists_window_interpolation_coefficients {n : ℕ} (hn : 2 ≤ n)
    (frequency : Fin n → ℝ) (hfrequency : ∀ j, |frequency j| ≤ Real.pi-Real.pi/(n : ℝ))
    {t : ℝ} (ht0 : 0 ≤ t) (htn : t≤n) :
    ∃ a : Fin n → ℂ, (∑ k, ‖a k‖) ≤ 3*(3*(n : ℝ))^n ∧
      ∀ j, Complex.exp (I*((t*frequency j : ℝ) : ℂ)) =
        ∑ k, a k*Complex.exp (I*(((k.val : ℝ)*frequency j : ℝ) : ℂ)) := by
  let p := newtonPolynomial n (windowNodes frequency) (windowNewtonCoefficient frequency t)
  apply exists_window_coefficients_of_polynomial (by omega) frequency t p
    (newtonPolynomial_natDegree_le (by omega) _ _)
  · exact newtonPolynomial_mass_le_window_constant hn _ (windowNodes_norm_le frequency) _
      (windowNewtonCoefficient_norm_le hn frequency hfrequency ht0 htn)
  · exact windowNewtonPolynomial_eval hn frequency hfrequency t

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
