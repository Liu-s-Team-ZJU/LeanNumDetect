import MultiTuran.Turan.Harnack
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv

/-! # The zero-free logarithmic derivative estimate

Positive harmonic functions control the derivative of their holomorphic
representatives by Harnack, Borel–Carathéodory and Cauchy's estimate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Complex Metric Real Set InnerProductSpace Filter Topology

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- Holomorphic derivatives are determined by the real part on a neighborhood. -/
theorem complex_derivative_eq_of_re_eventuallyEq {f g : ℂ → ℂ} {x A B : ℂ}
    (hf : HasDerivAt f A x) (hg : HasDerivAt g B x)
    (heq : (fun z => (f z).re) =ᶠ[𝓝 x] (fun z => (g z).re)) : A = B := by
  have hfR := Complex.reCLM.hasFDerivAt.comp x hf.complexToReal_fderiv
  have hgR := Complex.reCLM.hasFDerivAt.comp x hg.complexToReal_fderiv
  have h := hfR.unique (hgR.congr_of_eventuallyEq heq)
  have h1 := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) h
  have hI := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) h
  apply Complex.ext
  · simpa using h1
  · simpa using hI

/-- A positive real part gives a uniform derivative bound on the inner disk. -/
theorem analytic_derivative_le_of_nonnegative_real_part {F : ℂ → ℂ} {S : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball 0 2)) (hS : 0 < S)
    (hpos : ∀ y ∈ ball (0 : ℂ) 2, 0 ≤ (F y).re) {w x : ℂ}
    (hw : ‖w‖ ≤ 1) (hvalue : (F w).re ≤ S) (hx : ‖x‖ ≤ 1/2) :
    ‖deriv F x‖ ≤ 832*S := by
  let G : ℂ → ℂ := fun z => F z - F 0
  have hG : AnalyticOnNhd ℂ G (ball 0 2) := fun z hz => (hF z hz).sub analyticAt_const
  have hzero : 0 ≤ (F 0).re := hpos 0 (by simp)
  have hupper (z : ℂ) (hz : ‖z‖ ≤ 3/2) : (F z).re ≤ 52*S := by
    have h := harmonic_nonneg_harnack_pair (fun y hy => (hF y hy).harmonicAt_re) hpos hz hw
    linarith
  have hGnorm (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖G z‖ ≤ 208*S := by
    have hzball : z ∈ ball (0 : ℂ) (3/2 : ℝ) := by
      simp only [mem_ball, dist_zero_right]
      linarith
    have hsub : ball (0 : ℂ) (3/2 : ℝ) ⊆ ball 0 2 := by
      intro y hy
      simp only [mem_ball, dist_zero_right] at *
      linarith
    have hm : Set.MapsTo G (ball 0 (3/2 : ℝ)) {z : ℂ | z.re ≤ 52*S} := by
      intro y hy
      change (F y).re - (F 0).re ≤ 52*S
      have hyl : ‖y‖ < (3/2 : ℝ) := by simpa only [mem_ball,dist_zero_right] using hy
      have h := hupper y hyl.le
      linarith
    have h := Complex.borelCaratheodory_zero (by positivity : (0:ℝ) < 52*S)
      (hG.mono hsub).differentiableOn hm (by norm_num) hzball (by simp [G])
    have hden : (0 : ℝ) < 3/2-‖z‖ := by linarith
    apply h.trans
    apply (div_le_iff₀ hden).2
    nlinarith
  have hsub : closedBall x (1/4 : ℝ) ⊆ ball (0 : ℂ) 2 := by
    intro y hy
    have hyx : ‖y-x‖ ≤ (1/4:ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hy
    have hnorm := norm_le_norm_sub_add y x
    simp only [mem_ball,dist_zero_right]
    linarith
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0:ℝ) < 1/4) (hG.differentiableOn.diffContOnCl_ball hsub)
    (fun y hy => hGnorm y (by
      have hyx : ‖y-x‖ = (1/4:ℝ) := by simpa only [mem_sphere,dist_eq_norm] using hy
      have hnorm := norm_le_norm_sub_add y x
      linarith))
  have hxball : x ∈ ball (0 : ℂ) 2 := by
    simp only [mem_ball,dist_zero_right]
    linarith
  have hd : deriv G x = deriv F x := by
    exact ((hF x hxball).differentiableAt.hasDerivAt.sub_const (F 0)).deriv
  rw [hd] at hC
  linarith

/-- The logarithmic derivative of a zero-free holomorphic factor is bounded
linearly in its logarithmic growth, with an explicit absolute coefficient. -/
theorem zeroFree_logDerivative_le_of_growth {h : ℂ → ℂ} {M S : ℝ}
    (hh : AnalyticOnNhd ℂ h (ball 0 2))
    (hne : ∀ z ∈ ball (0 : ℂ) 2, h z ≠ 0) (hM : 0 < M) (hS : 0 < S)
    (hbound : ∀ z ∈ ball (0 : ℂ) 2, ‖h z‖ ≤ M) {w x : ℂ}
    (hw : ‖w‖ ≤ 1) (hx : ‖x‖ ≤ 1/2)
    (hgrowth : M ≤ Real.exp S * ‖h w‖) :
    ‖deriv h x / h x‖ ≤ 832*S := by
  let u : ℂ → ℝ := fun z => Real.log M - Real.log ‖h z‖
  have hu : HarmonicOnNhd u (ball 0 2) := fun z hz =>
    (harmonicAt_const _).sub ((hh z hz).harmonicAt_log_norm (hne z hz))
  obtain ⟨F,hF,hFre⟩ := hu.exists_analyticOnNhd_ball_re_eq
  have hFre' (z : ℂ) (hz : z ∈ ball (0 : ℂ) 2) : (F z).re = u z := hFre hz
  have hpos : ∀ z ∈ ball (0 : ℂ) 2, 0 ≤ (F z).re := by
    intro z hz
    rw [hFre' z hz]
    exact sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 (hne z hz)) (hbound z hz))
  have hwball : w ∈ ball (0 : ℂ) 2 := by
    simp only [mem_ball,dist_zero_right]
    linarith
  have hvalue : (F w).re ≤ S := by
    rw [hFre' w hwball]
    have hp := norm_pos_iff.2 (hne w hwball)
    have hg := Real.log_le_log hM hgrowth
    rw [Real.log_mul (Real.exp_ne_zero _) hp.ne',Real.log_exp] at hg
    dsimp [u]
    linarith
  have hder := analytic_derivative_le_of_nonnegative_real_part hF hS hpos hw hvalue hx
  have hxball : x ∈ ball (0 : ℂ) 2 := by
    simp only [mem_ball,dist_zero_right]
    linarith
  let g : ℂ → ℂ := fun z => (Real.log M : ℂ) - Complex.log (h z / h x) - (Real.log ‖h x‖ : ℂ)
  have hquot : HasDerivAt (fun z => h z / h x) (deriv h x / h x) x :=
    (hh x hxball).differentiableAt.hasDerivAt.div_const _
  have hquot1 : h x / h x = 1 := div_self (hne x hxball)
  have hg : HasDerivAt g (-(deriv h x / h x)) x := by
    have hlog := hquot.clog (by rw [hquot1]; exact Complex.one_mem_slitPlane)
    have he : deriv h x / h x / (h x / h x) = deriv h x / h x := by rw [hquot1,div_one]
    rw [he] at hlog
    convert ((hlog.const_sub (Real.log M : ℂ)).sub_const (Real.log ‖h x‖ : ℂ)) using 1 <;> simp [g]
  have hre : (fun z => (F z).re) =ᶠ[𝓝 x] (fun z => (g z).re) := by
    filter_upwards [isOpen_ball.mem_nhds hxball] with z hz
    rw [hFre' z hz]
    dsimp [u,g]
    rw [Complex.log_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 (hne z hz)) (norm_ne_zero_iff.2 (hne x hxball))]
    ring
  have heq := complex_derivative_eq_of_re_eventuallyEq (hF x hxball).differentiableAt.hasDerivAt hg hre
  rw [heq,norm_neg] at hder
  exact hder

end
end LeanNumDetect.MultiTuran
