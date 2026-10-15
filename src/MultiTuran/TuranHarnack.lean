import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Tactic

/-! # Quantitative Harnack estimates for the Turán argument

The estimates are proved from the Poisson formula and its existing kernel
bounds. They apply to actual harmonic functions and to the logarithmic
modulus of actual zero-free holomorphic functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Complex Metric Real Set InnerProductSpace

namespace LeanNumDetect.MultiTuran
noncomputable section

private theorem circleIntegrable_riesz_mul {u : ℂ → ℝ} {R : ℝ} {w : ℂ}
    (hu : ContinuousOn u (closedBall 0 R)) (hw : w ∈ ball 0 R) (hR : 0 < R) :
    CircleIntegrable (fun z => (herglotzRieszKernel 0 w z).re * u z) 0 R := by
  have hne : ∀ z ∈ sphere (0 : ℂ) R, z-w ≠ 0 := by
    intro z hz he
    have heq : z = w := sub_eq_zero.mp he
    subst z
    have hzR : ‖w‖ = R := by simpa using hz
    have hwR : ‖w‖ < R := by simpa using hw
    linarith
  have hk : ContinuousOn (fun z => (herglotzRieszKernel 0 w z).re) (sphere 0 R) := by
    simp only [herglotzRieszKernel, sub_zero]
    have hc : ContinuousOn (fun z : ℂ => (z+w)/(z-w)) (sphere 0 R) :=
      (continuousOn_id.add continuousOn_const).div
        (continuousOn_id.sub continuousOn_const) hne
    exact Complex.continuous_re.comp_continuousOn hc
  exact (hk.mul (hu.mono sphere_subset_closedBall)).circleIntegrable hR.le

/-- Both exact Harnack factors follow from the actual Poisson kernel. -/
theorem harmonic_nonneg_harnack_center {u : ℂ → ℝ} {R : ℝ}
    (hR : 0 < R) (hu : HarmonicOnNhd u (closedBall 0 R))
    (hpos : ∀ z ∈ closedBall (0 : ℂ) R, 0 ≤ u z) {w : ℂ}
    (hw : w ∈ ball 0 R) :
    (R-‖w‖)/(R+‖w‖) * u 0 ≤ u w ∧
      u w ≤ (R+‖w‖)/(R-‖w‖) * u 0 := by
  have hint := circleIntegrable_riesz_mul hu.continuousOn hw hR
  have huInt : CircleIntegrable u 0 R := by
    apply ContinuousOn.circleIntegrable'
    simpa only [abs_of_pos hR] using hu.continuousOn.mono sphere_subset_closedBall
  have hmean : Real.circleAverage u 0 R = u 0 := by
    apply HarmonicOnNhd.circleAverage_eq
    simpa only [abs_of_pos hR] using hu
  have hp := hu.circleAverage_re_herglotzRieszKernel_smul hw
  change Real.circleAverage (fun z => (herglotzRieszKernel 0 w z).re * u z) 0 R = u w at hp
  constructor
  · have h := Real.circleAverage_mono
      (huInt.const_smul (a := ((R-‖w‖)/(R+‖w‖)))) hint (fun z hz => ?_)
    · simpa only [Real.circleAverage_smul, smul_eq_mul, hmean, hp] using h
    · have hz' : z ∈ sphere (0 : ℂ) R := by simpa only [abs_of_pos hR] using hz
      have hk := le_re_herglotzRieszKernel hz' hw
      simp only [sub_zero] at hk
      simpa only [herglotzRieszKernel, sub_zero, Pi.smul_apply, smul_eq_mul] using
        mul_le_mul_of_nonneg_right hk (hpos z (sphere_subset_closedBall hz'))
  · have h := Real.circleAverage_mono hint
      (huInt.const_smul (a := ((R+‖w‖)/(R-‖w‖)))) (fun z hz => ?_)
    · simpa only [Real.circleAverage_smul, smul_eq_mul, hmean, hp] using h
    · have hz' : z ∈ sphere (0 : ℂ) R := by simpa only [abs_of_pos hR] using hz
      have hk := re_herglotzRieszKernel_le hz' hw
      simp only [sub_zero] at hk
      simpa only [herglotzRieszKernel, sub_zero, Pi.smul_apply, smul_eq_mul] using
        mul_le_mul_of_nonneg_right hk (hpos z (sphere_subset_closedBall hz'))

/-- A uniform two-point Harnack constant on the fixed disks used in the
zero-product argument. -/
theorem harmonic_nonneg_harnack_pair {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (ball 0 2))
    (hpos : ∀ z ∈ ball (0 : ℂ) 2, 0 ≤ u z) {z w : ℂ}
    (hz : ‖z‖ ≤ 3/2) (hw : ‖w‖ ≤ 1) : u z ≤ 52 * u w := by
  have hsubset : closedBall (0 : ℂ) (7/4 : ℝ) ⊆ ball 0 2 := by
    intro x hx
    simp only [mem_closedBall, mem_ball, dist_zero_right] at *
    linarith
  have huf := hu.mono hsubset
  have hpf : ∀ x ∈ closedBall (0 : ℂ) (7/4 : ℝ), 0 ≤ u x :=
    fun x hx => hpos x (hsubset hx)
  have hzball : z ∈ ball (0 : ℂ) (7/4 : ℝ) := by
    simp only [mem_ball, dist_zero_right]
    linarith
  have hwball : w ∈ ball (0 : ℂ) (7/4 : ℝ) := by
    simp only [mem_ball, dist_zero_right]
    linarith
  have hzupper := (harmonic_nonneg_harnack_center (by norm_num) huf hpf hzball).2
  have hwlower := (harmonic_nonneg_harnack_center (by norm_num) huf hpf hwball).1
  have hzero : 0 ≤ u 0 := hpos 0 (by simp)
  have hratioz : ((7/4 : ℝ)+‖z‖)/((7/4 : ℝ)-‖z‖) ≤ 13 := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < 7/4-‖z‖)).2
    linarith
  have hratiow : (1/4 : ℝ) ≤ ((7/4 : ℝ)-‖w‖)/((7/4 : ℝ)+‖w‖) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 7/4+‖w‖)).2
    linarith
  have hzbound := hzupper.trans (mul_le_mul_of_nonneg_right hratioz hzero)
  have hwbound := (mul_le_mul_of_nonneg_right hratiow hzero).trans hwlower
  linarith

/-- A zero-free holomorphic factor cannot be too small on the inner disk
when its outer bound and one inner value have controlled ratio. -/
theorem zeroFree_norm_lower_of_growth {h : ℂ → ℂ} {M S : ℝ}
    (hh : AnalyticOnNhd ℂ h (ball 0 2))
    (hne : ∀ z ∈ ball (0 : ℂ) 2, h z ≠ 0) (hM : 0 < M)
    (hbound : ∀ z ∈ ball (0 : ℂ) 2, ‖h z‖ ≤ M) {w z : ℂ}
    (hw : ‖w‖ ≤ 1) (hz : ‖z‖ ≤ 3/2)
    (hgrowth : M ≤ Real.exp S * ‖h w‖) :
    M * Real.exp (-52*S) ≤ ‖h z‖ := by
  let u : ℂ → ℝ := fun x => Real.log M - Real.log ‖h x‖
  have hlog : HarmonicOnNhd u (ball 0 2) := by
    intro x hx
    exact (harmonicAt_const (Real.log M) : HarmonicAt (fun _ : ℂ => Real.log M) x).sub
      ((hh x hx).harmonicAt_log_norm (hne x hx))
  have hpos : ∀ x ∈ ball (0 : ℂ) 2, 0 ≤ u x := by
    intro x hx
    exact sub_nonneg.2 (Real.log_le_log (norm_pos_iff.2 (hne x hx)) (hbound x hx))
  have hwball : w ∈ ball (0 : ℂ) 2 := by simpa only [mem_ball, dist_zero_right] using
    (show ‖w‖ < (2:ℝ) by linarith)
  have hzball : z ∈ ball (0 : ℂ) 2 := by simpa only [mem_ball, dist_zero_right] using
    (show ‖z‖ < (2:ℝ) by linarith)
  have hwp : 0 < ‖h w‖ := norm_pos_iff.2 (hne w hwball)
  have hzp : 0 < ‖h z‖ := norm_pos_iff.2 (hne z hzball)
  have hloggrowth := Real.log_le_log hM hgrowth
  rw [Real.log_mul (Real.exp_ne_zero _) hwp.ne', Real.log_exp] at hloggrowth
  have huw : u w ≤ S := by dsimp [u]; linarith
  have huz := harmonic_nonneg_harnack_pair hlog hpos hz hw
  have hlower : Real.log M - 52*S ≤ Real.log ‖h z‖ := by dsimp [u] at *; linarith
  have he := Real.exp_le_exp.mpr hlower
  simpa only [Real.exp_sub, Real.exp_log hM, Real.exp_log hzp, neg_mul,
    Real.exp_neg, div_eq_mul_inv] using he

end
end LeanNumDetect.MultiTuran
