import MultiTuran.TuranHarmonicMass
import MultiTuran.TuranEffectiveRoots
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-! Actual finite Cauchy sums with poles in the closed lower half plane. -/

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
open Set Filter MeasureTheory Complex Metric InnerProductSpace Real

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The unweighted finite Cauchy sum, with multiplicities retained. -/
def cauchySum {N : ℕ} (poles : Fin N → ℂ) (w : ℂ) : ℂ :=
  ∑ j, (w-poles j)⁻¹

/-- Its positive-real-part logarithmic majorant. -/
def cauchyLogMajorant {N : ℕ} (poles : Fin N → ℂ) (y : ℝ) (w : ℂ) : ℝ :=
  Real.log ‖1+Complex.I*cauchySum poles w/(y : ℂ)‖

theorem cauchySum_im_nonpos {N : ℕ} (poles : Fin N → ℂ)
    (hpoles : ∀ j, (poles j).im ≤ 0) {w : ℂ} (hw : 0 ≤ w.im) :
    (cauchySum poles w).im ≤ 0 := by
  unfold cauchySum
  change Complex.imLm (∑ j, (w-poles j)⁻¹) ≤ 0
  rw [map_sum]
  apply Finset.sum_nonpos
  intro j _
  change ((w-poles j)⁻¹).im ≤ 0
  rw [Complex.inv_im]
  apply div_nonpos_of_nonpos_of_nonneg
  · simp only [Complex.sub_im]
    linarith [hpoles j]
  · exact Complex.normSq_nonneg _

theorem analyticAt_cauchySum {N : ℕ} (poles : Fin N → ℂ) {w : ℂ}
    (hw : ∀ j, w ≠ poles j) : AnalyticAt ℂ (cauchySum poles) w := by
  unfold cauchySum
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr (hw j))

theorem cauchyMajorant_re_ge_one {N : ℕ} (poles : Fin N → ℂ)
    (hpoles : ∀ j, (poles j).im ≤ 0) {y : ℝ} (hy : 0 < y)
    {w : ℂ} (hw : 0 ≤ w.im) :
    1 ≤ (1+Complex.I*cauchySum poles w/(y : ℂ)).re := by
  simp only [Complex.add_re,Complex.one_re,Complex.div_ofReal_re,Complex.I_mul_re]
  have h := div_nonpos_of_nonpos_of_nonneg (cauchySum_im_nonpos poles hpoles hw) hy.le
  rw [neg_div]
  linarith

theorem cauchyLogMajorant_nonneg {N : ℕ} (poles : Fin N → ℂ)
    (hpoles : ∀ j, (poles j).im ≤ 0) {y : ℝ} (hy : 0 < y)
    {w : ℂ} (hw : 0 ≤ w.im) :
    0 ≤ cauchyLogMajorant poles y w := by
  apply Real.log_nonneg
  exact (cauchyMajorant_re_ge_one poles hpoles hy hw).trans (Complex.re_le_norm _)

theorem harmonicOnNhd_cauchyLogMajorant {N : ℕ} (poles : Fin N → ℂ)
    (hpoles : ∀ j, (poles j).im ≤ 0) {y : ℝ} (hy : 0 < y) :
    HarmonicOnNhd (cauchyLogMajorant poles y) {w : ℂ | 0 < w.im} := by
  intro w hw
  change 0 < w.im at hw
  have hn : ∀ j, w ≠ poles j := by
    intro j heq
    have him := congrArg Complex.im heq
    linarith [hpoles j]
  have ha : AnalyticAt ℂ (fun w => 1+Complex.I*cauchySum poles w/(y : ℂ)) w := by
    exact analyticAt_const.add ((analyticAt_const.mul (analyticAt_cauchySum poles hn)).div_const)
  apply AnalyticAt.harmonicAt_log_norm ha
  intro hz
  have h := cauchyMajorant_re_ge_one poles hpoles hy hw.le
  rw [hz] at h
  norm_num at h

theorem cauchyLogMajorant_continuousAt {N : ℕ} (poles : Fin N → ℂ)
    (hpoles : ∀ j, (poles j).im ≤ 0) {y : ℝ} (hy : 0 < y)
    {w : ℂ} (hw : 0 ≤ w.im) (hne : ∀ j, w ≠ poles j) :
    ContinuousAt (cauchyLogMajorant poles y) w := by
  have ha : ContinuousAt (fun w => 1+Complex.I*cauchySum poles w/(y : ℂ)) w :=
    (continuousAt_const.add ((continuousAt_const.mul (analyticAt_cauchySum poles hne).continuousAt).div_const _))
  have hpos : 0 < ‖1+Complex.I*cauchySum poles w/(y : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      ((cauchyMajorant_re_ge_one poles hpoles hy hw).trans (Complex.re_le_norm _))
  exact ha.norm.log hpos.ne'

/-- At height `R`, every pole is at least distance `R` from the imaginary
axis point, so the logarithmic centre value decays as `N/(yR)`. -/
theorem cauchyLogMajorant_imaginary_axis_le {N : ℕ} (poles : Fin N → ℂ)
    (hpoles : ∀ j, (poles j).im ≤ 0) {y R : ℝ} (hy : 0 < y) (hR : 0 < R) :
    cauchyLogMajorant poles y (Complex.I*(R : ℂ)) ≤ (N : ℝ)/(y*R) := by
  have hterm (j : Fin N) : ‖(Complex.I*(R : ℂ)-poles j)⁻¹‖ ≤ 1/R := by
    rw [norm_inv]
    have hd : R ≤ ‖Complex.I*(R : ℂ)-poles j‖ := by
      have hi := Complex.im_le_norm (Complex.I*(R : ℂ)-poles j)
      simp only [Complex.sub_im,Complex.mul_im,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add] at hi
      linarith [hpoles j]
    simpa only [one_div] using one_div_le_one_div_of_le hR hd
  have hsum : ‖cauchySum poles (Complex.I*(R : ℂ))‖ ≤ (N : ℝ)/R := by
    unfold cauchySum
    calc
      _ ≤ ∑ j, ‖(Complex.I*(R : ℂ)-poles j)⁻¹‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin N, 1/R := Finset.sum_le_sum (fun j _ => hterm j)
      _ = _ := by simp [div_eq_mul_inv]
  let w : ℂ := Complex.I*(R : ℂ)
  have hw : 0 ≤ w.im := by dsimp [w]; simpa using hR.le
  have hH : 1 ≤ ‖1+Complex.I*cauchySum poles w/(y : ℂ)‖ :=
    (cauchyMajorant_re_ge_one poles hpoles hy hw).trans (Complex.re_le_norm _)
  have hlog := Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hH)
  have hnorm := norm_add_le (1 : ℂ) (Complex.I*cauchySum poles w/(y : ℂ))
  have hdiv : ‖Complex.I*cauchySum poles w/(y : ℂ)‖ ≤ (N : ℝ)/(y*R) := by
    rw [norm_div,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]
    apply (div_le_iff₀ hy).mpr
    have he : (N : ℝ)/(y*R)*y=(N : ℝ)/R := by field_simp
    rw [he]
    exact hsum
  change Real.log ‖1+Complex.I*cauchySum poles w/(y : ℂ)‖ ≤ _
  rw [norm_one] at hnorm
  linarith

/-- The actual Cauchy logarithmic majorant has uniformly bounded whole-line
mass. This is the half-plane weak-Cauchy mechanism. -/
theorem lintegral_cauchyLogMajorant_le {N : ℕ} (poles : Fin N → ℂ)
    (hpoles : ∀ j, (poles j).im ≤ 0) {y : ℝ} (hy : 0 < y) :
    (∫⁻ x : ℝ, ENNReal.ofReal (cauchyLogMajorant poles y (x : ℂ))) ≤
      ENNReal.ofReal (2*Real.pi*(N : ℝ)/y) := by
  have hcentre : ∀ R : ℝ, 0 < R → cauchyLogMajorant poles y (Complex.I*(R : ℂ)) ≤
      ((N : ℝ)/y)/R := by
    intro R hR
    simpa only [div_div] using cauchyLogMajorant_imaginary_axis_le poles hpoles hy hR
  have hb : ∀ᵐ x : ℝ, ContinuousAt (cauchyLogMajorant poles y) (x : ℂ) := by
    filter_upwards [ae_ne_root_centres poles] with x hx
    exact cauchyLogMajorant_continuousAt poles hpoles hy (by simp) hx
  have h := harmonic_upperHalfPlane_lintegral_boundary_le
    (harmonicOnNhd_cauchyLogMajorant poles hpoles hy)
    (fun w hw => cauchyLogMajorant_nonneg poles hpoles hy hw.le)
    (by positivity : (0 : ℝ) ≤ (N : ℝ)/y) hcentre hb
  convert h using 1
  congr 1
  ring

end
end LeanNumDetect.MultiTuran
