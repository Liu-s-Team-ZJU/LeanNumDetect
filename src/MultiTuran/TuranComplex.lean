import MultiTuran.TuranInterval
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Genuine growth bounds for complex exponential sums

Subtracting a real exponential makes the sampled roots lie in the unit
disk. The exact-degree recurrence therefore gives radial disk growth.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Set Metric

namespace LeanNumDetect.MultiTuran
open TuranRecurrence
noncomputable section

def complexExponentialSum {n : ℕ} (exponent c : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ j, c j * Complex.exp (exponent j * z)

theorem complexExponentialSum_affine {n : ℕ} (exponent c : Fin n → ℂ)
    (a b z : ℂ) :
    complexExponentialSum (fun j => exponent j*b)
      (fun j => c j*Complex.exp (exponent j*a)) z =
        complexExponentialSum exponent c (b*z+a) := by
  unfold complexExponentialSum
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem complexExponentialSum_on_mesh {n : ℕ} (exponent c : Fin n → ℂ)
    (step : ℝ) (M : ℕ) :
    powerSum (fun j => Complex.exp (exponent j*(step : ℂ))) c M =
      complexExponentialSum exponent c (((M : ℝ)*step : ℝ) : ℂ) := by
  unfold powerSum complexExponentialSum
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- The recurrence applies to arbitrary complex exponents with nonpositive
real parts, without any distinctness assumption. -/
theorem complexExponentialSum_extrapolate_nonpos {n : ℕ} (hn : 0 < n)
    (exponent c : Fin n → ℂ) (hexponent : ∀ j, (exponent j).re ≤ 0)
    {length T B : ℝ} (hlength : 0 < length) (hT : length ≤ T)
    (hbound : ∀ t ∈ Icc (0 : ℝ) length,
      ‖complexExponentialSum exponent c (t : ℂ)‖ ≤ B) :
    ‖complexExponentialSum exponent c (T : ℂ)‖ ≤
      B*(4*Real.exp 1*T/length)^(n-1) := by
  have hT0 : 0 < T := hlength.trans_le hT
  have hB : 0 ≤ B := (norm_nonneg _).trans (hbound 0 ⟨le_rfl,hlength.le⟩)
  by_cases hn2 : 2 ≤ n
  · obtain ⟨M,hMr,hMpos,hstepbound,hratio⟩ :=
      exists_turan_extrapolation_mesh (show 0 < n-1 by omega) hlength hT
    have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
    let step : ℝ := T/M
    have hstep : 0 ≤ step := by dsimp [step]; positivity
    have hz : ∀ j, ‖Complex.exp (exponent j*(step : ℂ))‖ ≤ 1 := by
      intro j
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero] using mul_nonpos_of_nonpos_of_nonneg (hexponent j) hstep
    have hinitial : ∀ k < n,
        ‖powerSum (fun j => Complex.exp (exponent j*(step : ℂ))) c k‖ ≤ B := by
      intro k hk
      rw [complexExponentialSum_on_mesh]
      apply hbound
      constructor
      · exact mul_nonneg (Nat.cast_nonneg _) hstep
      · have hkr : (k : ℝ) ≤ (n-1 : ℕ) := by exact_mod_cast (show k ≤ n-1 by omega)
        exact (mul_le_mul_of_nonneg_right hkr hstep).trans hstepbound
    have h := unit_powerSum_norm_le_degree hn2
      (fun j => Complex.exp (exponent j*(step : ℂ))) c hz hB hinitial hMr
    rw [complexExponentialSum_on_mesh] at h
    have heval : (M : ℝ)*step = T := by dsimp [step]; field_simp
    rw [heval] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hB
    apply pow_le_pow_left₀ (by positivity)
    calc
      _ = (2*Real.exp 1)*((M : ℝ)/(n-1 : ℕ)) := by ring
      _ ≤ (2*Real.exp 1)*(2*T/length) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  · have hn1 : n = 1 := by omega
    subst n
    have hnorm : ‖complexExponentialSum exponent c (T : ℂ)‖ ≤ ‖c 0‖ := by
      simp only [complexExponentialSum, Fin.sum_univ_one, norm_mul, Complex.norm_exp]
      have harg : (exponent 0 * (T : ℂ)).re ≤ 0 := by
        simpa using mul_nonpos_of_nonpos_of_nonneg (hexponent 0) hT0.le
      simpa using mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr harg) (norm_nonneg (c 0))
    have hc : ‖c 0‖ ≤ B := by
      simpa [complexExponentialSum] using hbound 0 ⟨le_rfl,hlength.le⟩
    simpa using hnorm.trans hc

theorem complexExponentialSum_shift_exponent {n : ℕ} (exponent c : Fin n → ℂ)
    (σ t : ℝ) :
    complexExponentialSum (fun j => exponent j-(σ : ℂ)) c (t : ℂ) =
      (Real.exp (-σ*t) : ℂ) * complexExponentialSum exponent c (t : ℂ) := by
  unfold complexExponentialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.ofReal_exp]
  rw [mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Real-ray growth for a genuine exponential sum with real parts bounded
by `σ`. The exponential loss is independent of the number of terms. -/
theorem complexExponentialSum_extrapolate_real {n : ℕ} (hn : 0 < n)
    (exponent c : Fin n → ℂ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hexponent : ∀ j, (exponent j).re ≤ σ)
    {length T B : ℝ} (hlength : 0 < length) (hT : length ≤ T)
    (hbound : ∀ t ∈ Icc (0 : ℝ) length,
      ‖complexExponentialSum exponent c (t : ℂ)‖ ≤ B) :
    ‖complexExponentialSum exponent c (T : ℂ)‖ ≤
      B*Real.exp (σ*T)*(4*Real.exp 1*T/length)^(n-1) := by
  let shifted : Fin n → ℂ := fun j => exponent j-(σ : ℂ)
  have hshifted : ∀ j, (shifted j).re ≤ 0 := by
    intro j
    simpa [shifted] using sub_nonpos.mpr (hexponent j)
  have hnorm (t : ℝ) : ‖complexExponentialSum shifted c (t : ℂ)‖ =
      Real.exp (-σ*t)*‖complexExponentialSum exponent c (t : ℂ)‖ := by
    rw [complexExponentialSum_shift_exponent, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hboundShifted : ∀ t ∈ Icc (0 : ℝ) length,
      ‖complexExponentialSum shifted c (t : ℂ)‖ ≤ B := by
    intro t ht
    rw [hnorm]
    have hfactor : Real.exp (-σ*t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ) ht.1)
    calc
      _ ≤ ‖complexExponentialSum exponent c (t : ℂ)‖ := by
        simpa using mul_le_mul_of_nonneg_right hfactor
          (norm_nonneg (complexExponentialSum exponent c (t : ℂ)))
      _ ≤ B := hbound t ht
  have h := complexExponentialSum_extrapolate_nonpos hn shifted c hshifted
    hlength hT hboundShifted
  rw [hnorm] at h
  have heq : Real.exp (σ*T)*Real.exp (-σ*T) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_nonneg (σ*T))
  calc
    _ = Real.exp (σ*T)*(Real.exp (-σ*T)*
        ‖complexExponentialSum exponent c (T : ℂ)‖) := by rw [← mul_assoc,heq,one_mul]
    _ ≤ Real.exp (σ*T)*(B*(4*Real.exp 1*T/length)^(n-1)) := hh
    _ = _ := by ring

/-- Actual complex disk growth, with the exact exponent `n - 1` and an
absolute numerical constant. The center, radii, coefficients and exponents
are unrestricted apart from the stated radius and frequency bounds. -/
theorem complexExponentialSum_disk_norm_le {n : ℕ} (hn : 0 < n)
    (exponent c : Fin n → ℂ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hexponent : ∀ j, ‖exponent j‖ ≤ σ)
    (center : ℂ) {r R B : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hbound : ∀ w ∈ Metric.closedBall center r,
      ‖complexExponentialSum exponent c w‖ ≤ B)
    {z : ℂ} (hz : z ∈ Metric.closedBall center R) :
    ‖complexExponentialSum exponent c z‖ ≤
      B*Real.exp (σ*R)*(4*Real.exp 1*R/r)^(n-1) := by
  have hR : 0 < R := hr.trans_le hrR
  have hzR : ‖z-center‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  let v : ℂ := (z-center)/(R : ℂ)
  have hv : ‖v‖ ≤ 1 := by
    dsimp [v]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact (div_le_one hR).mpr hzR
  let exponentRay : Fin n → ℂ := fun j => exponent j*v
  let coeffRay : Fin n → ℂ := fun j => c j*Complex.exp (exponent j*center)
  have hrepr (t : ℂ) : complexExponentialSum exponentRay coeffRay t =
      complexExponentialSum exponent c (v*t+center) :=
    complexExponentialSum_affine exponent c center v t
  have hreal : ∀ j, (exponentRay j).re ≤ σ := by
    intro j
    calc
      _ ≤ ‖exponentRay j‖ := Complex.re_le_norm _
      _ = ‖exponent j‖*‖v‖ := norm_mul _ _
      _ ≤ ‖exponent j‖*1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ ≤ σ := by simpa using hexponent j
  have hboundRay : ∀ t ∈ Icc (0 : ℝ) r,
      ‖complexExponentialSum exponentRay coeffRay (t : ℂ)‖ ≤ B := by
    intro t ht
    rw [hrepr]
    apply hbound
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right hv ht.1).trans (by simpa using ht.2)
  have h := complexExponentialSum_extrapolate_real hn exponentRay coeffRay hσ hreal
    hr hrR hboundRay
  have harg : v*(R : ℂ)+center = z := by
    dsimp [v]
    rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hR.ne')]
    ring
  rwa [hrepr, harg] at h

theorem differentiable_complexExponentialSum {n : ℕ}
    (exponent c : Fin n → ℂ) : Differentiable ℂ (complexExponentialSum exponent c) := by
  unfold complexExponentialSum
  apply Differentiable.fun_sum
  intro j _
  fun_prop

end
end LeanNumDetect.MultiTuran
