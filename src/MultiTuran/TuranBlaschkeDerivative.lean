import MultiTuran.TuranBlaschkeExtraction
import MultiTuran.TuranLogDerivative
import MultiTuran.TuranCauchyWeak
import Mathlib.Analysis.Calculus.LogDeriv

/-! # Actual logarithmic derivatives of finite Blaschke factorizations -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators ComplexConjugate Topology ENNReal
open Set Metric Filter MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

theorem logDeriv_blaschkeFactor {R : ℝ} (hR : 0 < R) {root z : ℂ}
    (hroot : ‖root‖ < R) (hz : ‖z‖ ≤ R) (hzero : z ≠ root) :
    logDeriv (blaschkeFactor R root) z =
      (z-root)⁻¹ + conj root/((R : ℂ)^2-conj root*z) := by
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hnum : (R : ℂ)*(z-root) ≠ 0 := mul_ne_zero hRne (sub_ne_zero.mpr hzero)
  have hden := blaschke_denominator_ne_zero hroot hz
  unfold blaschkeFactor
  rw [logDeriv_div z hnum hden (by fun_prop) (by fun_prop),
    logDeriv_const_mul z (R : ℂ) hRne]
  have hn : HasDerivAt (fun u : ℂ => u-root) 1 z := (hasDerivAt_id z).sub_const root
  have hd : HasDerivAt (fun u : ℂ => (R : ℂ)^2-conj root*u) (-conj root) z :=
    by simpa using ((hasDerivAt_id z).const_mul (conj root)).const_sub ((R : ℂ)^2)
  simp only [logDeriv_apply,hn.deriv,hd.deriv,one_div,neg_div,sub_neg_eq_add]

theorem logDeriv_blaschkeProduct {N : ℕ} {R : ℝ} (hR : 0 < R)
    (roots : Fin N → ℂ) (hroots : ∀ i, ‖roots i‖ < R) {z : ℂ} (hz : z ∈ closedBall 0 R)
    (hzero : ∀ i, z ≠ roots i) :
    logDeriv (blaschkeProduct R roots) z =
      (∑ i, (z-roots i)⁻¹) + ∑ i, conj (roots i)/((R : ℂ)^2-conj (roots i)*z) := by
  have hnorm : ‖z‖ ≤ R := by simpa using hz
  have hne (i : Fin N) : blaschkeFactor R (roots i) z ≠ 0 :=
    div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne')
      (sub_ne_zero.mpr (hzero i))) (blaschke_denominator_ne_zero (hroots i) hnorm)
  have h := logDeriv_prod (s := Finset.univ) (fun i _ => hne i)
    (fun i _ => (analyticOnNhd_blaschkeFactor (hroots i) z hz).differentiableAt)
  change logDeriv (blaschkeProduct R roots) z = ∑ i, logDeriv (blaschkeFactor R (roots i)) z at h
  rw [h]
  simp_rw [logDeriv_blaschkeFactor hR (hroots _) hnorm (hzero _)]
  rw [Finset.sum_add_distrib]

theorem norm_blaschke_correction_four_le {root z : ℂ}
    (hroot : ‖root‖ ≤ 2) (hz : ‖z‖ ≤ 1/2) :
    ‖conj root/((4 : ℂ)^2-conj root*z)‖ ≤ (2/15 : ℝ) := by
  have hprod : ‖conj root*z‖ ≤ 1 := by
    rw [norm_mul,Complex.norm_conj]
    have h := mul_le_mul hroot hz (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h
    exact h
  have hden : (15 : ℝ) ≤ ‖(4 : ℂ)^2-conj root*z‖ := by
    norm_num only [show (4 : ℂ)^2 = 16 by norm_num]
    have h := norm_sub_norm_le ((4 : ℂ)^2) (conj root*z)
    norm_num at h
    rw [norm_mul,Complex.norm_conj] at hprod
    linarith
  rw [norm_div,Complex.norm_conj]
  exact div_le_div₀ (by positivity) hroot (by norm_num) hden

theorem norm_sum_blaschke_correction_four_le {N : ℕ} (roots : Fin N → ℂ)
    (hroots : ∀ i, ‖roots i‖ ≤ 2) {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖∑ i, conj (roots i)/((4 : ℂ)^2-conj (roots i)*z)‖ ≤ (2/15 : ℝ)*N := by
  calc
    _ ≤ ∑ i, ‖conj (roots i)/((4 : ℂ)^2-conj (roots i)*z)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, (2/15 : ℝ) :=
      Finset.sum_le_sum (fun i _ => norm_blaschke_correction_four_le (hroots i) hz)
    _ = _ := by simp; ring

theorem logDeriv_eq_cauchy_add_of_blaschke_factor {N : ℕ} (roots : Fin N → ℂ)
    (hroots : ∀ i, ‖roots i‖ ≤ 2) {f h : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 4))
    (hh : AnalyticOnNhd ℂ h (closedBall 0 4))
    (hfactor : ∀ u ∈ closedBall (0 : ℂ) 4, f u = blaschkeProduct 4 roots u*h u)
    {z : ℂ} (hz : ‖z‖ ≤ 1/2) (hfz : f z ≠ 0) :
    deriv f z/f z = (∑ i, (z-roots i)⁻¹) +
      (∑ i, conj (roots i)/((4 : ℂ)^2-conj (roots i)*z)) + deriv h z/h z := by
  have hzball : z ∈ ball (0 : ℂ) 4 := by
    simp only [mem_ball,dist_zero_right]
    linarith
  have hz4 := ball_subset_closedBall hzball
  have hroots4 : ∀ i, ‖roots i‖ < (4 : ℝ) := fun i => (hroots i).trans_lt (by norm_num)
  have hne : blaschkeProduct 4 roots z ≠ 0 ∧ h z ≠ 0 :=
    mul_ne_zero_iff.mp ((hfactor z hz4) ▸ hfz)
  have hzero : ∀ i, z ≠ roots i := by
    intro i hi
    apply hne.1
    unfold blaschkeProduct
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [blaschkeFactor,hi]
  have hlocal : f =ᶠ[𝓝 z] fun u => blaschkeProduct 4 roots u*h u := by
    filter_upwards [closedBall_mem_nhds_of_mem hzball] with u hu
    exact hfactor u hu
  have hlog : logDeriv f z = logDeriv (fun u => blaschkeProduct 4 roots u*h u) z := by
    simp only [logDeriv_apply,hlocal.deriv_eq,hlocal.self_of_nhds]
  rw [← logDeriv_apply,hlog,logDeriv_mul z hne.1 hne.2
    (analyticOnNhd_blaschkeProduct hroots4 z hz4).differentiableAt
    (hh z hz4).differentiableAt,
    logDeriv_blaschkeProduct (by norm_num) roots hroots4 hz4 hzero,logDeriv_apply]
  norm_num only [Complex.ofReal_ofNat]

/-- A true bounded-growth holomorphic function has its actual logarithmic
derivative bounded by an actual Cauchy sum plus a linear growth loss. -/
theorem exists_logDerivative_cauchy_majorant {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 4)) {M S : ℝ} (hM : 0 < M) (hS : 0 < S)
    (hbound : ∀ z ∈ sphere (0 : ℂ) 4, ‖f z‖ ≤ M) {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hgrowth : M ≤ Real.exp S*‖f w‖) :
    ∃ N : ℕ, ∃ roots : Fin N → ℂ, (N : ℝ) ≤ 7*S ∧
      ∀ z : ℂ, ‖z‖ ≤ 1/2 → f z ≠ 0 →
        ‖deriv f z/f z‖ ≤ ‖∑ i, (z-roots i)⁻¹‖ + 833*S := by
  obtain ⟨N,roots,h,hroots,hN,_horder,hh,hne,hfactor,_hcircle,hboth⟩ :=
    exists_bounded_zeroFree_blaschke_factor hf hM hbound hw hgrowth
  have hballsub : ball (0 : ℂ) 2 ⊆ closedBall 0 4 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  have hw4 : w ∈ closedBall (0 : ℂ) 4 := by
    simp only [mem_closedBall,dist_zero_right]
    linarith
  have hhgrowth : M ≤ Real.exp S*‖h w‖ :=
    hgrowth.trans (mul_le_mul_of_nonneg_left (hboth w hw4).1 (Real.exp_nonneg _))
  refine ⟨N,roots,hN,?_⟩
  intro z hz hfz
  have hhder := zeroFree_logDerivative_le_of_growth (hh.mono hballsub) hne hM hS
    (fun u hu => (hboth u (hballsub hu)).2) hw hz hhgrowth
  rw [logDeriv_eq_cauchy_add_of_blaschke_factor roots hroots hf hh hfactor hz hfz]
  have hcor := norm_sum_blaschke_correction_four_le roots hroots hz
  calc
    _ ≤ ‖∑ i, (z-roots i)⁻¹‖+
        ‖∑ i, conj (roots i)/((4 : ℂ)^2-conj (roots i)*z)‖+‖deriv h z/h z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

end
end LeanNumDetect.MultiTuran
