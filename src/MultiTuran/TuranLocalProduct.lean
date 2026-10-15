import MultiTuran.TuranBlaschkeFactors
import MultiTuran.TuranComplex
import MultiTuran.TuranHarnack
import MultiTuran.TuranEffectiveProductRoots

/-! Disk growth and actual finite Blaschke products give the local
effective-degree lower estimate used in the measurable-set Turán theorem. -/

set_option autoImplicit false
open scoped BigOperators ComplexConjugate
open Set Metric

namespace LeanNumDetect.MultiTuran
noncomputable section

private theorem blaschke_four_denominator_bounds {w z : ℂ}
    (hw : ‖w‖ ≤ 2) (hz : ‖z‖ ≤ 3/2) :
    13 ≤ ‖(4 : ℂ)^2-conj w*z‖ ∧ ‖(4 : ℂ)^2-conj w*z‖ ≤ 19 := by
  have hp : ‖conj w*z‖ ≤ 3 := by
    rw [norm_mul,Complex.norm_conj]
    nlinarith [norm_nonneg w,norm_nonneg z]
  have hnorm : ‖(4 : ℂ)^2‖=16 := by norm_num
  have hl := norm_sub_norm_le ((4 : ℂ)^2) (conj w*z)
  have hu := norm_sub_le ((4 : ℂ)^2) (conj w*z)
  rw [hnorm] at hl hu
  constructor <;> linarith

theorem norm_blaschkeFactor_four_le_distance {w z : ℂ}
    (hw : ‖w‖ ≤ 2) (hz : ‖z‖ ≤ 3/2) :
    ‖blaschkeFactor 4 w z‖ ≤ ‖z-w‖ := by
  obtain ⟨hl,_⟩ := blaschke_four_denominator_bounds hw hz
  have hp : 0 < ‖(4 : ℂ)^2-conj w*z‖ := by linarith
  rw [blaschkeFactor,norm_div,norm_mul]
  have h4 : ‖((4 : ℝ) : ℂ)‖=4 := by norm_num
  rw [h4]
  apply (div_le_iff₀ hp).mpr
  nlinarith [norm_nonneg (z-w)]

theorem norm_blaschkeFactor_four_lower {w z : ℂ}
    (hw : ‖w‖ ≤ 2) (hz : ‖z‖ ≤ 1/2) :
    (4/17 : ℝ)*min 1 ‖z-w‖ ≤ ‖blaschkeFactor 4 w z‖ := by
  have hp : ‖conj w*z‖ ≤ 1 := by
    rw [norm_mul,Complex.norm_conj]
    nlinarith [norm_nonneg w,norm_nonneg z]
  have hu := norm_sub_le ((4 : ℂ)^2) (conj w*z)
  have hn : ‖(4 : ℂ)^2‖=16 := by norm_num
  rw [hn] at hu
  have hl := (blaschke_four_denominator_bounds (w:=w) (z:=z) hw (by linarith)).1
  rw [blaschkeFactor,norm_div,norm_mul]
  have h4 : ‖((4 : ℝ) : ℂ)‖=4 := by norm_num
  rw [h4]
  apply (le_div_iff₀ (by linarith : 0 < ‖(4 : ℂ)^2-conj w*z‖)).mpr
  have ha := min_le_right (1 : ℝ) ‖z-w‖
  have ha0 : 0 ≤ min 1 ‖z-w‖ := le_min (by norm_num) (norm_nonneg _)
  calc
    _ ≤ (4/17 : ℝ)*min 1 ‖z-w‖*17 :=
      mul_le_mul_of_nonneg_left (by linarith : ‖(4 : ℂ)^2-conj w*z‖ ≤ 17) (by positivity)
    _ = 4*min 1 ‖z-w‖ := by ring
    _ ≤ 4*‖z-w‖ := mul_le_mul_of_nonneg_left ha (by norm_num)

theorem norm_blaschkeFactor_four_le_local {w x z : ℂ} {r : ℝ}
    (hw : ‖w‖ ≤ 2) (hx : ‖x‖ ≤ 1/2) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz : z ∈ closedBall x r) :
    ‖blaschkeFactor 4 w z‖ ≤ r+min 1 ‖x-w‖ := by
  have hzx : ‖z-x‖ ≤ r := by simpa [Metric.mem_closedBall,dist_eq_norm] using hz
  have hzn : ‖z‖ ≤ 3/2 := by
    have h := norm_sub_le z x
    have h' := norm_add_le (z-x) x
    rw [sub_add_cancel] at h'
    linarith
  by_cases hdist : ‖x-w‖ ≤ 1
  · rw [min_eq_right hdist]
    have htri : ‖z-w‖ ≤ ‖z-x‖+‖x-w‖ := by
      have he : z-w=(z-x)+(x-w) := by ring
      rw [he]
      exact norm_add_le _ _
    exact (norm_blaschkeFactor_four_le_distance hw hzn).trans
      (htri.trans (by linarith))
  · rw [min_eq_left (le_of_not_ge hdist)]
    exact (norm_blaschkeFactor_le_one (by linarith : ‖w‖ < 4)
      (by simpa using (show ‖z‖ ≤ 4 by linarith))).trans (by linarith)

/-- A local disk bound for the actual exponential sum from its actual
bounded holomorphic quotient. Distances are capped at one, so the same
finite family works at every real point. -/
theorem complexExponentialSum_local_product_bound {n N : ℕ}
    (exponent c : Fin n → ℂ) (roots : Fin N → ℂ) (h : ℂ → ℂ) (M : ℝ)
    (hroots : ∀ j, ‖roots j‖ ≤ 2)
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) 4,
      complexExponentialSum exponent c z=blaschkeProduct 4 roots z*h z)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) 4, ‖h z‖ ≤ M)
    {x : ℂ} (hx : ‖x‖ ≤ 1/2) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {z : ℂ} (hz : z ∈ closedBall x r) :
    ‖complexExponentialSum exponent c z‖ ≤ M*∏ j, (r+min 1 ‖x-roots j‖) := by
  have hzx : ‖z-x‖ ≤ r := by simpa [Metric.mem_closedBall,dist_eq_norm] using hz
  have hzn : ‖z‖ ≤ 4 := by
    have h' := norm_add_le (z-x) x
    rw [sub_add_cancel] at h'
    linarith
  have hz4 : z ∈ closedBall (0 : ℂ) 4 := by simpa using hzn
  rw [hfactor z hz4,norm_mul,blaschkeProduct,norm_prod]
  calc
    _ ≤ (∏ j, ‖blaschkeFactor 4 (roots j) z‖)*M :=
      mul_le_mul_of_nonneg_left (hbound z hz4) (Finset.prod_nonneg fun j _ => norm_nonneg _)
    _ ≤ (∏ j, (r+min 1 ‖x-roots j‖))*M :=
      mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun j _ => norm_nonneg _)
        (fun j _ => norm_blaschkeFactor_four_le_local (hroots j) hx hr hr1 hz))
        ((norm_nonneg _).trans (hbound 0 (by simp)))
    _ = _ := mul_comm _ _

/-- The exact disk-growth degree passes to the capped distance product.
The point `w` is any witness for the outer-to-inner growth ratio. -/
theorem complexExponentialSum_root_scale_growth {n N : ℕ} (hn : 0 < n)
    (exponent c : Fin n → ℂ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hexponent : ∀ j, ‖exponent j‖ ≤ σ)
    (roots : Fin N → ℂ) (h : ℂ → ℂ) {M H₀ : ℝ} (hM : 0 < M)
    (hroots : ∀ j, ‖roots j‖ ≤ 2)
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) 4,
      complexExponentialSum exponent c z=blaschkeProduct 4 roots z*h z)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) 4, ‖h z‖ ≤ M)
    {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hgrowth : M ≤ Real.exp H₀*‖complexExponentialSum exponent c w‖)
    {x : ℂ} (hx : ‖x‖ ≤ 1/2) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Real.exp (-(H₀+2*σ+(n-1 : ℕ)*Real.log (8*Real.exp 1)))*r^(n-1) ≤
      ∏ j, (r+min 1 ‖x-roots j‖) := by
  let A : ℝ := 8*Real.exp 1
  have hA : 0 < A := by dsimp [A]; positivity
  let p : ℝ := ∏ j, (r+min 1 ‖x-roots j‖)
  have hlocal : ∀ z ∈ closedBall x r,
      ‖complexExponentialSum exponent c z‖ ≤ M*p :=
    fun z hz => complexExponentialSum_local_product_bound exponent c roots h M
      hroots hfactor hbound hx hr.le hr1 hz
  have hwx : w ∈ closedBall x 2 := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    exact (norm_sub_le w x).trans (by linarith)
  have hf := complexExponentialSum_disk_norm_le hn exponent c hσ hexponent x hr
    (by linarith : r ≤ 2) hlocal hwx
  have hf' : ‖complexExponentialSum exponent c w‖ ≤
      M*p*Real.exp (2*σ)*(A/r)^(n-1) := by
    simpa only [A,mul_comm σ 2,show 4*Real.exp 1*2=8*Real.exp 1 by ring] using hf
  have hmul := hgrowth.trans (mul_le_mul_of_nonneg_left hf' (Real.exp_nonneg _))
  have hcancel : 1 ≤ Real.exp H₀*(p*Real.exp (2*σ)*(A/r)^(n-1)) := by
    apply (mul_le_mul_iff_of_pos_left hM).mp
    nlinarith only [hmul]
  let H₁ : ℝ := H₀+2*σ+(n-1 : ℕ)*Real.log A
  have he : Real.exp H₁=Real.exp H₀*Real.exp (2*σ)*A^(n-1) := by
    dsimp [H₁]
    rw [Real.exp_add,Real.exp_add,Real.exp_nat_mul,Real.exp_log hA]
  have hid : (Real.exp (-H₁)*r^(n-1)) *
      (Real.exp H₀*Real.exp (2*σ)*(A/r)^(n-1))=1 := by
    rw [Real.exp_neg,he,div_pow]
    field_simp
  calc
    _ = (Real.exp (-H₁)*r^(n-1))*1 := by rw [mul_one]
    _ ≤ (Real.exp (-H₁)*r^(n-1)) *
        (Real.exp H₀*(p*Real.exp (2*σ)*(A/r)^(n-1))) :=
      mul_le_mul_of_nonneg_left hcancel (by positivity)
    _ = p := by
      calc
        _ = p*((Real.exp (-H₁)*r^(n-1)) *
          (Real.exp H₀*Real.exp (2*σ)*(A/r)^(n-1))) := by ring
        _ = p := by rw [hid,mul_one]

/-- The zero-free factor and the explicit rational factors give a lower
bound before effective-degree cancellation. -/
theorem blaschke_factorization_norm_lower {N : ℕ}
    (f h : ℂ → ℂ) (roots : Fin N → ℂ) {M H₀ : ℝ} (hM : 0 < M)
    (hroots : ∀ j, ‖roots j‖ ≤ 2)
    (hh : AnalyticOnNhd ℂ h (ball 0 2))
    (hne : ∀ z ∈ ball (0 : ℂ) 2, h z ≠ 0)
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) 4, f z=blaschkeProduct 4 roots z*h z)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) 4, ‖h z‖ ≤ M)
    {w : ℂ} (hw : ‖w‖ ≤ 1) (hgrowth : M ≤ Real.exp H₀*‖h w‖)
    {x : ℂ} (hx : ‖x‖ ≤ 1/2) :
    M*Real.exp (-52*H₀)*(4/17 : ℝ)^N*(∏ j, min 1 ‖x-roots j‖) ≤ ‖f x‖ := by
  have hsub : ball (0 : ℂ) 2 ⊆ closedBall 0 4 := by
    intro z hz
    simp only [mem_ball,mem_closedBall,dist_zero_right] at *
    linarith
  have hlower := zeroFree_norm_lower_of_growth hh hne hM
    (fun z hz => hbound z (hsub hz)) hw (by linarith : ‖x‖ ≤ 3/2) hgrowth
  have hprod : (4/17 : ℝ)^N*(∏ j, min 1 ‖x-roots j‖) ≤
      ‖blaschkeProduct 4 roots x‖ := by
    have hp := Finset.prod_le_prod (s:=Finset.univ)
      (f:=fun j => (4/17 : ℝ)*min 1 ‖x-roots j‖)
      (g:=fun j => ‖blaschkeFactor 4 (roots j) x‖)
      (fun j _ => mul_nonneg (by norm_num) (le_min (by norm_num) (norm_nonneg _)))
      (fun j _ => norm_blaschkeFactor_four_lower (hroots j) hx)
    simpa only [blaschkeProduct,norm_prod,Finset.prod_mul_distrib,
      Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hp
  have hx4 : x ∈ closedBall (0 : ℂ) 4 := by
    simp only [mem_closedBall,dist_zero_right]
    linarith
  rw [hfactor x hx4,norm_mul]
  calc
    _ = ((4/17 : ℝ)^N*(∏ j, min 1 ‖x-roots j‖))*(M*Real.exp (-52*H₀)) := by ring
    _ ≤ ‖blaschkeProduct 4 roots x‖*‖h x‖ :=
      mul_le_mul hprod hlower (by positivity) (norm_nonneg _)

end
end LeanNumDetect.MultiTuran
