import MultiTuran.Turan.LocalProduct

/-! The actual zero product has effective degree `n-1`. -/

set_option autoImplicit false
open scoped BigOperators
open Set Metric

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- Pointwise lower bound outside the finite root family. All analytic data
refer to the genuine exponential sum and its genuine Blaschke quotient. -/
theorem complexExponentialSum_effective_norm_lower {n N : ℕ} (hn : 0 < n)
    (exponent c : Fin n → ℂ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hexponent : ∀ j, ‖exponent j‖ ≤ σ)
    (roots : Fin N → ℂ) (h : ℂ → ℂ) {M H₀ : ℝ} (hM : 0 < M) (hH₀ : 0 ≤ H₀)
    (hroots : ∀ j, ‖roots j‖ ≤ 2)
    (hh : AnalyticOnNhd ℂ h (closedBall 0 4))
    (hne : ∀ z ∈ ball (0 : ℂ) 2, h z ≠ 0)
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) 4,
      complexExponentialSum exponent c z=blaschkeProduct 4 roots z*h z)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) 4,
      ‖complexExponentialSum exponent c z‖ ≤ ‖h z‖ ∧ ‖h z‖ ≤ M)
    {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hgrowth : M ≤ Real.exp H₀*‖complexExponentialSum exponent c w‖)
    {x : ℝ} (hx : x ∈ Icc (-1/2 : ℝ) (1/2))
    (hroot : ∀ j, (x : ℂ) ≠ roots j) :
    M*Real.exp (-(52*H₀+(H₀+2*σ+(n-1 : ℕ)*Real.log (8*Real.exp 1))+
      N*Real.log (17/2 : ℝ)))*Real.exp (-effectiveLogPotential (n-1) roots x) ≤
      ‖complexExponentialSum exponent c (x : ℂ)‖ := by
  let H₁ : ℝ := H₀+2*σ+(n-1 : ℕ)*Real.log (8*Real.exp 1)
  have hlogA : 0 ≤ Real.log (8*Real.exp 1) := by
    apply Real.log_nonneg
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have hH₁ : 0 ≤ H₁ := by dsimp [H₁]; positivity
  have hxnorm : ‖(x : ℂ)‖ ≤ 1/2 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hx.1],hx.2⟩
  have hscale : ∀ r : ℝ, 0 < r → r ≤ 1 →
      Real.exp (-H₁)*r^(n-1) ≤ ∏ j, (r+min 1 ‖(x : ℂ)-roots j‖) := by
    intro r hr hr1
    exact complexExponentialSum_root_scale_growth hn exponent c hσ hexponent roots h hM
      hroots hfactor (fun z hz => (hbound z hz).2) hw hgrowth hxnorm hr hr1
  have hp := rootProduct_lower_of_scale_growth (n-1) roots x H₁ hH₁ hroot hscale
  have hw4 : w ∈ closedBall (0 : ℂ) 4 := by
    simp only [mem_closedBall,dist_zero_right]
    linarith
  have hgrowthh := hgrowth.trans (mul_le_mul_of_nonneg_left (hbound w hw4).1 (Real.exp_nonneg _))
  have hsub : ball (0 : ℂ) 2 ⊆ closedBall 0 4 := by
    intro z hz
    exact closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hz)
  have hlow := blaschke_factorization_norm_lower (complexExponentialSum exponent c) h roots hM
    hroots (hh.mono hsub) hne hfactor (fun z hz => (hbound z hz).2) hw hgrowthh hxnorm
  have heN : Real.exp (-((N : ℝ)*Real.log (17/2 : ℝ)))=(2/17 : ℝ)^N := by
    rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<17/2)]
    rw [← inv_pow]
    norm_num
  have he : Real.exp (-(52*H₀+H₁+N*Real.log (17/2 : ℝ)))=
      Real.exp (-52*H₀)*(4/17 : ℝ)^N*(Real.exp (-H₁)/(2 : ℝ)^N) := by
    rw [neg_add,neg_add,Real.exp_add,Real.exp_add,heN]
    have hpowers : (2/17 : ℝ)^N=(4/17 : ℝ)^N/(2 : ℝ)^N := by
      rw [← div_pow]
      norm_num
    rw [hpowers]
    simp only [neg_mul]
    ring
  calc
    _ = M*Real.exp (-52*H₀)*(4/17 : ℝ)^N*
        ((Real.exp (-H₁)/(2 : ℝ)^N)*Real.exp (-effectiveLogPotential (n-1) roots x)) := by
      rw [he]
      ring
    _ ≤ M*Real.exp (-52*H₀)*(4/17 : ℝ)^N*(∏ j, min 1 ‖(x : ℂ)-roots j‖) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := hlow

/-- Taking logarithms is legitimate outside the actual finite zero set. -/
theorem complexExponentialSum_effective_log_lower {n N : ℕ} (hn : 0 < n)
    (exponent c : Fin n → ℂ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hexponent : ∀ j, ‖exponent j‖ ≤ σ)
    (roots : Fin N → ℂ) (h : ℂ → ℂ) {M H₀ : ℝ} (hM : 0 < M) (hH₀ : 0 ≤ H₀)
    (hroots : ∀ j, ‖roots j‖ ≤ 2)
    (hh : AnalyticOnNhd ℂ h (closedBall 0 4))
    (hne : ∀ z ∈ ball (0 : ℂ) 2, h z ≠ 0)
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) 4,
      complexExponentialSum exponent c z=blaschkeProduct 4 roots z*h z)
    (hbound : ∀ z ∈ closedBall (0 : ℂ) 4,
      ‖complexExponentialSum exponent c z‖ ≤ ‖h z‖ ∧ ‖h z‖ ≤ M)
    {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hgrowth : M ≤ Real.exp H₀*‖complexExponentialSum exponent c w‖)
    {x : ℝ} (hx : x ∈ Icc (-1/2 : ℝ) (1/2))
    (hroot : ∀ j, (x : ℂ) ≠ roots j) :
    Real.log M-(52*H₀+(H₀+2*σ+(n-1 : ℕ)*Real.log (8*Real.exp 1))+
      N*Real.log (17/2 : ℝ))-effectiveLogPotential (n-1) roots x ≤
      Real.log ‖complexExponentialSum exponent c (x : ℂ)‖ := by
  have hlow := complexExponentialSum_effective_norm_lower hn exponent c hσ hexponent roots h hM
    hH₀ hroots hh hne hfactor hbound hw hgrowth hx hroot
  have hleft : 0 < M*Real.exp (-(52*H₀+(H₀+2*σ+(n-1 : ℕ)*Real.log (8*Real.exp 1))+
      N*Real.log (17/2 : ℝ)))*Real.exp (-effectiveLogPotential (n-1) roots x) := by positivity
  have hl := Real.log_le_log hleft hlow
  rw [Real.log_mul (mul_pos hM (Real.exp_pos _)).ne' (Real.exp_ne_zero _),
    Real.log_mul hM.ne' (Real.exp_ne_zero _),Real.log_exp,Real.log_exp] at hl
  linarith

end
end LeanNumDetect.MultiTuran
