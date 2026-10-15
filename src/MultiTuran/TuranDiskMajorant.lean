import MultiTuran.TuranEffectiveLower
import MultiTuran.TuranBlaschkeExtraction
import MultiTuran.TuranGeometricBound

/-! Genuine disk maxima, zero extraction and logarithmic majorants for
finite exponential sums. No Remez comparison is a hypothesis here. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology
open Set Metric MeasureTheory Filter

namespace LeanNumDetect.MultiTuran
noncomputable section

def turanDiskGrowthBudget (n : ℕ) (σ : ℝ) : ℝ :=
  4*σ+(n-1 : ℕ)*Real.log (16*Real.exp 1)

def turanRootError (n : ℕ) (σ : ℝ) (N : ℕ) : ℝ :=
  52*turanDiskGrowthBudget n σ+
    (turanDiskGrowthBudget n σ+2*σ+(n-1 : ℕ)*Real.log (8*Real.exp 1))+
    N*Real.log (17/2 : ℝ)

theorem turanDiskGrowthBudget_nonneg (n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    0 ≤ turanDiskGrowthBudget n σ := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hl : 0 ≤ Real.log (16*Real.exp 1) := Real.log_nonneg (by linarith)
  dsimp [turanDiskGrowthBudget]
  positivity

theorem analyticOnNhd_complexExponentialSum {n : ℕ} (exponent c : Fin n → ℂ) :
    AnalyticOnNhd ℂ (complexExponentialSum exponent c) univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_complexExponentialSum exponent c)

/-- An actual entire exponential sum has a positive inner-disk maximum
unless its real restriction is identically zero. -/
theorem complexExponentialSum_exists_disk_growth_data {n : ℕ} (hn : 0 < n)
    (exponent c : Fin n → ℂ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hexponent : ∀ j, ‖exponent j‖ ≤ σ)
    (hzero : (fun x : ℝ => complexExponentialSum exponent c (x : ℂ)) ≠ 0) :
    ∃ M : ℝ, ∃ w : ℂ, 0 < M ∧ ‖w‖ ≤ 1 ∧
      (∀ z ∈ closedBall (0 : ℂ) 4, ‖complexExponentialSum exponent c z‖ ≤ M) ∧
      M ≤ Real.exp (turanDiskGrowthBudget n σ)*‖complexExponentialSum exponent c w‖ := by
  let f := complexExponentialSum exponent c
  have hf := analyticOnNhd_complexExponentialSum exponent c
  obtain ⟨w,hw,hwmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn
    (by exact ⟨0,by simp⟩) (hf.continuousOn.norm.mono (subset_univ _))
  have hwpos : 0 < ‖f w‖ := by
    by_contra hpos
    have hwzero : ‖f w‖=0 := le_antisymm (le_of_not_gt hpos) (norm_nonneg _)
    have hball : Set.EqOn f 0 (closedBall (0 : ℂ) 1) := by
      intro z hz
      have hle : ‖f z‖ ≤ ‖f w‖ := hwmax hz
      exact norm_eq_zero.mp (le_antisymm (by rwa [hwzero] at hle) (norm_nonneg _))
    have hloc : f =ᶠ[𝓝 (0 : ℂ)] 0 := hball.eventuallyEq_of_mem
      (closedBall_mem_nhds_of_mem (by simp : (0 : ℂ) ∈ ball 0 1))
    have hfzero : f=0 := hf.eq_of_eventuallyEq (fun z _ => analyticAt_const) hloc
    apply hzero
    funext x
    exact congrFun hfzero (x : ℂ)
  let M := ‖f w‖*Real.exp (turanDiskGrowthBudget n σ)
  have he : Real.exp (turanDiskGrowthBudget n σ)=
      Real.exp (σ*4)*(16*Real.exp 1)^(n-1) := by
    rw [turanDiskGrowthBudget,Real.exp_add,Real.exp_nat_mul,
      Real.exp_log (by positivity : (0:ℝ)<16*Real.exp 1),mul_comm σ 4]
  refine ⟨M,w,mul_pos hwpos (Real.exp_pos _),by simpa using hw,?_,?_⟩
  · intro z hz
    have h := complexExponentialSum_disk_norm_le hn exponent c hσ hexponent 0
      (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)≤4)
      (fun u hu => hwmax hu) hz
    dsimp only [M]
    rw [he]
    simpa only [div_one,show 4*Real.exp 1*4=16*Real.exp 1 by ring,mul_assoc] using h
  · dsimp only [M]
    exact le_of_eq (mul_comm _ _)

/-- Actual finite roots and a literal integrable effective potential give
a logarithmic lower bound throughout the unit real interval off the roots. -/
theorem complexExponentialSum_exists_logMajorant {n : ℕ} (hn : 0 < n)
    (exponent c : Fin n → ℂ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hexponent : ∀ j, ‖exponent j‖ ≤ σ)
    (hzero : (fun x : ℝ => complexExponentialSum exponent c (x : ℂ)) ≠ 0) :
    ∃ N : ℕ, ∃ roots : Fin N → ℂ, ∃ M : ℝ, 0 < M ∧
      (N : ℝ) ≤ 7*turanDiskGrowthBudget n σ ∧
      (∀ x ∈ Icc (-1/2 : ℝ) (1/2), ‖complexExponentialSum exponent c (x : ℂ)‖ ≤ M) ∧
      (∀ x ∈ Icc (-1/2 : ℝ) (1/2), (∀ j, (x : ℂ) ≠ roots j) →
        complexExponentialSum exponent c (x : ℂ) ≠ 0 ∧
        Real.log M-turanRootError n σ N-effectiveLogPotential (n-1) roots x ≤
          Real.log ‖complexExponentialSum exponent c (x : ℂ)‖) := by
  obtain ⟨M,w,hM,hw,hbound,hgrowth⟩ :=
    complexExponentialSum_exists_disk_growth_data hn exponent c hσ hexponent hzero
  have hf : AnalyticOnNhd ℂ (complexExponentialSum exponent c) (closedBall 0 4) :=
    (analyticOnNhd_complexExponentialSum exponent c).mono (subset_univ _)
  obtain ⟨N,roots,h,hroots,hN,_horder,hh,hne,hfactor,_hcircle,hbounds⟩ :=
    exists_bounded_zeroFree_blaschke_factor hf hM
      (fun z hz => hbound z (sphere_subset_closedBall hz)) hw hgrowth
  refine ⟨N,roots,M,hM,hN,?_,?_⟩
  · intro x hx
    apply hbound
    simp only [mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    exact (abs_le.mpr ⟨by linarith [hx.1],hx.2⟩).trans (by norm_num)
  · intro x hx hroot
    have hlower := complexExponentialSum_effective_norm_lower hn exponent c hσ hexponent roots h hM
      (turanDiskGrowthBudget_nonneg n hσ) hroots hh hne hfactor hbounds hw hgrowth hx hroot
    have hnonzero : complexExponentialSum exponent c (x : ℂ) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hlower)
    refine ⟨hnonzero,?_⟩
    exact complexExponentialSum_effective_log_lower hn exponent c hσ hexponent roots h hM
      (turanDiskGrowthBudget_nonneg n hσ) hroots hh hne hfactor hbounds hw hgrowth hx hroot

end
end LeanNumDetect.MultiTuran
