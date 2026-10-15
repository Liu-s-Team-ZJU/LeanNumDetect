import MultiTuran.TuranBlaschkeZeros

/-! # Complete zero extraction and a bounded zero-free Blaschke quotient -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology
open Set Metric Filter

namespace LeanNumDetect.MultiTuran
noncomputable section

theorem exists_complete_zeroPolynomial_factor {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 4)) {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hfw : f w ≠ 0) :
    ∃ N : ℕ, ∃ roots : Fin N → ℂ, ∃ g : ℂ → ℂ,
      (∀ i, ‖roots i‖ ≤ 2) ∧
      (∀ z ∈ closedBall (0 : ℂ) 4,
        (zeroMultiplicity roots z : WithTop ℤ) ≤ meromorphicOrderAt f z) ∧
      (∀ z ∈ closedBall (0 : ℂ) 2,
        (zeroMultiplicity roots z : WithTop ℤ) = meromorphicOrderAt f z) ∧
      AnalyticOnNhd ℂ g (closedBall 0 4) ∧
      (∀ z ∈ closedBall (0 : ℂ) 4, f z = zeroPolynomial roots z*g z) ∧
      (∀ z ∈ closedBall (0 : ℂ) 2, g z ≠ 0) := by
  classical
  have hw4 : w ∈ closedBall (0 : ℂ) 4 := by
    simp only [mem_closedBall,dist_zero_right]
    linarith
  have hfinite : ∀ z ∈ closedBall (0 : ℂ) 4, meromorphicOrderAt f z ≠ ⊤ := by
    apply (hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall_mem
      (Metric.isConnected_closedBall (by norm_num : (0 : ℝ) ≤ 4))).mp
    refine ⟨w,hw4,?_⟩
    rw [(hf w hw4).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfw]
    simp
  have hsubset : closedBall (0 : ℂ) 2 ⊆ closedBall 0 4 :=
    closedBall_subset_closedBall (by norm_num)
  have hf2 := hf.mono hsubset
  let D := MeromorphicOn.divisor f (closedBall (0 : ℂ) 2)
  let m : ℂ → ℕ := fun z => (D z).toNat
  have hDnonneg (z : ℂ) : 0 ≤ D z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf2 z
  have hmfinite : (Function.support m).Finite := by
    apply ((D).finiteSupport (isCompact_closedBall 0 2)).subset
    intro z hz
    intro hzD
    have hDz : D z = 0 := by simpa only [Function.mem_support,not_not] using hzD
    exact hz (by simp [m,hDz])
  obtain ⟨N,roots,hcount⟩ := exists_roots_of_finite_multiplicity m hmfinite
  have hcast (z : ℂ) : (zeroMultiplicity roots z : ℤ) = D z := by
    rw [hcount]
    exact Int.toNat_of_nonneg (hDnonneg z)
  have heq : ∀ z ∈ closedBall (0 : ℂ) 2,
      (zeroMultiplicity roots z : WithTop ℤ) = meromorphicOrderAt f z := by
    intro z hz
    have hd : (D z : WithTop ℤ) = meromorphicOrderAt f z := by
      dsimp [D]
      rw [MeromorphicOn.divisor_apply hf2.meromorphicOn hz]
      exact WithTop.coe_untop₀_of_ne_top (hfinite z (hsubset hz))
    exact (congrArg (fun k : ℤ => (k : WithTop ℤ)) (hcast z)).trans hd
  have horder : ∀ z ∈ closedBall (0 : ℂ) 4,
      (zeroMultiplicity roots z : WithTop ℤ) ≤ meromorphicOrderAt f z := by
    intro z hz
    by_cases hz2 : z ∈ closedBall (0 : ℂ) 2
    · exact (heq z hz2).le
    · have hmzero : zeroMultiplicity roots z = 0 := by
        rw [hcount]
        simp [m,D,Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz2]
      rw [hmzero,Nat.cast_zero]
      exact (hf z hz).meromorphicOrderAt_nonneg
  have hroots : ∀ i, ‖roots i‖ ≤ 2 := by
    intro i
    have hpos := zeroMultiplicity_pos_at_root roots i
    have hDne : D (roots i) ≠ 0 := by
      intro hd
      rw [hcount] at hpos
      simp [m,hd] at hpos
    have hmem : roots i ∈ closedBall (0 : ℂ) 2 := D.supportWithinDomain hDne
    simpa only [mem_closedBall,dist_zero_right] using hmem
  obtain ⟨g,hg,hfactor⟩ := exists_analytic_zeroPolynomial_factor hf horder
  refine ⟨N,roots,g,hroots,horder,heq,hg,hfactor,?_⟩
  intro z hz
  have hz4 := hsubset hz
  have hzball4 : z ∈ ball (0 : ℂ) 4 := by
    have hnz : ‖z‖ ≤ 2 := by simpa using hz
    simp only [mem_ball,dist_zero_right]
    linarith
  have hlocal : f =ᶠ[𝓝 z] fun u => zeroPolynomial roots u*g u := by
    filter_upwards [closedBall_mem_nhds_of_mem hzball4] with u hu
    exact hfactor u hu
  have hprod := meromorphicOrderAt_congr (hlocal.filter_mono nhdsWithin_le_nhds)
  rw [fun_meromorphicOrderAt_mul (analyticOnNhd_zeroPolynomial roots z (mem_univ z)).meromorphicAt
    (hg z hz4).meromorphicAt, zeroPolynomial_meromorphicOrder, heq z hz] at hprod
  have hgorder : meromorphicOrderAt g z = 0 := by
    by_cases ht : meromorphicOrderAt g z = ⊤
    · rw [ht,add_top] at hprod
      exact False.elim (hfinite z hz4 hprod)
    · lift meromorphicOrderAt f z to ℤ using hfinite z hz4 with k hk
      lift meromorphicOrderAt g z to ℤ using ht with l hl
      norm_cast at hprod
      have hlzero : l = 0 := by omega
      simp [hlzero]
  exact (hg z hz4).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp hgorder

/-- All zeros in the radius-two disk are removed with their actual
multiplicities. The remaining factor is genuinely holomorphic, bounded by
the same outer maximum, zero-free on the inner disk, and dominates `f`.
Its actual number of removed zeros satisfies the proved growth count. -/
theorem exists_bounded_zeroFree_blaschke_factor {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 4)) {M S : ℝ} (hM : 0 < M)
    (hbound : ∀ z ∈ sphere (0 : ℂ) 4, ‖f z‖ ≤ M) {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hgrowth : M ≤ Real.exp S*‖f w‖) :
    ∃ N : ℕ, ∃ roots : Fin N → ℂ, ∃ h : ℂ → ℂ,
      (∀ i, ‖roots i‖ ≤ 2) ∧ (N : ℝ) ≤ 7*S ∧
      (∀ z ∈ closedBall (0 : ℂ) 4,
        (zeroMultiplicity roots z : WithTop ℤ) ≤ meromorphicOrderAt f z) ∧
      AnalyticOnNhd ℂ h (closedBall 0 4) ∧
      (∀ z ∈ ball (0 : ℂ) 2, h z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) 4, f z = blaschkeProduct 4 roots z*h z) ∧
      (∀ z ∈ sphere (0 : ℂ) 4, ‖h z‖ = ‖f z‖) ∧
      (∀ z ∈ closedBall (0 : ℂ) 4, ‖f z‖ ≤ ‖h z‖ ∧ ‖h z‖ ≤ M) := by
  have hfw : f w ≠ 0 := by
    intro he
    rw [he,norm_zero,mul_zero] at hgrowth
    exact (not_le_of_gt hM) hgrowth
  obtain ⟨N,roots,g,hroots,horder,_heq,hg,hfactor,hgne⟩ :=
    exists_complete_zeroPolynomial_factor hf hw hfw
  have hroots4 : ∀ i, ‖roots i‖ < (4 : ℝ) := fun i => (hroots i).trans_lt (by norm_num)
  let h : ℂ → ℂ := fun z => blaschkeCofactor 4 roots z*g z
  have han : AnalyticOnNhd ℂ h (closedBall 0 4) :=
    ((analyticOnNhd_blaschkeCofactor 4 roots).mono (Set.subset_univ _)).mul hg
  have hfact : ∀ z ∈ closedBall (0 : ℂ) 4, f z = blaschkeProduct 4 roots z*h z := by
    intro z hz
    rw [hfactor z hz,zeroPolynomial_eq_blaschke_mul_cofactor (by norm_num) hroots4 hz]
    dsimp [h]
    ring
  have hcircle : ∀ z ∈ sphere (0 : ℂ) 4, ‖h z‖ = ‖f z‖ := by
    intro z hz
    have he := congrArg norm (hfact z (sphere_subset_closedBall hz)).symm
    rw [norm_mul,norm_blaschkeProduct_on_sphere hroots4 hz,one_mul] at he
    exact he
  refine ⟨N,roots,h,hroots,selected_zero_count_le_of_growth hroots hf horder hM hbound hw hgrowth,
    horder,han,?_,hfact,hcircle,?_⟩
  · intro z hz
    have hz2 := ball_subset_closedBall hz
    have hz4 : z ∈ closedBall (0 : ℂ) 4 :=
      closedBall_subset_closedBall (by norm_num) hz2
    exact mul_ne_zero (blaschkeCofactor_ne_zero (by norm_num) hroots4 hz4) (hgne z hz2)
  · intro z hz
    constructor
    · rw [hfact z hz,norm_mul]
      simpa using mul_le_mul_of_nonneg_right (norm_blaschkeProduct_le_one hroots4 hz) (norm_nonneg (h z))
    · exact analytic_norm_le_of_sphere_bound han
        (fun u hu => (hcircle u hu).trans_le (hbound u hu)) hz

end
end LeanNumDetect.MultiTuran
