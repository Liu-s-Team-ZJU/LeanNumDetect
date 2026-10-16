import MultiTuran.Turan.BlaschkeFactors

/-! # Removing actual finite zero multisets

The multiplicity condition is expressed using the genuine meromorphic
order. Conversion to meromorphic normal form fills precisely the removable
singularities, yielding an actual holomorphic quotient and pointwise identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology
open Set Metric Filter

namespace LeanNumDetect.MultiTuran
noncomputable section

def zeroMultiplicity {N : ℕ} (roots : Fin N → ℂ) (z : ℂ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => roots i=z)).card

theorem zeroPolynomial_meromorphicOrder {N : ℕ} (roots : Fin N → ℂ) (z : ℂ) :
    meromorphicOrderAt (zeroPolynomial roots) z =
      (zeroMultiplicity roots z : WithTop ℤ) := by
  classical
  unfold zeroPolynomial
  rw [meromorphicOrderAt_fun_prod (fun i _ => by fun_prop)]
  have hterm (i : Fin N) : meromorphicOrderAt (fun u : ℂ => u-roots i) z =
      if roots i=z then (1 : WithTop ℤ) else 0 := by
    by_cases hi : roots i=z
    · simp only [hi, if_true, meromorphicOrderAt_id_sub_const]
    · rw [if_neg hi]
      have ha : AnalyticAt ℂ (fun u : ℂ => u-roots i) z := by fun_prop
      exact ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hi))
  simp_rw [hterm]
  simp [zeroMultiplicity, Finset.sum_ite]

/-- Any selected finite multiset of actual zeros, with multiplicity at most
the genuine order, has a genuine holomorphic polynomial quotient. -/
theorem exists_analytic_zeroPolynomial_factor {N : ℕ} {roots : Fin N → ℂ}
    {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (horder : ∀ z ∈ U,
      (zeroMultiplicity roots z : WithTop ℤ) ≤ meromorphicOrderAt f z) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      ∀ z ∈ U, f z = zeroPolynomial roots z*g z := by
  let P : ℂ → ℂ := zeroPolynomial roots
  have hP : ∀ z, AnalyticAt ℂ P z := fun z => analyticOnNhd_zeroPolynomial roots z (Set.mem_univ z)
  let F : ℂ → ℂ := fun z => f z/P z
  have hF : MeromorphicOn F U := hf.meromorphicOn.div (fun z _ => (hP z).meromorphicAt)
  let g : ℂ → ℂ := toMeromorphicNFOn F U
  have hgnf : MeromorphicNFOn g U := meromorphicNFOn_toMeromorphicNFOn F U
  have hg : AnalyticOnNhd ℂ g U := by
    intro z hz
    apply (hgnf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hF hz,
      fun_meromorphicOrderAt_div (hf z hz).meromorphicAt (hP z).meromorphicAt]
    change 0 ≤ meromorphicOrderAt f z-meromorphicOrderAt (zeroPolynomial roots) z
    rw [zeroPolynomial_meromorphicOrder]
    have ho := horder z hz
    by_cases ht : meromorphicOrderAt f z = ⊤
    · simp [ht]
    · lift meromorphicOrderAt f z to ℤ using ht with k hk
      norm_cast at ho ⊢
      exact sub_nonneg.mpr ho
  refine ⟨g,hg,?_⟩
  intro z hz
  have hpne : meromorphicOrderAt P z ≠ ⊤ := by
    rw [zeroPolynomial_meromorphicOrder]
    simp
  have hpEventually := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hP z).meromorphicAt).mp hpne
  have hgeq := hF.toMeromorphicNFOn_eq_self_on_nhdsNE hz
  have heq : f =ᶠ[𝓝[≠] z] fun w => P w*g w := by
    filter_upwards [hpEventually,hgeq] with w hp hw
    change g w = f w/P w at hw
    rw [hw]
    field_simp [hp]
  exact tendsto_nhds_unique_of_eventuallyEq (hf z hz).continuousAt.continuousWithinAt
    ((hP z).continuousAt.mul (hg z hz).continuousAt).continuousWithinAt heq

/-- The bounded holomorphic partial Blaschke quotient is constructed from
actual selected zeros and their genuine multiplicities. -/
theorem exists_blaschke_factor_of_zero_multiplicities {N : ℕ} {R M : ℝ}
    (hR : 0 < R) {roots : Fin N → ℂ} (hroots : ∀ i, ‖roots i‖ < R)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (horder : ∀ z ∈ closedBall (0 : ℂ) R,
      (zeroMultiplicity roots z : WithTop ℤ) ≤ meromorphicOrderAt f z)
    (hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 R) ∧
      (∀ z ∈ closedBall (0 : ℂ) R, f z = blaschkeProduct R roots z*h z) ∧
      (∀ z ∈ sphere (0 : ℂ) R, ‖h z‖ = ‖f z‖) ∧
      (∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ ‖h z‖) ∧
      (∀ z ∈ closedBall (0 : ℂ) R, ‖h z‖ ≤ M) := by
  obtain ⟨g,hg,hfactor⟩ := exists_analytic_zeroPolynomial_factor hf horder
  exact exists_blaschke_factor_of_polynomial_factor hR hroots hg hfactor hbound

end
end LeanNumDetect.MultiTuran
