import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Tactic

/-! # Finite Blaschke factors and the maximum principle

The factors are explicit rational functions. Their circle modulus is one,
and all comparisons concern genuine holomorphic functions on actual disks.
-/

set_option autoImplicit false
open scoped BigOperators ComplexConjugate
open Set Metric

namespace LeanNumDetect.MultiTuran
noncomputable section

def blaschkeFactor (R : ℝ) (w z : ℂ) : ℂ :=
  (R : ℂ)*(z-w)/((R : ℂ)^2-conj w*z)

def blaschkeProduct {N : ℕ} (R : ℝ) (roots : Fin N → ℂ) (z : ℂ) : ℂ :=
  ∏ i, blaschkeFactor R (roots i) z

def zeroPolynomial {N : ℕ} (roots : Fin N → ℂ) (z : ℂ) : ℂ :=
  ∏ i, (z-roots i)

def blaschkeCofactor {N : ℕ} (R : ℝ) (roots : Fin N → ℂ) (z : ℂ) : ℂ :=
  ∏ i, ((R : ℂ)^2-conj (roots i)*z)/(R : ℂ)

theorem blaschke_denominator_ne_zero {R : ℝ} {w z : ℂ}
    (hw : ‖w‖ < R) (hz : ‖z‖ ≤ R) : (R : ℂ)^2-conj w*z ≠ 0 := by
  have hR : 0 < R := (norm_nonneg w).trans_lt hw
  have hlt : ‖conj w*z‖ < R^2 := by
    calc
      _ = ‖w‖*‖z‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ‖w‖*R := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ < R*R := mul_lt_mul_of_pos_right hw hR
      _ = _ := by ring
  have hnorm : ‖(R : ℂ)^2‖ = R^2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  intro he
  rw [← sub_eq_zero.mp he, hnorm] at hlt
  exact (lt_irrefl _ hlt)

theorem analyticOnNhd_blaschkeFactor {R : ℝ} {w : ℂ} (hw : ‖w‖ < R) :
    AnalyticOnNhd ℂ (blaschkeFactor R w) (closedBall 0 R) := by
  intro z hz
  have hz' : ‖z‖ ≤ R := by simpa using hz
  unfold blaschkeFactor
  exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => (R : ℂ)*(z-w)) z).div
    (by fun_prop) (blaschke_denominator_ne_zero hw hz')

theorem blaschkeFactor_eq_inv_canonical (R : ℝ) (w z : ℂ) :
    blaschkeFactor R w z = (Complex.canonicalFactor R w z)⁻¹ := by
  rw [blaschkeFactor, Complex.canonicalFactor_apply, inv_div]

theorem norm_blaschkeFactor_on_sphere {R : ℝ} {w z : ℂ}
    (hw : ‖w‖ < R) (hz : z ∈ sphere 0 R) : ‖blaschkeFactor R w z‖ = 1 := by
  rw [blaschkeFactor_eq_inv_canonical, norm_inv,
    Complex.norm_canonicalFactor_eval_circle_eq_one (by simpa using hw) hz, inv_one]

/-- The usual maximum modulus principle, packaged for a literal disk. -/
theorem analytic_norm_le_of_sphere_bound {f : ℂ → ℂ} {R M : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall 0 R) : ‖f z‖ ≤ M := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_closedBall
    (isClosed_closedBall.diffContOnCl_iff.mpr hf.differentiableOn)
    (fun w hw => hbound w (frontier_closedBall_subset_sphere hw))
  simpa only [isClosed_closedBall.closure_eq] using hz

theorem norm_blaschkeFactor_le_one {R : ℝ} {w z : ℂ}
    (hw : ‖w‖ < R) (hz : z ∈ closedBall 0 R) : ‖blaschkeFactor R w z‖ ≤ 1 :=
  analytic_norm_le_of_sphere_bound (analyticOnNhd_blaschkeFactor hw)
    (fun _ h => (norm_blaschkeFactor_on_sphere hw h).le) hz

/-- Explicit local factor bound, the ingredient used with an ordered list
of distances to zeros. -/
theorem norm_blaschkeFactor_le {R s ρ : ℝ} {w z : ℂ}
    (hR : 0 < R) (hw : ‖w‖ ≤ s) (hz : ‖z‖ ≤ ρ)
    (hden : 0 < R^2-s*ρ) :
    ‖blaschkeFactor R w z‖ ≤ R*(s+ρ)/(R^2-s*ρ) := by
  have hs : 0 ≤ s := (norm_nonneg _).trans hw
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hz
  have hnormR : ‖(R : ℂ)‖ = R := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hnum : ‖(R : ℂ)*(z-w)‖ ≤ R*(s+ρ) := by
    rw [norm_mul, hnormR]
    apply mul_le_mul_of_nonneg_left _ hR.le
    exact (norm_sub_le z w).trans (by linarith)
  have hprod : ‖conj w*z‖ ≤ s*ρ := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hw hz (norm_nonneg _) hs
  have hnormpow : ‖(R : ℂ)^2‖ = R^2 := by rw [norm_pow, hnormR]
  have hlower : R^2-s*ρ ≤ ‖(R : ℂ)^2-conj w*z‖ := by
    have h := norm_sub_norm_le ((R : ℂ)^2) (conj w*z)
    rw [hnormpow] at h
    linarith
  rw [blaschkeFactor, norm_div]
  apply div_le_div₀ (by positivity) hnum hden hlower

theorem analyticOnNhd_zeroPolynomial {N : ℕ} (roots : Fin N → ℂ) :
    AnalyticOnNhd ℂ (zeroPolynomial roots) Set.univ := by
  intro z _
  unfold zeroPolynomial
  fun_prop

theorem analyticOnNhd_blaschkeCofactor {N : ℕ} (R : ℝ) (roots : Fin N → ℂ) :
    AnalyticOnNhd ℂ (blaschkeCofactor R roots) Set.univ := by
  intro z _
  unfold blaschkeCofactor
  fun_prop

theorem blaschkeCofactor_ne_zero {N : ℕ} {R : ℝ} (hR : 0 < R)
    {roots : Fin N → ℂ} (hroots : ∀ i, ‖roots i‖ < R)
    {z : ℂ} (hz : z ∈ closedBall 0 R) : blaschkeCofactor R roots z ≠ 0 := by
  unfold blaschkeCofactor
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact div_ne_zero (blaschke_denominator_ne_zero (hroots i) (by simpa using hz))
    (Complex.ofReal_ne_zero.mpr hR.ne')

theorem analyticOnNhd_blaschkeProduct {N : ℕ} {R : ℝ} {roots : Fin N → ℂ}
    (hroots : ∀ i, ‖roots i‖ < R) :
    AnalyticOnNhd ℂ (blaschkeProduct R roots) (closedBall 0 R) := by
  intro z hz
  unfold blaschkeProduct
  apply Finset.analyticAt_fun_prod
  intro i _
  exact analyticOnNhd_blaschkeFactor (hroots i) z hz

theorem norm_blaschkeProduct_on_sphere {N : ℕ} {R : ℝ} {roots : Fin N → ℂ}
    (hroots : ∀ i, ‖roots i‖ < R) {z : ℂ} (hz : z ∈ sphere 0 R) :
    ‖blaschkeProduct R roots z‖ = 1 := by
  unfold blaschkeProduct
  rw [norm_prod]
  simp only [norm_blaschkeFactor_on_sphere (hroots _) hz, Finset.prod_const_one]

theorem norm_blaschkeProduct_le_one {N : ℕ} {R : ℝ} {roots : Fin N → ℂ}
    (hroots : ∀ i, ‖roots i‖ < R) {z : ℂ} (hz : z ∈ closedBall 0 R) :
    ‖blaschkeProduct R roots z‖ ≤ 1 :=
  analytic_norm_le_of_sphere_bound (analyticOnNhd_blaschkeProduct hroots)
    (fun _ h => (norm_blaschkeProduct_on_sphere hroots h).le) hz

theorem zeroPolynomial_eq_blaschke_mul_cofactor {N : ℕ} {R : ℝ}
    (hR : 0 < R) {roots : Fin N → ℂ} (hroots : ∀ i, ‖roots i‖ < R)
    {z : ℂ} (hz : z ∈ closedBall 0 R) :
    zeroPolynomial roots z = blaschkeProduct R roots z*blaschkeCofactor R roots z := by
  unfold zeroPolynomial blaschkeProduct blaschkeCofactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hden := blaschke_denominator_ne_zero (hroots i) (by simpa using hz)
  have hden' : (R : ℂ)^2-z*conj (roots i) ≠ 0 := by simpa [mul_comm] using hden
  unfold blaschkeFactor
  field_simp [hden, hden', Complex.ofReal_ne_zero.mpr hR.ne']

/-- Dividing an actual polynomial zero factor and replacing it by its
Blaschke factor preserves boundary modulus and gives the genuine bounded
holomorphic quotient inside the disk. -/
theorem exists_blaschke_factor_of_polynomial_factor {N : ℕ} {R M : ℝ}
    (hR : 0 < R) {roots : Fin N → ℂ} (hroots : ∀ i, ‖roots i‖ < R)
    {f g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) R, f z = zeroPolynomial roots z*g z)
    (hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (closedBall 0 R) ∧
      (∀ z ∈ closedBall (0 : ℂ) R, f z = blaschkeProduct R roots z*h z) ∧
      (∀ z ∈ sphere (0 : ℂ) R, ‖h z‖ = ‖f z‖) ∧
      (∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ ‖h z‖) ∧
      (∀ z ∈ closedBall (0 : ℂ) R, ‖h z‖ ≤ M) := by
  let h : ℂ → ℂ := fun z => blaschkeCofactor R roots z*g z
  have han : AnalyticOnNhd ℂ h (closedBall 0 R) :=
    ((analyticOnNhd_blaschkeCofactor R roots).mono (Set.subset_univ _)).mul hg
  have hfact : ∀ z ∈ closedBall (0 : ℂ) R, f z = blaschkeProduct R roots z*h z := by
    intro z hz
    rw [hfactor z hz, zeroPolynomial_eq_blaschke_mul_cofactor hR hroots hz]
    dsimp [h]
    ring
  have hcircle : ∀ z ∈ sphere (0 : ℂ) R, ‖h z‖ = ‖f z‖ := by
    intro z hz
    have he := congrArg norm (hfact z (sphere_subset_closedBall hz)).symm
    rw [norm_mul, norm_blaschkeProduct_on_sphere hroots hz, one_mul] at he
    exact he
  refine ⟨h,han,hfact,hcircle,?_,?_⟩
  · intro z hz
    rw [hfact z hz,norm_mul]
    simpa using mul_le_mul_of_nonneg_right (norm_blaschkeProduct_le_one hroots hz) (norm_nonneg (h z))
  · exact fun z hz => analytic_norm_le_of_sphere_bound han
      (fun w hw => (hcircle w hw).trans_le (hbound w hw)) hz

end
end LeanNumDetect.MultiTuran
