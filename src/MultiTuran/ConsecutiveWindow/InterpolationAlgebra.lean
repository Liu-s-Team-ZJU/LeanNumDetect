import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! # Finite Newton algebra, including repeated nodes

Coefficient mass is estimated before evaluating the interpolation polynomial.
The resolvent identity is purely algebraic and never divides by differences
between nodes.  Consequently it also handles confluent coordinate values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
open Polynomial

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
noncomputable section

def polynomialMass (p : ℂ[X]) : ℝ := p.sum (fun _ a => ‖a‖)

theorem polynomialMass_nonneg (p : ℂ[X]) : 0 ≤ polynomialMass p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

@[simp] theorem polynomialMass_monomial (k : ℕ) (a : ℂ) :
    polynomialMass (monomial k a) = ‖a‖ := by
  unfold polynomialMass
  exact sum_monomial_index _ _ (by simp)

@[simp] theorem polynomialMass_zero : polynomialMass (0 : ℂ[X])=0 := by simp [polynomialMass]

@[simp] theorem polynomialMass_C (a : ℂ) : polynomialMass (C a) = ‖a‖ := by
  simpa only [monomial_zero_left] using polynomialMass_monomial 0 a

@[simp] theorem polynomialMass_one : polynomialMass (1 : ℂ[X])=1 := by
  change polynomialMass (C (1 : ℂ))=1
  rw [← monomial_zero_left,polynomialMass_monomial]
  norm_num

theorem polynomialMass_add_le (p q : ℂ[X]) :
    polynomialMass (p+q) ≤ polynomialMass p+polynomialMass q := by
  classical
  have hsum (r : ℂ[X]) (hr : r.support ⊆ p.support ∪ q.support) :
      polynomialMass r = ∑ k ∈ p.support ∪ q.support, ‖r.coeff k‖ :=
    sum_eq_of_subset _ (fun _ => norm_zero) hr
  rw [hsum (p+q) support_add,hsum p Finset.subset_union_left,
    hsum q Finset.subset_union_right,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => by rw [coeff_add]; exact norm_add_le _ _

theorem polynomialMass_sum_le {ι : Type*} (s : Finset ι) (p : ι → ℂ[X]) :
    polynomialMass (∑ i ∈ s, p i) ≤ ∑ i ∈ s, polynomialMass (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (polynomialMass_add_le _ _).trans (add_le_add le_rfl ih)

theorem polynomialMass_mul_le (p q : ℂ[X]) :
    polynomialMass (p*q) ≤ polynomialMass p*polynomialMass q := by
  rw [Polynomial.mul_eq_sum_sum]
  calc
    _ ≤ ∑ i ∈ p.support, polynomialMass
        (q.sum fun j a => monomial (i+j) (p.coeff i*a)) := polynomialMass_sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, ‖p.coeff i*q.coeff j‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (polynomialMass_sum_le _ _).trans_eq (by simp only [polynomialMass_monomial])
    _ = polynomialMass p*polynomialMass q := by
      simp only [norm_mul,polynomialMass,sum_def,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]

theorem polynomialMass_C_mul_le (a : ℂ) (p : ℂ[X]) :
    polynomialMass (C a*p) ≤ ‖a‖*polynomialMass p := by
  have h := polynomialMass_mul_le (C a) p
  simpa only [polynomialMass_C] using h

def newtonBasis (nodes : ℕ → ℂ) (k : ℕ) : ℂ[X] :=
  ∏ i ∈ Finset.range k, (X-C (nodes i))

theorem newtonBasis_mass_le (nodes : ℕ → ℂ) (hnodes : ∀ i, ‖nodes i‖ ≤ 1) (k : ℕ) :
    polynomialMass (newtonBasis nodes k) ≤ (2 : ℝ)^k := by
  induction k with
  | zero => simp [newtonBasis]
  | succ k ih =>
    have hf : polynomialMass (X-C (nodes k)) ≤ 2 := by
      have h := polynomialMass_add_le X (C (-nodes k))
      have hX : polynomialMass (X : ℂ[X])=1 := by
        rw [← monomial_one_one_eq_X,polynomialMass_monomial]
        norm_num
      rw [hX,polynomialMass_C,norm_neg] at h
      simpa only [map_neg,sub_eq_add_neg] using h.trans (by linarith [hnodes k])
    rw [newtonBasis,Finset.prod_range_succ]
    exact (polynomialMass_mul_le _ _).trans
      (by simpa only [newtonBasis, pow_succ] using
        mul_le_mul ih hf (polynomialMass_nonneg _) (by positivity))

theorem newtonBasis_natDegree_le (nodes : ℕ → ℂ) (k : ℕ) :
    (newtonBasis nodes k).natDegree ≤ k := by
  unfold newtonBasis
  have h := natDegree_prod_le (Finset.range k) (fun i => X-C (nodes i))
  simpa using h

@[simp] theorem newtonBasis_eval (nodes : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    (newtonBasis nodes k).eval z = ∏ i ∈ Finset.range k, (z-nodes i) := by
  simp only [newtonBasis, eval_prod, eval_sub, eval_X, eval_C]

def newtonPolynomial (n : ℕ) (nodes : ℕ → ℂ) (c : Fin n → ℂ) : ℂ[X] :=
  ∑ j, C (c j)*newtonBasis nodes j.val

theorem newtonPolynomial_natDegree_le {n : ℕ} (hn : 0 < n)
    (nodes : ℕ → ℂ) (c : Fin n → ℂ) : (newtonPolynomial n nodes c).natDegree ≤ n-1 := by
  unfold newtonPolynomial
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_le _ _).trans ((newtonBasis_natDegree_le nodes j.val).trans (by omega))

theorem newtonPolynomial_mass_le {n : ℕ} (nodes : ℕ → ℂ)
    (hnodes : ∀ i, ‖nodes i‖ ≤ 1) (c : Fin n → ℂ) :
    polynomialMass (newtonPolynomial n nodes c) ≤ ∑ j, ‖c j‖*(2 : ℝ)^j.val := by
  unfold newtonPolynomial
  apply (polynomialMass_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact (polynomialMass_C_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (newtonBasis_mass_le nodes hnodes j.val) (norm_nonneg _))

theorem newtonPolynomial_mass_le_window_constant {n : ℕ} (hn : 2 ≤ n)
    (nodes : ℕ → ℂ) (hnodes : ∀ i, ‖nodes i‖ ≤ 1) (c : Fin n → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ 3*(3/2 : ℝ)^n*(n : ℝ)^(j.val+1)) :
    polynomialMass (newtonPolynomial n nodes c) ≤ 3*(3*(n : ℝ))^n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hgeom (m : ℕ) : (n : ℝ)*(∑ j ∈ Finset.range m, (2*(n : ℝ))^j) ≤ (2*(n : ℝ))^m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ,mul_add,pow_succ]
      have hp : 0 ≤ (2*(n : ℝ))^m := by positivity
      nlinarith
  calc
    _ ≤ ∑ j : Fin n, (3*(3/2 : ℝ)^n*(n : ℝ)^(j.val+1))*(2 : ℝ)^j.val :=
      (newtonPolynomial_mass_le nodes hnodes c).trans
        (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (by positivity))
    _ = (3*(3/2 : ℝ)^n)*((n : ℝ)*(∑ j ∈ Finset.range n, (2*(n : ℝ))^j)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [Finset.mul_sum,pow_succ,mul_pow]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (3*(3/2 : ℝ)^n)*(2*(n : ℝ))^n :=
      mul_le_mul_of_nonneg_left (hgeom n) (by positivity)
    _ = _ := by rw [mul_assoc,← mul_pow]; congr 1; congr 1; ring

theorem polynomialMass_eq_fin_sum {n : ℕ} (hn : 0 < n) (p : ℂ[X])
    (hp : p.natDegree ≤ n-1) : polynomialMass p = ∑ k : Fin n, ‖p.coeff k.val‖ := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ‖p.coeff k‖)]
  apply sum_eq_of_subset _ (fun _ => norm_zero)
  intro k hk
  exact Finset.mem_range.mpr ((le_natDegree_of_ne_zero (mem_support_iff.mp hk)).trans_lt (by omega))

theorem polynomial_eval_eq_fin_sum {n : ℕ} (hn : 0 < n) (p : ℂ[X])
    (hp : p.natDegree ≤ n-1) (z : ℂ) :
    p.eval z = ∑ k : Fin n, p.coeff k.val * z ^ k.val := by
  rw [Polynomial.eval_eq_sum_range' (by omega : p.natDegree < n) z]
  exact (Fin.sum_univ_eq_sum_range (fun k => p.coeff k * z ^ k) n).symm

theorem unitCircle_pow_eq_exponential (y : ℝ) (k : ℕ) :
    Complex.exp (Complex.I * (y : ℂ)) ^ k =
      Complex.exp (Complex.I * (((k : ℝ) * y : ℝ) : ℂ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The polynomial witness yields the exact original scalar exponential
interpolation interface and its coefficient-mass constant. -/
theorem exists_window_coefficients_of_polynomial {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (t : ℝ) (p : ℂ[X])
    (hp : p.natDegree ≤ n-1) (hmass : polynomialMass p ≤ 3*(3*(n : ℝ))^n)
    (hvalue : ∀ j, p.eval (Complex.exp (Complex.I * (frequency j : ℂ))) =
      Complex.exp (Complex.I * ((t * frequency j : ℝ) : ℂ))) :
    ∃ a : Fin n → ℂ, (∑ k, ‖a k‖) ≤ 3*(3*(n : ℝ))^n ∧
      ∀ j, Complex.exp (Complex.I * ((t * frequency j : ℝ) : ℂ)) =
        ∑ k, a k * Complex.exp (Complex.I * (((k.val : ℝ)*frequency j : ℝ) : ℂ)) := by
  refine ⟨fun k => p.coeff k.val, ?_, ?_⟩
  · rwa [← polynomialMass_eq_fin_sum hn p hp]
  · intro j
    rw [← hvalue j, polynomial_eval_eq_fin_sum hn p hp]
    simp only [unitCircle_pow_eq_exponential]

/-- The finite resolvent expansion is valid with arbitrary repetitions. -/
theorem newton_resolvent_identity (nodes : ℕ → ℂ) (m : ℕ) (z ζ : ℂ)
    (hz : ζ≠z) (hnodes : ∀ i<m, ζ≠nodes i) :
    1/(ζ-z) =
      (∑ k ∈ Finset.range m,
        (∏ i ∈ Finset.range k, (z-nodes i))/(∏ i ∈ Finset.range (k+1), (ζ-nodes i))) +
      (∏ i ∈ Finset.range m, (z-nodes i))/
        ((ζ-z)*(∏ i ∈ Finset.range m, (ζ-nodes i))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hi := ih (fun i hi => hnodes i (by omega))
    have hprod : (∏ i ∈ Finset.range m, (ζ-nodes i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => sub_ne_zero.mpr (hnodes i (by
        have := Finset.mem_range.mp hi
        omega))
    rw [Finset.sum_range_succ,Finset.prod_range_succ,Finset.prod_range_succ]
    rw [hi]
    field_simp [hprod,sub_ne_zero.mpr hz,sub_ne_zero.mpr (hnodes m (by omega))]
    <;> ring

theorem newton_resolvent_at_node (nodes : ℕ → ℂ) {n : ℕ} (j : Fin n) (ζ : ℂ)
    (hnodes : ∀ i<n, ζ≠nodes i) :
    1/(ζ-nodes j.val) =
      ∑ k ∈ Finset.range n,
        (∏ i ∈ Finset.range k, (nodes j.val-nodes i))/
          (∏ i ∈ Finset.range (k+1), (ζ-nodes i)) := by
  have h := newton_resolvent_identity nodes n (nodes j.val) ζ (hnodes j.val j.isLt) hnodes
  have hp : (∏ i ∈ Finset.range n, (nodes j.val-nodes i))=0 :=
    Finset.prod_eq_zero (Finset.mem_range.mpr j.isLt) (sub_self _)
  simpa only [hp,zero_div,add_zero] using h

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
