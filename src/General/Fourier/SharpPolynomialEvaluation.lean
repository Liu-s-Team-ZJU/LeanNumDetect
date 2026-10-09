import General.Fourier.PolynomialEvaluationBounds
import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import General.Fourier.LegendreIntervalBounds

/-! Sharp unit-interval polynomial evaluation, using shifted Legendre polynomials. -/
set_option autoImplicit false
open scoped Polynomial BigOperators
open Set MeasureTheory
namespace LeanNumDetect.PolynomialEvaluationBounds
noncomputable section

def realShiftedLegendre (n : ℕ) : ℝ[X] :=
  (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)

theorem realShiftedLegendre_coeff (n k : ℕ) :
    (realShiftedLegendre n).coeff k =
      (-1 : ℝ)^k * (n.choose k : ℝ) * ((n+k).choose n : ℝ) := by
  simp [realShiftedLegendre, Polynomial.coeff_shiftedLegendre]

@[simp] theorem realShiftedLegendre_natDegree (n : ℕ) :
    (realShiftedLegendre n).natDegree = n := by
  rw [realShiftedLegendre, Polynomial.natDegree_map_eq_of_injective
    (Int.cast_injective (α := ℝ)), Polynomial.natDegree_shiftedLegendre]

@[simp] theorem realShiftedLegendre_eval_zero (n : ℕ) :
    (realShiftedLegendre n).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, realShiftedLegendre_coeff]
  simp

@[simp] theorem realShiftedLegendre_eval_one (n : ℕ) :
    (realShiftedLegendre n).eval 1 = (-1 : ℝ)^n := by
  have h := Polynomial.shiftedLegendre_eval_symm n (1 : ℝ)
  simpa [realShiftedLegendre, Polynomial.aeval_def, Polynomial.coeff_shiftedLegendre] using h

theorem realShiftedLegendre_coeff_recurrence (n k : ℕ) :
    ((k : ℝ)+1)^2 * (realShiftedLegendre n).coeff (k+1) +
      ((n : ℝ)*((n : ℝ)+1) - (k : ℝ)*((k : ℝ)+1)) *
        (realShiftedLegendre n).coeff k = 0 := by
  by_cases hk : k ≤ n
  · have h₁ := Nat.choose_succ_right_eq n k
    have h₂ := Nat.choose_mul_succ_eq (n+k) n
    have h₁R : (n.choose (k+1) : ℝ) * ((k : ℝ)+1) =
        (n.choose k : ℝ) * ((n : ℝ)-(k : ℝ)) := by
      exact_mod_cast h₁
    have h₂R : (((n+k).choose n : ℝ)) * ((n : ℝ)+(k : ℝ)+1) =
        ((n+k+1).choose n : ℝ) * ((k : ℝ)+1) := by
      simpa only [show n+k+1-n=k+1 by omega, Nat.cast_add, Nat.cast_one] using
        (show (((n+k).choose n : ℝ)) * ((n+k+1 : ℕ) : ℝ) =
          ((n+k+1).choose n : ℝ) * ((n+k+1-n : ℕ) : ℝ) by exact_mod_cast h₂)
    have hb : ((k : ℝ)+1)^2 * (n.choose (k+1) : ℝ) * ((n+k+1).choose n : ℝ) =
        (n.choose k : ℝ) * ((n : ℝ)-(k : ℝ)) *
          (((n+k).choose n : ℝ) * ((n : ℝ)+(k : ℝ)+1)) := by
      calc
        _ = ((n.choose (k+1) : ℝ) * ((k : ℝ)+1)) *
          (((n+k+1).choose n : ℝ) * ((k : ℝ)+1)) := by ring
        _ = _ := by rw [h₁R, ← h₂R]
    rw [realShiftedLegendre_coeff, realShiftedLegendre_coeff, pow_succ]
    simp only [← Nat.add_assoc]
    linear_combination -((-1 : ℝ)^k) * hb
  · have hkn : n < k := Nat.lt_of_not_ge hk
    rw [realShiftedLegendre_coeff, realShiftedLegendre_coeff,
      Nat.choose_eq_zero_of_lt (by omega : n < k+1),
      Nat.choose_eq_zero_of_lt hkn]
    ring

theorem realShiftedLegendre_divergence_equation (n : ℕ) :
    ((Polynomial.X * (1-Polynomial.X)) *
      (realShiftedLegendre n).derivative).derivative +
      Polynomial.C ((n : ℝ)*((n : ℝ)+1)) * realShiftedLegendre n = 0 := by
  apply Polynomial.ext
  intro k
  have hp : (Polynomial.X * (1-Polynomial.X)) * (realShiftedLegendre n).derivative =
      Polynomial.X * (realShiftedLegendre n).derivative -
        Polynomial.X * (Polynomial.X * (realShiftedLegendre n).derivative) := by ring
  rw [hp]
  cases k with
  | zero =>
      simpa [Polynomial.coeff_derivative, Polynomial.coeff_sub,
        Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero,
        Polynomial.coeff_C_mul] using realShiftedLegendre_coeff_recurrence n 0
  | succ k =>
      simp only [Polynomial.coeff_add, Polynomial.coeff_derivative,
        Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
        Polynomial.coeff_zero]
      have h := realShiftedLegendre_coeff_recurrence n (k+1)
      push_cast at h ⊢
      nlinarith

theorem realShiftedLegendre_equation (n : ℕ) (x : ℝ) :
    x*(1-x)*(realShiftedLegendre n).derivative.derivative.eval x +
      (1-2*x)*(realShiftedLegendre n).derivative.eval x +
        (n : ℝ)*((n : ℝ)+1)*(realShiftedLegendre n).eval x = 0 := by
  have h := congrArg (Polynomial.eval x) (realShiftedLegendre_divergence_equation n)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_sub,
    Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_one, Polynomial.eval_zero] at h
  nlinarith

theorem realShiftedLegendre_unit_sq_le_one (n : ℕ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : ((realShiftedLegendre n).eval x)^2 ≤ 1 := by
  cases n with
  | zero => simp [realShiftedLegendre, Polynomial.shiftedLegendre]
  | succ n =>
      apply realPolynomial_unit_sq_le_one_of_legendre_ode
        (eigenvalue := ((n+1 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)+1))
        (by positivity) (fun t _ => realShiftedLegendre_equation (n+1) t)
        (by simp) ?_ hx
      rw [realShiftedLegendre_eval_one, ← pow_mul, Nat.mul_comm (n+1) 2, pow_mul]
      norm_num

theorem polynomial_unit_integral_derivative (P : ℝ[X]) :
    (∫ x in (0 : ℝ)..1, P.derivative.eval x) = P.eval 1 - P.eval 0 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => P.hasDerivAt x) (P.derivative.continuous.intervalIntegrable _ _)

theorem realShiftedLegendre_orthogonal {n m : ℕ} (hnm : n ≠ m) :
    (∫ x in (0 : ℝ)..1,
      (realShiftedLegendre n).eval x * (realShiftedLegendre m).eval x) = 0 := by
  let P := realShiftedLegendre n
  let Q := realShiftedLegendre m
  let W : ℝ[X] := Polynomial.X*(1-Polynomial.X)*(P.derivative*Q-P*Q.derivative)
  have hW (x : ℝ) : W.derivative.eval x =
      ((m : ℝ)*((m : ℝ)+1)-(n : ℝ)*((n : ℝ)+1)) * (P.eval x*Q.eval x) := by
    have hp := realShiftedLegendre_equation n x
    have hq := realShiftedLegendre_equation m x
    change x*(1-x)*P.derivative.derivative.eval x +
      (1-2*x)*P.derivative.eval x + (n : ℝ)*((n : ℝ)+1)*P.eval x = 0 at hp
    change x*(1-x)*Q.derivative.derivative.eval x +
      (1-2*x)*Q.derivative.eval x + (m : ℝ)*((m : ℝ)+1)*Q.eval x = 0 at hq
    simp only [W, Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_one, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_zero]
    linear_combination (Q.eval x)*hp - (P.eval x)*hq
  have h := polynomial_unit_integral_derivative W
  have he : (fun x : ℝ => W.derivative.eval x) =
      (fun x => ((m : ℝ)*((m : ℝ)+1)-(n : ℝ)*((n : ℝ)+1))*(P.eval x*Q.eval x)) := by
    funext x; exact hW x
  rw [he, intervalIntegral.integral_const_mul] at h
  have hb : W.eval 1 - W.eval 0 = 0 := by simp [W]
  rw [hb] at h
  have hcoef : ((m : ℝ)*((m : ℝ)+1)-(n : ℝ)*((n : ℝ)+1)) ≠ 0 := by
    have hmnR : (m : ℝ) - (n : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm hnm)
    have hsum : (m : ℝ)+(n : ℝ)+1 ≠ 0 := by positivity
    have heq : (m : ℝ)*((m : ℝ)+1)-(n : ℝ)*((n : ℝ)+1) =
        ((m : ℝ)-(n : ℝ))*((m : ℝ)+(n : ℝ)+1) := by ring
    rw [heq]; exact mul_ne_zero hmnR hsum
  exact (mul_eq_zero.mp h).resolve_left hcoef

def realShiftedLegendreSequence : Polynomial.Sequence ℝ where
  elems' := realShiftedLegendre
  degree_eq' n := by
    have hz : realShiftedLegendre n ≠ 0 := by
      intro h; have := realShiftedLegendre_eval_zero n; simp [h] at this
    rw [Polynomial.degree_eq_natDegree hz, realShiftedLegendre_natDegree]

theorem realShiftedLegendre_leadingCoeff_unit (n : ℕ) :
    IsUnit (realShiftedLegendre n).leadingCoeff := by
  apply isUnit_iff_ne_zero.mpr
  apply Polynomial.leadingCoeff_ne_zero.mpr
  intro h; have := realShiftedLegendre_eval_zero n; simp [h] at this

def legendreIntegralPair (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun P := ∫ x in (0 : ℝ)..1, (realShiftedLegendre n).eval x * P.eval x
  map_add' P Q := by
    simp only [Polynomial.eval_add, mul_add]
    exact intervalIntegral.integral_add
      (((realShiftedLegendre n).continuous.mul P.continuous).intervalIntegrable _ _)
      (((realShiftedLegendre n).continuous.mul Q.continuous).intervalIntegrable _ _)
  map_smul' c P := by
    simp only [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply]
    rw [show (fun x => (realShiftedLegendre n).eval x * (c*P.eval x)) =
      (fun x => c*((realShiftedLegendre n).eval x*P.eval x)) by funext x; ring]
    exact intervalIntegral.integral_const_mul _ _

theorem realShiftedLegendre_orthogonal_of_degree_lt (n : ℕ) (P : ℝ[X])
    (hP : P.degree < n) : legendreIntegralPair n P = 0 := by
  have hspan := realShiftedLegendreSequence.span_degreeLT
    (m := n) (fun i _ => realShiftedLegendre_leadingCoeff_unit i)
  have hker : Submodule.span ℝ (realShiftedLegendreSequence '' Iio n) ≤
      LinearMap.ker (legendreIntegralPair n) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change legendreIntegralPair n (realShiftedLegendre i) = 0
    exact realShiftedLegendre_orthogonal (by have := hi; simp at this; omega)
  apply hker
  rw [hspan, Polynomial.mem_degreeLT]
  exact hP

theorem central_choose_step (n : ℕ) :
    (n+1) * ((2*n+2).choose (n+1)) =
      2*(2*n+1)*((2*n).choose n) := by
  have h := Nat.choose_mul_succ_eq (2*n) n
  have hc : (2*n+2).choose (n+1) = 2*((2*n+1).choose n) := by
    rw [show 2*n+2=(2*n+1)+1 by omega, Nat.choose_succ_succ,
      Nat.choose_symm_half]
    omega
  rw [hc]
  rw [show 2*n+1-n=n+1 by omega] at h
  nlinarith

theorem realShiftedLegendre_derivative_top_coeff (n : ℕ) :
    (realShiftedLegendre (n+1)).derivative.coeff n =
      (-2*(2*(n : ℝ)+1))*(realShiftedLegendre n).coeff n := by
  have h : ((n : ℝ)+1)*((2*n+2).choose (n+1) : ℝ) =
      2*(2*(n : ℝ)+1)*((2*n).choose n : ℝ) := by
    exact_mod_cast central_choose_step n
  rw [Polynomial.coeff_derivative, realShiftedLegendre_coeff,
    realShiftedLegendre_coeff, Nat.choose_self, Nat.choose_self, pow_succ]
  simp only [Nat.cast_one, mul_one]
  rw [show n+n=2*n by omega, show n+1+(n+1)=2*n+2 by omega]
  linear_combination -((-1 : ℝ)^n)*h

theorem realShiftedLegendre_derivative_remainder_degree (n : ℕ) :
    ((realShiftedLegendre (n+1)).derivative -
      Polynomial.C (-2*(2*(n : ℝ)+1))*realShiftedLegendre n).degree < n := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro k hk
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  by_cases hkn : k=n
  · subst k
    rw [realShiftedLegendre_derivative_top_coeff]
    ring
  · have hnk : n<k := lt_of_le_of_ne hk (Ne.symm hkn)
    have hd : (realShiftedLegendre (n+1)).derivative.natDegree ≤ n := by
      simpa only [realShiftedLegendre_natDegree, Nat.add_sub_cancel]
        using (realShiftedLegendre (n+1)).natDegree_derivative_le
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hnk),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hnk)]
    ring

theorem realShiftedLegendre_sq_integral (n : ℕ) :
    (∫ x in (0 : ℝ)..1, ((realShiftedLegendre n).eval x)^2) =
      1/(2*(n : ℝ)+1) := by
  let P := realShiftedLegendre n
  let Q := realShiftedLegendre (n+1)
  have hlow := realShiftedLegendre_orthogonal_of_degree_lt n
    (Q.derivative-Polynomial.C (-2*(2*(n : ℝ)+1))*P)
    (realShiftedLegendre_derivative_remainder_degree n)
  change (∫ x in (0 : ℝ)..1,
    P.eval x*(Q.derivative-Polynomial.C (-2*(2*(n : ℝ)+1))*P).eval x)=0 at hlow
  have hpdeg : P.derivative.degree < n+1 := by
    apply Polynomial.degree_le_natDegree.trans_lt
    exact_mod_cast (lt_of_le_of_lt P.natDegree_derivative_le (by simp [P]))
  have hlow₂ := realShiftedLegendre_orthogonal_of_degree_lt (n+1) P.derivative hpdeg
  change (∫ x in (0 : ℝ)..1, Q.eval x*P.derivative.eval x)=0 at hlow₂
  have hFTC := polynomial_unit_integral_derivative (Q*P)
  simp only [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul] at hFTC
  have hi₁ : IntervalIntegrable (fun x : ℝ => Q.derivative.eval x*P.eval x) volume 0 1 :=
    (Q.derivative.continuous.mul P.continuous).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun x : ℝ => Q.eval x*P.derivative.eval x) volume 0 1 :=
    (Q.continuous.mul P.derivative.continuous).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi₁ hi₂, hlow₂] at hFTC
  have hb : Q.eval 1*P.eval 1 - Q.eval 0*P.eval 0 = -2 := by
    simp only [Q, P, realShiftedLegendre_eval_one, realShiftedLegendre_eval_zero, pow_succ]
    have hs : ((-1 : ℝ)^n)^2 = 1 := by rw [← pow_mul]; simp
    nlinarith
  rw [hb, add_zero] at hFTC
  have hf : (fun x : ℝ =>
      P.eval x*(Q.derivative-Polynomial.C (-2*(2*(n : ℝ)+1))*P).eval x) =
      (fun x => Q.derivative.eval x*P.eval x -
        (-2*(2*(n : ℝ)+1))*(P.eval x)^2) := by
    funext x
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  rw [hf, intervalIntegral.integral_sub
    hi₁
    (show IntervalIntegrable (fun x : ℝ => (-2*(2*(n : ℝ)+1))*(P.eval x)^2) volume 0 1 from
      ((continuous_const.mul (P.continuous.pow 2)).intervalIntegrable _ _)),
    intervalIntegral.integral_const_mul, hFTC] at hlow
  have hden : 0 < 2*(n : ℝ)+1 := by positivity
  apply (eq_div_iff (ne_of_gt hden)).2
  nlinarith

theorem realShiftedLegendre_expansion (P : ℝ[X]) {n : ℕ} (hdeg : P.natDegree ≤ n) :
    ∃ a : Fin (n+1) → ℝ, ∑ i, a i • realShiftedLegendre i.val = P := by
  have hspan := realShiftedLegendreSequence.span_degreeLE
    (m := n) (fun i _ => realShiftedLegendre_leadingCoeff_unit i)
  have hrange : realShiftedLegendreSequence '' Iic n =
      range (fun i : Fin (n+1) => realShiftedLegendre i.val) := by
    ext Q
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, Nat.lt_succ_iff.mpr hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, Nat.lt_succ_iff.mp i.isLt, rfl⟩
  have hmem : P ∈ Polynomial.degreeLE ℝ n :=
    Polynomial.mem_degreeLE.mpr (P.degree_le_natDegree.trans (by exact_mod_cast hdeg))
  rw [← hspan, hrange] at hmem
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem

theorem sum_fin_odd (s : ℕ) : (∑ i : Fin s, (2*(i.val : ℝ)+1)) = (s : ℝ)^2 := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
      ring

theorem realPolynomial_unit_row_bound_sharp {P : ℝ[X]} {n : ℕ}
    (hdeg : P.natDegree ≤ n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (P.eval x)^2 ≤ ((n : ℝ)+1)^2 * (∫ t in (0 : ℝ)..1, (P.eval t)^2) := by
  obtain ⟨a, ha⟩ := realShiftedLegendre_expansion P hdeg
  have heval (t : ℝ) : P.eval t =
      ∑ i : Fin (n+1), a i * (realShiftedLegendre i.val).eval t := by
    rw [← ha, Polynomial.eval_finsetSum]
    simp
  have hp (i j : Fin (n+1)) : legendreIntegralPair i.val (realShiftedLegendre j.val) =
      if i=j then 1/(2*(i.val : ℝ)+1) else 0 := by
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl]
      change (∫ t in (0 : ℝ)..1,
        (realShiftedLegendre i.val).eval t * (realShiftedLegendre i.val).eval t) = _
      simpa only [pow_two] using realShiftedLegendre_sq_integral i.val
    · rw [if_neg hij]
      exact realShiftedLegendre_orthogonal (by intro hv; exact hij (Fin.ext hv))
  have hpair (i : Fin (n+1)) : legendreIntegralPair i.val P = a i/(2*(i.val : ℝ)+1) := by
    rw [← ha, map_sum]
    simp only [map_smul, smul_eq_mul]
    simp_rw [hp i]
    simp [div_eq_mul_inv]
  have hefun : (fun t : ℝ => (P.eval t)^2) =
      (fun t => ∑ i : Fin (n+1), a i*((realShiftedLegendre i.val).eval t*P.eval t)) := by
    funext t
    nth_rw 1 [pow_two, heval t]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _; ring
  have henergy : (∫ t in (0 : ℝ)..1, (P.eval t)^2) =
      ∑ i : Fin (n+1), (a i)^2/(2*(i.val : ℝ)+1) := by
    rw [hefun, intervalIntegral.integral_finsetSum
      (fun i _ => (show Continuous (fun t : ℝ =>
        a i*((realShiftedLegendre i.val).eval t*P.eval t)) from
          continuous_const.mul ((realShiftedLegendre i.val).continuous.mul P.continuous)).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul]
    change a i * legendreIntegralPair i.val P = _
    rw [hpair i]
    ring
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i : Fin (n+1) => a i*(realShiftedLegendre i.val).eval x)
    (f := fun i : Fin (n+1) => (a i)^2/(2*(i.val : ℝ)+1))
    (g := fun i : Fin (n+1) => (2*(i.val : ℝ)+1)*((realShiftedLegendre i.val).eval x)^2)
    (fun i _ => by positivity) (fun i _ => by positivity)
    (fun i _ => by
      have hw : (2*(i.val : ℝ)+1) ≠ 0 := by positivity
      apply le_of_eq
      field_simp [hw])
  have hkernel : (∑ i : Fin (n+1),
      (2*(i.val : ℝ)+1)*((realShiftedLegendre i.val).eval x)^2) ≤ ((n : ℝ)+1)^2 := by
    calc
      _ ≤ ∑ i : Fin (n+1), (2*(i.val : ℝ)+1) :=
        Finset.sum_le_sum (fun i _ => by
          simpa using mul_le_mul_of_nonneg_left
            (realShiftedLegendre_unit_sq_le_one i.val hx) (by positivity : 0≤2*(i.val : ℝ)+1))
      _ = _ := by simpa using sum_fin_odd (n+1)
  have hE : 0 ≤ ∫ t in (0 : ℝ)..1, (P.eval t)^2 := by
    rw [henergy]; positivity
  rw [← heval x, ← henergy] at hCS
  exact hCS.trans ((mul_le_mul_of_nonneg_left hkernel hE).trans_eq (by ring))

theorem complexPolynomial_unit_row_bound_sharp {P Q : ℝ[X]} {n : ℕ}
    (hPdeg : P.natDegree ≤ n) (hQdeg : Q.natDegree ≤ n)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖complexPolynomialSignal P Q x‖^2 ≤
      ((n : ℝ)+1)^2 * (∫ t in (0 : ℝ)..1, ‖complexPolynomialSignal P Q t‖^2) := by
  have hp := realPolynomial_unit_row_bound_sharp hPdeg hx
  have hq := realPolynomial_unit_row_bound_sharp hQdeg hx
  have hn (t : ℝ) : ‖complexPolynomialSignal P Q t‖^2 = (P.eval t)^2+(Q.eval t)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply,
      complexPolynomialSignal_re, complexPolynomialSignal_im]
    ring
  have he : (∫ t in (0 : ℝ)..1, ‖complexPolynomialSignal P Q t‖^2) =
      (∫ t in (0 : ℝ)..1, (P.eval t)^2)+(∫ t in (0 : ℝ)..1, (Q.eval t)^2) := by
    rw [show (fun t : ℝ => ‖complexPolynomialSignal P Q t‖^2) =
      (fun t => (P.eval t)^2+(Q.eval t)^2) by funext t; exact hn t]
    exact intervalIntegral.integral_add
      (show IntervalIntegrable (fun t : ℝ => (P.eval t)^2) volume 0 1 from
        (P.continuous.pow 2).intervalIntegrable _ _)
      (show IntervalIntegrable (fun t : ℝ => (Q.eval t)^2) volume 0 1 from
        (Q.continuous.pow 2).intervalIntegrable _ _)
  rw [hn x, he]
  nlinarith

theorem jetPolynomial_unit_row_bound_sharp {s : ℕ} (hs : 0 < s)
    (a : Fin s → ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖jetPolynomialSignal a x‖^2 ≤
      (s : ℝ)^2 * (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2) := by
  rw [jetPolynomialSignal_eq_coefficientPolynomialSignal]
  have h := complexPolynomial_unit_row_bound_sharp
    (coefficientPolynomial_natDegree_le hs (fun j => (a j/(j.val.factorial : ℂ)).re))
    (coefficientPolynomial_natDegree_le hs (fun j => (a j/(j.val.factorial : ℂ)).im)) hx
  have hsR : ((s-1 : ℕ) : ℝ)+1=s := by
    exact_mod_cast (Nat.sub_add_cancel (show 1≤s from hs))
  change ‖complexPolynomialSignal
      (realCoefficientPolynomial (fun j => a j/(j.val.factorial : ℂ)))
      (imaginaryCoefficientPolynomial (fun j => a j/(j.val.factorial : ℂ))) x‖^2 ≤
    ((↑(s-1) : ℝ)+1)^2 * (∫ t in (0 : ℝ)..1,
      ‖complexPolynomialSignal
        (realCoefficientPolynomial (fun j => a j/(j.val.factorial : ℂ)))
        (imaginaryCoefficientPolynomial (fun j => a j/(j.val.factorial : ℂ))) t‖^2) at h
  simpa only [← coefficientPolynomialSignal_eq, hsR] using h


end
end LeanNumDetect.PolynomialEvaluationBounds
