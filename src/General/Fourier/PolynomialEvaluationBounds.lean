import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-!
# Polynomial evaluation bounds on the unit interval

The Chebyshev endpoint extremal inequality gives a weak Markov inequality on
the whole unit interval, by applying it on a one-sided subinterval of length
at least one half. The constants here are deliberately simple.
-/

set_option autoImplicit false
open scoped Polynomial BigOperators
open Set MeasureTheory

namespace LeanNumDetect.PolynomialEvaluationBounds

noncomputable section

theorem realPolynomial_endpoint_derivative_le {P : ℝ[X]} {n : ℕ}
    (hdeg : P.natDegree ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc (-1 : ℝ) 1, |P.eval t| ≤ B) :
    |P.derivative.eval 1| ≤ (n : ℝ) ^ 2 * B := by
  by_cases hB0 : B = 0
  · have hzero : P = 0 := by
      apply P.eq_zero_of_infinite_isRoot
      apply (Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono
      intro t ht
      change P.eval t = 0
      have := hbound t ht
      rw [hB0] at this
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    simp [hzero, hB0]
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  have hone (Q : ℝ[X]) (hQdeg : Q.natDegree ≤ n)
      (hQbound : ∀ t ∈ Icc (-1 : ℝ) 1, |Q.eval t| ≤ B) :
      Q.derivative.eval 1 ≤ (n : ℝ)^2 * B := by
    have h := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
      (P := B⁻¹ • Q) (n := n) (k := 1) (x := 1) (by norm_num)
      ((Polynomial.degree_smul_le B⁻¹ Q).trans
        (Polynomial.degree_le_natDegree.trans (by exact_mod_cast hQdeg)))
      (fun t ht => by
        simp only [Polynomial.eval_smul, smul_eq_mul, abs_mul, abs_inv,
          abs_of_pos hBpos]
        exact (inv_mul_le_iff₀ hBpos).2 (by simpa using hQbound t ht))
    simp only [Function.iterate_one, Polynomial.derivative_smul,
      Polynomial.eval_smul, smul_eq_mul,
      Polynomial.Chebyshev.derivative_T_eval_one, Int.cast_natCast] at h
    simpa [mul_comm] using (inv_mul_le_iff₀ hBpos).1 h
  apply abs_le.mpr
  constructor
  · have h := hone (-P) (by simpa using hdeg) (by simpa using hbound)
    simpa only [Polynomial.derivative_neg, Polynomial.eval_neg, neg_neg] using (neg_le_neg h)
  · exact hone P hdeg hbound

theorem realPolynomial_right_derivative_le {P : ℝ[X]} {n : ℕ}
    (hdeg : P.natDegree ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |P.eval t| ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hhalf : 1 / 2 ≤ x) :
    |P.derivative.eval x| ≤ 4 * (n : ℝ) ^ 2 * B := by
  let Q := P.comp (Polynomial.C (x / 2) * Polynomial.X + Polynomial.C (x / 2))
  have hQdeg : Q.natDegree ≤ n := by
    exact Polynomial.natDegree_comp_le.trans
      ((Nat.mul_le_mul hdeg Polynomial.natDegree_linear_le).trans (by simp))
  have hQbound : ∀ t ∈ Icc (-1 : ℝ) 1, |Q.eval t| ≤ B := by
    intro t ht
    dsimp [Q]
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    apply hbound
    constructor <;> nlinarith [hx.1, hx.2, ht.1, ht.2]
  have h := realPolynomial_endpoint_derivative_le hQdeg hB hQbound
  have hQder : Q.derivative.eval 1 = P.derivative.eval x * (x / 2) := by
    simp [Q, Polynomial.derivative_comp]
    ring
  rw [hQder, abs_mul, abs_of_nonneg (by linarith : 0 ≤ x / 2)] at h
  have hnonneg : 0 ≤ (n : ℝ)^2 * B := by positivity
  nlinarith [abs_nonneg (P.derivative.eval x)]

theorem realPolynomial_unit_derivative_le {P : ℝ[X]} {n : ℕ}
    (hdeg : P.natDegree ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |P.eval t| ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |P.derivative.eval x| ≤ 4 * (n : ℝ) ^ 2 * B := by
  by_cases hhalf : 1 / 2 ≤ x
  · exact realPolynomial_right_derivative_le hdeg hB hbound hx hhalf
  let Q := P.comp (1 - Polynomial.X)
  have hQdeg : Q.natDegree ≤ n := by
    have hlinear : (1 - (Polynomial.X : ℝ[X])).natDegree ≤ 1 := by
      simpa [sub_eq_add_neg, add_comm] using
        (Polynomial.natDegree_linear_le (a := (-1 : ℝ)) (b := 1))
    exact Polynomial.natDegree_comp_le.trans
      ((Nat.mul_le_mul hdeg hlinear).trans (by simp))
  have hQbound : ∀ t ∈ Icc (0 : ℝ) 1, |Q.eval t| ≤ B := by
    intro t ht
    simpa [Q, Polynomial.eval_comp] using
      hbound (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h := realPolynomial_right_derivative_le hQdeg hB hQbound
    (x := 1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)
  simpa [Q, Polynomial.derivative_comp_one_sub_X, Polynomial.eval_comp] using h

/-- Complex polynomials can be represented by two real polynomials. -/
def complexPolynomialSignal (P Q : ℝ[X]) (t : ℝ) : ℂ :=
  ((P.eval t : ℝ) : ℂ) + Complex.I * ((Q.eval t : ℝ) : ℂ)

theorem complexPolynomialSignal_re (P Q : ℝ[X]) (t : ℝ) :
    (complexPolynomialSignal P Q t).re = P.eval t := by
  simp [complexPolynomialSignal]

theorem complexPolynomialSignal_im (P Q : ℝ[X]) (t : ℝ) :
    (complexPolynomialSignal P Q t).im = Q.eval t := by
  simp [complexPolynomialSignal]

theorem continuous_complexPolynomialSignal (P Q : ℝ[X]) :
    Continuous (complexPolynomialSignal P Q) := by
  unfold complexPolynomialSignal
  fun_prop

theorem hasDerivAt_complexPolynomialSignal (P Q : ℝ[X]) (t : ℝ) :
    HasDerivAt (complexPolynomialSignal P Q)
      (complexPolynomialSignal P.derivative Q.derivative t) t := by
  exact (P.hasDerivAt t).ofReal_comp.add
    ((Q.hasDerivAt t).ofReal_comp.const_mul Complex.I)

theorem complexPolynomialSignal_deriv (P Q : ℝ[X]) (t : ℝ) :
    deriv (complexPolynomialSignal P Q) t =
      complexPolynomialSignal P.derivative Q.derivative t :=
  (hasDerivAt_complexPolynomialSignal P Q t).deriv

theorem complexPolynomial_unit_derivative_le {P Q : ℝ[X]} {n : ℕ}
    (hPdeg : P.natDegree ≤ n) (hQdeg : Q.natDegree ≤ n)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖complexPolynomialSignal P Q t‖ ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖deriv (complexPolynomialSignal P Q) x‖ ≤ 8 * (n : ℝ)^2 * B := by
  have hPbound : ∀ t ∈ Icc (0 : ℝ) 1, |P.eval t| ≤ B := by
    intro t ht
    have h := Complex.abs_re_le_norm (complexPolynomialSignal P Q t)
    rw [complexPolynomialSignal_re] at h
    exact h.trans (hbound t ht)
  have hQbound : ∀ t ∈ Icc (0 : ℝ) 1, |Q.eval t| ≤ B := by
    intro t ht
    have h := Complex.abs_im_le_norm (complexPolynomialSignal P Q t)
    rw [complexPolynomialSignal_im] at h
    exact h.trans (hbound t ht)
  have hP := realPolynomial_unit_derivative_le hPdeg hB hPbound hx
  have hQ := realPolynomial_unit_derivative_le hQdeg hB hQbound hx
  rw [complexPolynomialSignal_deriv]
  have h := Complex.norm_le_abs_re_add_abs_im
    (complexPolynomialSignal P.derivative Q.derivative x)
  rw [complexPolynomialSignal_re, complexPolynomialSignal_im] at h
  linarith

/-- A function with a relative Lipschitz bound cannot concentrate its entire
unit-interval energy in an arbitrarily short interval. -/
theorem unitInterval_peak_sq_le_energy_of_lipschitz {f : ℝ → ℂ}
    (hf : Continuous f) {B D x₀ : ℝ} (hB : 0 ≤ B) (hD : 1 ≤ D)
    (hx₀ : x₀ ∈ Icc (0 : ℝ) 1) (hpeak : ‖f x₀‖ = B)
    (hLip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖f y - f x‖ ≤ D * B * |y - x|) :
    B^2 ≤ 8 * D * (∫ t in (0 : ℝ)..1, ‖f t‖^2) := by
  have hDpos : 0 < D := by linarith
  let r := 1 / (2 * D)
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrhalf : r ≤ 1 / 2 := by
    dsimp [r]
    exact (div_le_div_iff₀ (by positivity) (by norm_num)).2 (by linarith)
  have hlocal {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
      (hlen : b - a = r)
      (hclose : ∀ t ∈ Icc a b, |t - x₀| ≤ r) :
      B^2 ≤ 8 * D * (∫ t in (0 : ℝ)..1, ‖f t‖^2) := by
    have hlow (t : ℝ) (ht : t ∈ Icc a b) : B / 2 ≤ ‖f t‖ := by
      have htunit : t ∈ Icc (0 : ℝ) 1 := ⟨ha.trans ht.1, ht.2.trans hb⟩
      have hdiff := hLip x₀ hx₀ t htunit
      have hdiff' := hdiff.trans
        (mul_le_mul_of_nonneg_left (hclose t ht) (by positivity : 0 ≤ D * B))
      have hscale : D * B * r = B / 2 := by
        dsimp [r]
        field_simp
      rw [hscale] at hdiff'
      have hnorm : ‖f x₀‖ - ‖f t‖ ≤ ‖f t - f x₀‖ := by
        simpa only [norm_sub_rev] using norm_sub_norm_le (f x₀) (f t)
      rw [hpeak] at hnorm
      linarith
    have henergy : r * (B / 2)^2 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 := by
      calc
        r * (B / 2)^2 = ∫ t in a..b, (B / 2)^2 := by
          simp [intervalIntegral.integral_const, hlen, smul_eq_mul]
        _ ≤ ∫ t in a..b, ‖f t‖^2 := by
          apply intervalIntegral.integral_mono_on (μ := volume) hab
            (continuous_const.intervalIntegrable a b)
            ((hf.norm.pow 2).intervalIntegrable a b)
          intro t ht
          exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 (hlow t ht)
        _ ≤ ∫ t in (0 : ℝ)..1, ‖f t‖^2 :=
          intervalIntegral.integral_mono_interval ha hab hb
            (Filter.Eventually.of_forall (fun t => by positivity))
            ((hf.norm.pow 2).intervalIntegrable 0 1)
    have hscale : r * (B / 2)^2 = B^2 / (8 * D) := by
      dsimp [r]
      field_simp
      ring
    rw [hscale] at henergy
    exact (div_le_iff₀ (by positivity : 0 < 8 * D)).1 henergy |>.trans_eq (by ring)
  by_cases hxhalf : x₀ ≤ 1 / 2
  · apply hlocal (a := x₀) (b := x₀ + r) hx₀.1 (by linarith) (by linarith)
      (by ring)
    intro t ht
    rw [abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.2]
  · apply hlocal (a := x₀ - r) (b := x₀) (by linarith) (by linarith) hx₀.2
      (by ring)
    intro t ht
    rw [abs_of_nonpos (by linarith [ht.2])]
    linarith [ht.1]

/-- The dimension-squared polynomial point-evaluation estimate, with an
absolute constant. All coefficient combinations are covered simultaneously. -/
theorem complexPolynomial_unit_row_bound {P Q : ℝ[X]} {n : ℕ}
    (hPdeg : P.natDegree ≤ n) (hQdeg : Q.natDegree ≤ n)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖complexPolynomialSignal P Q x‖^2 ≤
      64 * ((n : ℝ) + 1)^2 *
        (∫ t in (0 : ℝ)..1, ‖complexPolynomialSignal P Q t‖^2) := by
  let f := complexPolynomialSignal P Q
  have hf : Continuous f := continuous_complexPolynomialSignal P Q
  obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩) hf.norm.continuousOn
  let B := ‖f x₀‖
  have hB : 0 ≤ B := norm_nonneg _
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ B := hmax
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖deriv f t‖ ≤ 8 * ((n : ℝ) + 1)^2 * B := by
    have h := complexPolynomial_unit_derivative_le hPdeg hQdeg hB hbound ht
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    dsimp [f]
    nlinarith
  have hLip (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
      (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      ‖f v - f u‖ ≤ (8 * ((n : ℝ) + 1)^2) * B * |v - u| := by
    exact (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (hasDerivAt_complexPolynomialSignal P Q t).differentiableAt)
      hder hu hv |>.trans_eq (by rw [Real.norm_eq_abs])
  have hpeak := unitInterval_peak_sq_le_energy_of_lipschitz hf hB
    (show 1 ≤ 8 * ((n : ℝ) + 1)^2 by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    hx₀ (by rfl) hLip
  have hxbound := (sq_le_sq₀ (norm_nonneg _) hB).2 (hbound x hx)
  calc
    ‖f x‖^2 ≤ B^2 := hxbound
    _ ≤ 64 * ((n : ℝ) + 1)^2 * (∫ t in (0 : ℝ)..1, ‖f t‖^2) := by
      convert hpeak using 1
      ring

/-- Ordinary monomial coefficients, evaluated on the real line. -/
def coefficientPolynomialSignal {s : ℕ} (a : Fin s → ℂ) (t : ℝ) : ℂ :=
  ∑ j, a j * (t : ℂ)^j.val

def realCoefficientPolynomial {s : ℕ} (a : Fin s → ℂ) : ℝ[X] :=
  ∑ j, Polynomial.monomial j.val (a j).re

def imaginaryCoefficientPolynomial {s : ℕ} (a : Fin s → ℂ) : ℝ[X] :=
  ∑ j, Polynomial.monomial j.val (a j).im

theorem coefficientPolynomialSignal_eq {s : ℕ} (a : Fin s → ℂ) (t : ℝ) :
    coefficientPolynomialSignal a t =
      complexPolynomialSignal (realCoefficientPolynomial a)
        (imaginaryCoefficientPolynomial a) t := by
  apply Complex.ext
  · simp [coefficientPolynomialSignal, complexPolynomialSignal,
      realCoefficientPolynomial, imaginaryCoefficientPolynomial,
      Polynomial.eval_finsetSum, Complex.mul_re, ← Complex.ofReal_pow]
  · simp [coefficientPolynomialSignal, complexPolynomialSignal,
      realCoefficientPolynomial, imaginaryCoefficientPolynomial,
      Polynomial.eval_finsetSum, Complex.mul_im, ← Complex.ofReal_pow]

theorem coefficientPolynomial_natDegree_le {s : ℕ} (_hs : 0 < s)
    (a : Fin s → ℝ) :
    (∑ j, Polynomial.monomial j.val (a j)).natDegree ≤ s - 1 := by
  apply Polynomial.natDegree_le_of_degree_le
  apply (Polynomial.degree_sum_le _ _).trans
  apply Finset.sup_le
  intro j _
  exact (Polynomial.degree_monomial_le j.val (a j)).trans
    (by exact_mod_cast (show j.val ≤ s - 1 from Nat.le_pred_of_lt j.isLt))

theorem coefficientPolynomial_unit_row_bound {s : ℕ} (hs : 0 < s)
    (a : Fin s → ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖coefficientPolynomialSignal a x‖^2 ≤
      64 * (s : ℝ)^2 *
        (∫ t in (0 : ℝ)..1, ‖coefficientPolynomialSignal a t‖^2) := by
  have h := complexPolynomial_unit_row_bound
    (coefficientPolynomial_natDegree_le hs (fun j => (a j).re))
    (coefficientPolynomial_natDegree_le hs (fun j => (a j).im)) hx
  have hsR : ((s - 1 : ℕ) : ℝ) + 1 = s := by
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ s from hs))
  change ‖complexPolynomialSignal (realCoefficientPolynomial a)
      (imaginaryCoefficientPolynomial a) x‖^2 ≤
    64 * ((↑(s - 1) : ℝ) + 1)^2 * (∫ t in (0 : ℝ)..1,
      ‖complexPolynomialSignal (realCoefficientPolynomial a)
        (imaginaryCoefficientPolynomial a) t‖^2) at h
  simpa only [← coefficientPolynomialSignal_eq, hsR] using h

theorem coefficientPolynomial_unit_derivative_le {s : ℕ} (hs : 0 < s)
    (a : Fin s → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖coefficientPolynomialSignal a t‖ ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖deriv (coefficientPolynomialSignal a) x‖ ≤ 8 * (s : ℝ)^2 * B := by
  have heq : coefficientPolynomialSignal a =
      complexPolynomialSignal (realCoefficientPolynomial a)
        (imaginaryCoefficientPolynomial a) := by
    funext t
    exact coefficientPolynomialSignal_eq a t
  rw [heq] at hbound ⊢
  have h := complexPolynomial_unit_derivative_le
    (coefficientPolynomial_natDegree_le hs (fun j => (a j).re))
    (coefficientPolynomial_natDegree_le hs (fun j => (a j).im)) hB hbound hx
  have hpred : (s - 1 : ℕ) ≤ s := Nat.sub_le _ _
  have hpredR : ((s - 1 : ℕ) : ℝ) ≤ s := by exact_mod_cast hpred
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).2 hpredR)
      (by norm_num)) hB)

/-- Taylor jet coefficients, with the factorial normalization arising from
the exponential of the nilpotent companion matrix. -/
def jetPolynomialSignal {s : ℕ} (a : Fin s → ℂ) (t : ℝ) : ℂ :=
  ∑ j, a j * (t : ℂ)^j.val / (j.val.factorial : ℂ)

theorem jetPolynomialSignal_eq_coefficientPolynomialSignal {s : ℕ}
    (a : Fin s → ℂ) :
    jetPolynomialSignal a =
      coefficientPolynomialSignal (fun j => a j / (j.val.factorial : ℂ)) := by
  funext t
  simp only [jetPolynomialSignal, coefficientPolynomialSignal]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem jetPolynomial_unit_row_bound {s : ℕ} (hs : 0 < s)
    (a : Fin s → ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖jetPolynomialSignal a x‖^2 ≤
      64 * (s : ℝ)^2 * (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2) := by
  rw [jetPolynomialSignal_eq_coefficientPolynomialSignal]
  exact coefficientPolynomial_unit_row_bound hs _ hx

theorem jetPolynomial_unit_derivative_le {s : ℕ} (hs : 0 < s)
    (a : Fin s → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖jetPolynomialSignal a t‖ ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖deriv (jetPolynomialSignal a) x‖ ≤ 8 * (s : ℝ)^2 * B := by
  rw [jetPolynomialSignal_eq_coefficientPolynomialSignal] at hbound ⊢
  exact coefficientPolynomial_unit_derivative_le hs _ hB hbound hx

theorem continuous_jetPolynomialSignal {s : ℕ} (a : Fin s → ℂ) :
    Continuous (jetPolynomialSignal a) := by
  unfold jetPolynomialSignal
  fun_prop

/-- The complex polynomial having the given ordinary coefficients. -/
def coefficientPolynomial {s : ℕ} (a : Fin s → ℂ) : ℂ[X] :=
  ∑ j, Polynomial.monomial j.val (a j)

theorem coefficientPolynomial_eval {s : ℕ} (a : Fin s → ℂ) (t : ℝ) :
    (coefficientPolynomial a).eval (t : ℂ) = coefficientPolynomialSignal a t := by
  simp [coefficientPolynomial, coefficientPolynomialSignal,
    Polynomial.eval_finsetSum]

theorem coefficientPolynomial_coeff {s : ℕ} (a : Fin s → ℂ) (j : Fin s) :
    (coefficientPolynomial a).coeff j.val = a j := by
  simp only [coefficientPolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [Polynomial.coeff_monomial, hij']
  · simp

theorem coefficientPolynomialSignal_eq_zero_on_unit_iff {s : ℕ} (a : Fin s → ℂ) :
    (∀ t ∈ Icc (0 : ℝ) 1, coefficientPolynomialSignal a t = 0) ↔ a = 0 := by
  constructor
  · intro hzero
    have hpoly : coefficientPolynomial a = 0 := by
      apply (coefficientPolynomial a).eq_zero_of_infinite_isRoot
      apply ((Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image
        Complex.ofReal_injective.injOn).mono
      rintro z ⟨t, ht, rfl⟩
      change (coefficientPolynomial a).eval (t : ℂ) = 0
      rw [coefficientPolynomial_eval]
      exact hzero t ht
    funext j
    have := congrArg (fun P : ℂ[X] => P.coeff j.val) hpoly
    simpa [coefficientPolynomial_coeff] using this
  · rintro rfl
    simp [coefficientPolynomialSignal]

theorem jetPolynomialSignal_eq_zero_on_unit_iff {s : ℕ} (a : Fin s → ℂ) :
    (∀ t ∈ Icc (0 : ℝ) 1, jetPolynomialSignal a t = 0) ↔ a = 0 := by
  rw [jetPolynomialSignal_eq_coefficientPolynomialSignal]
  rw [coefficientPolynomialSignal_eq_zero_on_unit_iff]
  constructor
  · intro hzero
    funext j
    have hj := congrFun hzero j
    have hfac : (j.val.factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero j.val
    simpa only [Pi.zero_apply] using (div_eq_zero_iff.mp hj).resolve_right hfac
  · rintro rfl
    funext j
    simp

/-- Evaluation of Taylor jets as continuous functions, with their supremum norm. -/
def jetPolynomialEvaluation (s : ℕ) :
    (Fin s → ℂ) →ₗ[ℂ] C(Icc (0 : ℝ) 1, ℂ) where
  toFun a := ⟨fun t => jetPolynomialSignal a t,
    (continuous_jetPolynomialSignal a).comp continuous_subtype_val⟩
  map_add' a b := by
    ext t
    simp [jetPolynomialSignal, add_mul, add_div, Finset.sum_add_distrib]
  map_smul' c a := by
    ext t
    simp [jetPolynomialSignal, Finset.mul_sum, mul_assoc, mul_div_assoc]

theorem jetPolynomialEvaluation_apply {s : ℕ} (a : Fin s → ℂ)
    (t : Icc (0 : ℝ) 1) : jetPolynomialEvaluation s a t = jetPolynomialSignal a t := rfl

theorem jetPolynomialEvaluation_injective (s : ℕ) :
    Function.Injective (jetPolynomialEvaluation s) := by
  apply (injective_iff_map_eq_zero _).2
  intro a ha
  apply (jetPolynomialSignal_eq_zero_on_unit_iff a).1
  intro t ht
  have h := congrArg (fun f : C(Icc (0 : ℝ) 1, ℂ) => f ⟨t, ht⟩) ha
  simpa only [jetPolynomialEvaluation_apply, ContinuousMap.zero_apply] using h

/-- A fixed dimension has a uniform positive lower bound between the jet
coefficient norm and the polynomial supremum norm. -/
theorem jetPolynomial_coefficient_norm_le_sup (s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : Fin s → ℂ,
      ‖a‖ ≤ K * ‖jetPolynomialEvaluation s a‖ := by
  obtain ⟨K, hK, hanti⟩ :=
    (jetPolynomialEvaluation s).injective_iff_antilipschitz.mp
      (jetPolynomialEvaluation_injective s)
  refine ⟨K, by exact_mod_cast hK, fun a => ?_⟩
  have h := hanti.le_mul_dist a 0
  simpa only [dist_zero_right, map_zero] using h

theorem jetPolynomialEvaluation_norm_sq_le_energy {s : ℕ} (hs : 0 < s)
    (a : Fin s → ℂ) :
    ‖jetPolynomialEvaluation s a‖^2 ≤
      64 * (s : ℝ)^2 * (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2) := by
  let E := 64 * (s : ℝ)^2 * (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2)
  have henergy : 0 ≤ ∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2 := by
    apply intervalIntegral.integral_nonneg_of_forall
    · norm_num
    · intro t
      positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hnorm : ‖jetPolynomialEvaluation s a‖ ≤ Real.sqrt E := by
    apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).2
    intro t
    have h := jetPolynomial_unit_row_bound hs a t.property
    change ‖jetPolynomialSignal a t.val‖ ≤ Real.sqrt E
    nlinarith [Real.sq_sqrt hE, norm_nonneg (jetPolynomialSignal a t.val),
      Real.sqrt_nonneg E]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg E)).2 hnorm
  rwa [Real.sq_sqrt hE] at hsq

/-- Positive definiteness of the continuous Taylor-jet Gram form. The constant
depends only on the number of jet coefficients. No source separation enters. -/
theorem jetPolynomial_energy_lower (s : ℕ) (hs : 0 < s) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Fin s → ℂ,
      c * ‖a‖^2 ≤ ∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2 := by
  obtain ⟨K, hK, hcoeff⟩ := jetPolynomial_coefficient_norm_le_sup s
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  refine ⟨(64 * (s : ℝ)^2 * K^2)⁻¹, by positivity, fun a => ?_⟩
  have hnorm := hcoeff a
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity :
    0 ≤ K * ‖jetPolynomialEvaluation s a‖)).2 hnorm
  have hrow := jetPolynomialEvaluation_norm_sq_le_energy hs a
  have hmul := mul_le_mul_of_nonneg_left hrow (sq_nonneg K)
  rw [mul_pow] at hsq
  apply (inv_mul_le_iff₀ (by positivity : 0 < 64 * (s : ℝ)^2 * K^2)).2
  nlinarith

end
end LeanNumDetect.PolynomialEvaluationBounds
