import General.Fourier.PolynomialCrossCorrelation
import General.Fourier.SharperPolynomialEvaluation
import Mathlib.Analysis.Calculus.MeanValue

/-! Explicit variation bounds for modulated polynomial cross products.
The bound depends polynomially on the degrees, without a monomial mass loss. -/

set_option autoImplicit false
open scoped BigOperators InnerProductSpace Polynomial
open Set Matrix WithLp

namespace LeanNumDetect.PolynomialCrossCorrelation
open PolynomialEvaluationBounds
noncomputable section

theorem product_sub_norm_le_of_lipschitz
    (f g : ℝ → ℂ) {B C L K : ℝ}
    (hB : 0 ≤ B) (_hC : 0 ≤ C) (hL : 0 ≤ L) (_hK : 0 ≤ K)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ B)
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, ‖g x‖ ≤ C)
    (hLf : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖f x - f y‖ ≤ L * |x-y|)
    (hKg : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖g x - g y‖ ≤ K * |x-y|)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    ‖star (f x) * g x - star (f y) * g y‖ ≤ (L*C+B*K)*|x-y| := by
  have he : star (f x) * g x - star (f y) * g y =
      star (f x-f y) * g x + star (f y)*(g x-g y) := by
    rw [star_sub]
    ring
  rw [he]
  calc
    _ ≤ ‖star (f x-f y)*g x‖+‖star (f y)*(g x-g y)‖ := norm_add_le _ _
    _ = ‖f x-f y‖*‖g x‖+‖f y‖*‖g x-g y‖ := by simp only [norm_mul, norm_star]
    _ ≤ (L*|x-y|)*C+B*(K*|x-y|) := add_le_add
      (mul_le_mul (hLf x hx y hy) (hg x hx) (norm_nonneg _) (by positivity))
      (mul_le_mul (hf y hy) (hKg x hx y hy) (norm_nonneg _) hB)
    _ = _ := by ring

theorem fourier_product_norm_le_of_lipschitz
    (f g : ℝ → ℂ) {B C L K : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ B)
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, ‖g x‖ ≤ C)
    (hLf : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖f x - f y‖ ≤ L * |x-y|)
    (hKg : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖g x - g y‖ ≤ K * |x-y|)
    (θ η : ℝ) (hη : 0 < η)
    (hsep : ∀ p : ℤ, η ≤ |θ-2*Real.pi*p|)
    (N : ℕ) (hN : 0 < N) :
    ‖∑ k : Fin (N+1), Complex.exp (Complex.I*((k.val : ℝ)*θ : ℝ)) *
      (star (f ((k.val : ℝ)/N))*g ((k.val : ℝ)/N))‖ ≤
      Real.pi/(2*η)*(2*B*C+L*C+B*K) := by
  let q := Complex.exp (Complex.I*(θ : ℂ))
  let a : ℕ → ℂ := fun k => star (f ((k : ℝ)/N))*g ((k : ℝ)/N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : ‖q‖=1 := Complex.norm_exp_I_mul_ofReal θ
  have ht (k : ℕ) (hk : k ≤ N) : (k : ℝ)/N ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hNR).2 (by exact_mod_cast hk)⟩
  have hdiff (k : ℕ) (hk : k < N) : ‖a (k+1)-a k‖ ≤ (L*C+B*K)/N := by
    have h := product_sub_norm_le_of_lipschitz f g hB hC hL hK hf hg hLf hKg
      (ht (k+1) (by omega)) (ht k (by omega))
    have he : |((k+1 : ℕ) : ℝ)/N-(k : ℝ)/N| = 1/(N : ℝ) := by
      have he' : ((k+1 : ℕ) : ℝ)/N-(k : ℝ)/N = 1/(N : ℝ) := by
        push_cast
        ring
      rw [he', abs_of_nonneg (by positivity)]
    simpa only [a, he, mul_one_div] using h
  have ha (k : ℕ) (hk : k ≤ N) : ‖a k‖ ≤ B*C := by
    simp only [a, norm_mul, norm_star]
    exact mul_le_mul (hf _ (ht k hk)) (hg _ (ht k hk)) (norm_nonneg _) hB
  have hs : ∑ k ∈ Finset.range N, ‖a (k+1)-a k‖ ≤ L*C+B*K := by
    calc
      _ ≤ ∑ _k ∈ Finset.range N, (L*C+B*K)/(N : ℝ) :=
        Finset.sum_le_sum (fun k hk => hdiff k (Finset.mem_range.mp hk))
      _ = _ := by simp; field_simp
  have hb := geometric_weighted_sum_norm_bound q hq a N
  have hbound : ‖q-1‖*‖∑ k ∈ Finset.range (N+1), q^k*a k‖ ≤
      2*B*C+L*C+B*K := by
    have h0 := ha 0 (Nat.zero_le _)
    have hlast := ha N le_rfl
    linarith
  have hchord : (2/Real.pi)*η ≤ ‖q-1‖ := periodic_chord_lower θ η hsep
  have hpos : 0 < (2/Real.pi)*η := by positivity
  have hsmall := mul_le_mul_of_nonneg_right hchord
    (norm_nonneg (∑ k ∈ Finset.range (N+1), q^k*a k))
  have hquot : ‖∑ k ∈ Finset.range (N+1), q^k*a k‖ ≤
      Real.pi/(2*η)*(2*B*C+L*C+B*K) := by
    have he : (2*B*C+L*C+B*K)/((2/Real.pi)*η) =
        Real.pi/(2*η)*(2*B*C+L*C+B*K) := by field_simp
    rw [← he]
    exact (le_div_iff₀ hpos).2 (by simpa only [mul_comm] using hsmall.trans hbound)
  have hp (k : ℕ) : q^k = Complex.exp (Complex.I*((k : ℝ)*θ : ℝ)) := by
    dsimp [q]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← Fin.sum_univ_eq_sum_range] at hquot
  simpa only [hp, a] using hquot

theorem coefficientPolynomial_unit_derivative_le_exact_degree {s : ℕ} (hs : 0 < s)
    (c : Fin s → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Icc (0 : ℝ) 1, ‖coefficientPolynomialSignal c x‖ ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖deriv (coefficientPolynomialSignal c) x‖ ≤ 4*((s-1 : ℕ) : ℝ)^2*B := by
  have he : coefficientPolynomialSignal c = complexPolynomialSignal
      (realCoefficientPolynomial c) (imaginaryCoefficientPolynomial c) := by
    funext t
    exact coefficientPolynomialSignal_eq c t
  rw [he] at hbound ⊢
  exact complexPolynomial_unit_derivative_le_sharper
    (coefficientPolynomial_natDegree_le hs (fun j => (c j).re))
    (coefficientPolynomial_natDegree_le hs (fun j => (c j).im)) hB hbound hx

theorem inner_modulatedPolynomial_norm_le_of_sup {s t N : ℕ}
    (hs : 0 < s) (ht : 0 < t) (hN : 0 < N)
    (c : Fin s → ℂ) (d : Fin t → ℂ) (x y η : ℝ) (hη : 0 < η)
    (hsep : ∀ p : ℤ, η ≤ |y-x-2*Real.pi*p|)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hc : ∀ z ∈ Icc (0 : ℝ) 1, ‖coefficientPolynomialSignal c z‖ ≤ B)
    (hd : ∀ z ∈ Icc (0 : ℝ) 1, ‖coefficientPolynomialSignal d z‖ ≤ C) :
    ‖⟪modulatedPolynomial N x c, modulatedPolynomial N y d⟫_ℂ‖ ≤
      Real.pi/η*(1+2*(((s-1 : ℕ) : ℝ)^2+((t-1 : ℕ) : ℝ)^2))*B*C := by
  have hfc : Differentiable ℝ (coefficientPolynomialSignal c) := by
    rw [show coefficientPolynomialSignal c = complexPolynomialSignal
      (realCoefficientPolynomial c) (imaginaryCoefficientPolynomial c) by
      funext z; exact coefficientPolynomialSignal_eq c z]
    exact fun z => (hasDerivAt_complexPolynomialSignal _ _ z).differentiableAt
  have hfd : Differentiable ℝ (coefficientPolynomialSignal d) := by
    rw [show coefficientPolynomialSignal d = complexPolynomialSignal
      (realCoefficientPolynomial d) (imaginaryCoefficientPolynomial d) by
      funext z; exact coefficientPolynomialSignal_eq d z]
    exact fun z => (hasDerivAt_complexPolynomialSignal _ _ z).differentiableAt
  have hLc (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      ‖coefficientPolynomialSignal c u-coefficientPolynomialSignal c v‖ ≤
        (4*((s-1 : ℕ) : ℝ)^2*B)*|u-v| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Icc (0 : ℝ) 1)
      (x := v) (y := u) (fun z _ => hfc z)
      (fun z hz => coefficientPolynomial_unit_derivative_le_exact_degree hs c hB hc hz)
      (convex_Icc 0 1) hv hu
    simpa only [Real.norm_eq_abs] using h
  have hLd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      ‖coefficientPolynomialSignal d u-coefficientPolynomialSignal d v‖ ≤
        (4*((t-1 : ℕ) : ℝ)^2*C)*|u-v| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := Icc (0 : ℝ) 1)
      (x := v) (y := u) (fun z _ => hfd z)
      (fun z hz => coefficientPolynomial_unit_derivative_le_exact_degree ht d hC hd hz)
      (convex_Icc 0 1) hv hu
    simpa only [Real.norm_eq_abs] using h
  have h := fourier_product_norm_le_of_lipschitz
    (coefficientPolynomialSignal c) (coefficientPolynomialSignal d)
    hB hC (by positivity) (by positivity) hc hd hLc hLd (y-x) η hη hsep N hN
  have he : ⟪modulatedPolynomial N x c, modulatedPolynomial N y d⟫_ℂ =
      ∑ k : Fin (N+1), Complex.exp (Complex.I*((k.val : ℝ)*(y-x) : ℝ)) *
        (star (coefficientPolynomialSignal c ((k.val : ℝ)/N))*
          coefficientPolynomialSignal d ((k.val : ℝ)/N)) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro k _
    have hk : star (Complex.exp (Complex.I*((k.val : ℝ)*x : ℝ))*polynomialValue c k)*
        (Complex.exp (Complex.I*((k.val : ℝ)*y : ℝ))*polynomialValue d k) =
        Complex.exp (Complex.I*((k.val : ℝ)*(y-x) : ℝ))*
          (star (polynomialValue c k)*polynomialValue d k) := by
      rw [star_mul]
      calc
        _ = (star (Complex.exp (Complex.I*((k.val : ℝ)*x : ℝ)))*
            Complex.exp (Complex.I*((k.val : ℝ)*y : ℝ)))*
            (star (polynomialValue c k)*polynomialValue d k) := by ring
        _ = _ := by rw [star_phase_mul_phase x y k.val]
    simpa only [modulatedPolynomial, ofLp_toLp, RCLike.inner_apply', RCLike.star_def,
      coefficientPolynomialSignal, polynomialValue, Complex.ofReal_pow] using hk
  rw [he]
  convert h using 1
  field_simp
  ring

end
end LeanNumDetect.PolynomialCrossCorrelation
