import General.Fourier.QuantitativePolynomialCrossCorrelation
import General.Fourier.QuantitativePolynomialL2Derivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Discrete Abel bounds controlled by the continuous total variation.
The Cauchy--Schwarz estimate separates the two polynomial energies. -/

set_option autoImplicit false
open scoped BigOperators InnerProductSpace Polynomial
open Set MeasureTheory WithLp

namespace LeanNumDetect.PolynomialCrossCorrelation
open PolynomialEvaluationBounds
noncomputable section

theorem unitIntegral_mul_le_sqrt_energy (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, f t*g t) ≤
      Real.sqrt (∫ t in (0 : ℝ)..1, (f t)^2) *
        Real.sqrt (∫ t in (0 : ℝ)..1, (g t)^2) := by
  let A := ∫ t in (0 : ℝ)..1, (f t)^2
  let B := ∫ t in (0 : ℝ)..1, f t*g t
  let C := ∫ t in (0 : ℝ)..1, (g t)^2
  have hA : 0≤A := intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun t => sq_nonneg _)
  have hC : 0≤C := intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun t => sq_nonneg _)
  have hquad (x : ℝ) : 0≤A*(x*x)+(-2*B)*x+C := by
    have h := intervalIntegral.integral_nonneg_of_forall (μ := volume)
      (a := (0 : ℝ)) (b := 1) (by norm_num) (fun t => sq_nonneg (x*f t-g t))
    have he : (fun t => (x*f t-g t)^2) =
        (fun t => x^2*(f t)^2-2*x*(f t*g t)+(g t)^2) := by funext t; ring
    rw [he] at h
    rw [intervalIntegral.integral_add
      (show IntervalIntegrable (fun t => x^2*(f t)^2-2*x*(f t*g t)) volume 0 1 from
        (by fun_prop : Continuous (fun t => x^2*(f t)^2-2*x*(f t*g t))).intervalIntegrable 0 1)
        (show IntervalIntegrable (fun t => (g t)^2) volume 0 1 from (hg.pow 2).intervalIntegrable 0 1),
      intervalIntegral.integral_sub
        (show IntervalIntegrable (fun t => x^2*(f t)^2) volume 0 1 from
          (by fun_prop : Continuous (fun t => x^2*(f t)^2)).intervalIntegrable 0 1)
        (show IntervalIntegrable (fun t => 2*x*(f t*g t)) volume 0 1 from
          (by fun_prop : Continuous (fun t => 2*x*(f t*g t))).intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    dsimp [A, B, C]
    convert h using 1
    ring
  have hd := discrim_le_zero hquad
  have hs : B^2≤A*C := by
    dsimp [discrim] at hd
    nlinarith
  have hrs := Real.sq_sqrt hA
  have hrc := Real.sq_sqrt hC
  have hpos : 0≤Real.sqrt A*Real.sqrt C := by positivity
  change B≤Real.sqrt A*Real.sqrt C
  nlinarith [sq_nonneg (B-Real.sqrt A*Real.sqrt C)]

theorem grid_variation_le_integral_derivative (f : ℝ → ℂ)
    (hf : Continuous f) (hd : Differentiable ℝ f)
    (hdf : Continuous (deriv f)) (N : ℕ) (hN : 0<N) :
    (∑ k∈Finset.range N, ‖f (((k+1 : ℕ) : ℝ)/N)-f ((k : ℝ)/N)‖) ≤
      ∫ t in (0 : ℝ)..1, ‖deriv f t‖ := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  let a : ℕ → ℝ := fun k => (k : ℝ)/N
  have hcell (k : ℕ) : ‖f (a (k+1))-f (a k)‖ ≤
      ∫ t in a k..a (k+1), ‖deriv f t‖ := by
    apply norm_sub_le_integral_of_norm_deriv_le_of_le
      (show a k≤a (k+1) by dsimp [a]; gcongr; omega)
      hf.continuousOn hd.differentiableOn
      (Filter.Eventually.of_forall (fun t _ => le_rfl))
      (hdf.norm.intervalIntegrable _ _)
  have hs := Finset.sum_le_sum (s := Finset.range N) (fun k _ => hcell k)
  have hi := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := a) (n := N) (fun k _ => hdf.norm.intervalIntegrable (a k) (a (k+1)))
  rw [hi] at hs
  simpa [a, hNR.ne'] using hs

theorem fourier_weighted_norm_le_of_variation (f : ℝ → ℂ)
    (hf : Continuous f) (hd : Differentiable ℝ f) (hdf : Continuous (deriv f))
    (θ η : ℝ) (hη : 0<η)
    (hsep : ∀ p : ℤ, η≤|θ-2*Real.pi*p|) (N : ℕ) (hN : 0<N) :
    ‖∑ k : Fin (N+1), Complex.exp (Complex.I*((k.val : ℝ)*θ : ℝ))*
      f ((k.val : ℝ)/N)‖ ≤
      Real.pi/(2*η)*(‖f 0‖+‖f 1‖+∫ t in (0 : ℝ)..1, ‖deriv f t‖) := by
  let q := Complex.exp (Complex.I*(θ : ℂ))
  let a : ℕ → ℂ := fun k => f ((k : ℝ)/N)
  have hq : ‖q‖=1 := Complex.norm_exp_I_mul_ofReal θ
  have h := geometric_weighted_sum_norm_bound q hq a N
  have hv := grid_variation_le_integral_derivative f hf hd hdf N hN
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hb : ‖q-1‖*‖∑ k∈Finset.range (N+1), q^k*a k‖ ≤
      ‖f 0‖+‖f 1‖+∫ t in (0 : ℝ)..1, ‖deriv f t‖ := by
    simp only [a, Nat.cast_zero, zero_div, div_self hNR.ne'] at h
    apply h.trans
    simpa only [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hv (‖f 0‖+‖f 1‖)
  have hchord : (2/Real.pi)*η≤‖q-1‖ := periodic_chord_lower θ η hsep
  have hpos : 0<(2/Real.pi)*η := by positivity
  have hm := mul_le_mul_of_nonneg_right hchord
    (norm_nonneg (∑ k∈Finset.range (N+1), q^k*a k))
  have hquot : ‖∑ k∈Finset.range (N+1), q^k*a k‖ ≤
      Real.pi/(2*η)*(‖f 0‖+‖f 1‖+∫ t in (0 : ℝ)..1, ‖deriv f t‖) := by
    have he : (‖f 0‖+‖f 1‖+∫ t in (0 : ℝ)..1, ‖deriv f t‖)/((2/Real.pi)*η)=
        Real.pi/(2*η)*(‖f 0‖+‖f 1‖+∫ t in (0 : ℝ)..1, ‖deriv f t‖) := by field_simp
    rw [← he]
    exact (le_div_iff₀ hpos).2 (by simpa only [mul_comm] using hm.trans hb)
  have hp (k : ℕ) : q^k=Complex.exp (Complex.I*((k : ℝ)*θ : ℝ)) := by
    dsimp [q]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← Fin.sum_univ_eq_sum_range] at hquot
  simpa only [hp, a] using hquot

theorem product_derivative_variation_le_energy (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hfd : Differentiable ℝ f) (hgd : Differentiable ℝ g)
    (hdf : Continuous (deriv f)) (hdg : Continuous (deriv g)) :
    (∫ t in (0 : ℝ)..1, ‖deriv (fun t => star (f t)*g t) t‖) ≤
      Real.sqrt (∫ t in (0 : ℝ)..1, ‖deriv f t‖^2)*
        Real.sqrt (∫ t in (0 : ℝ)..1, ‖g t‖^2)+
      Real.sqrt (∫ t in (0 : ℝ)..1, ‖f t‖^2)*
        Real.sqrt (∫ t in (0 : ℝ)..1, ‖deriv g t‖^2) := by
  have he (t : ℝ) : deriv (fun t => star (f t)*g t) t =
      star (deriv f t)*g t+star (f t)*deriv g t :=
    ((hfd t).hasDerivAt.star.mul ((hgd t).hasDerivAt)).deriv
  have hcont : Continuous (fun t => deriv (fun t => star (f t)*g t) t) := by
    simp_rw [he]
    exact (hdf.star.mul hg).add (hf.star.mul hdg)
  have hm := intervalIntegral.integral_mono_on (μ := volume) (a := (0 : ℝ)) (b := 1)
    (by norm_num) (hcont.norm.intervalIntegrable 0 1)
    (show IntervalIntegrable (fun t => ‖deriv f t‖*‖g t‖+‖f t‖*‖deriv g t‖) volume 0 1 from
      (by fun_prop : Continuous (fun t => ‖deriv f t‖*‖g t‖+‖f t‖*‖deriv g t‖)).intervalIntegrable 0 1)
    (fun t _ => by
      rw [he]
      simpa only [norm_mul, norm_star] using norm_add_le
        (star (deriv f t)*g t) (star (f t)*deriv g t))
  rw [intervalIntegral.integral_add
    (show IntervalIntegrable (fun t => ‖deriv f t‖*‖g t‖) volume 0 1 from
      (by fun_prop : Continuous (fun t => ‖deriv f t‖*‖g t‖)).intervalIntegrable 0 1)
    (show IntervalIntegrable (fun t => ‖f t‖*‖deriv g t‖) volume 0 1 from
      (by fun_prop : Continuous (fun t => ‖f t‖*‖deriv g t‖)).intervalIntegrable 0 1)] at hm
  exact hm.trans (add_le_add
    (unitIntegral_mul_le_sqrt_energy _ _ hdf.norm hg.norm)
    (unitIntegral_mul_le_sqrt_energy _ _ hf.norm hdg.norm))

theorem fourier_product_norm_le_of_energy (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hfd : Differentiable ℝ f) (hgd : Differentiable ℝ g)
    (hdf : Continuous (deriv f)) (hdg : Continuous (deriv g))
    {B C D K : ℝ} (hB : 0≤B) (_hC : 0≤C) (_hD : 0≤D) (_hK : 0≤K)
    (hfend : ∀ t∈({0,1} : Set ℝ), ‖f t‖≤B*Real.sqrt (∫ z in (0 : ℝ)..1, ‖f z‖^2))
    (hgend : ∀ t∈({0,1} : Set ℝ), ‖g t‖≤C*Real.sqrt (∫ z in (0 : ℝ)..1, ‖g z‖^2))
    (hfder : Real.sqrt (∫ z in (0 : ℝ)..1, ‖deriv f z‖^2)≤
      D*Real.sqrt (∫ z in (0 : ℝ)..1, ‖f z‖^2))
    (hgder : Real.sqrt (∫ z in (0 : ℝ)..1, ‖deriv g z‖^2)≤
      K*Real.sqrt (∫ z in (0 : ℝ)..1, ‖g z‖^2))
    (θ η : ℝ) (hη : 0<η) (hsep : ∀ p : ℤ, η≤|θ-2*Real.pi*p|)
    (N : ℕ) (hN : 0<N) :
    ‖∑ k : Fin (N+1), Complex.exp (Complex.I*((k.val : ℝ)*θ : ℝ))*
      (star (f ((k.val : ℝ)/N))*g ((k.val : ℝ)/N))‖ ≤
      Real.pi/(2*η)*(2*B*C+D+K)*
        Real.sqrt (∫ z in (0 : ℝ)..1, ‖f z‖^2)*
        Real.sqrt (∫ z in (0 : ℝ)..1, ‖g z‖^2) := by
  have he (t : ℝ) : deriv (fun t => star (f t)*g t) t =
      star (deriv f t)*g t+star (f t)*deriv g t :=
    ((hfd t).hasDerivAt.star.mul ((hgd t).hasDerivAt)).deriv
  have hcont : Continuous (fun t => deriv (fun t => star (f t)*g t) t) := by
    simp_rw [he]
    exact (hdf.star.mul hg).add (hf.star.mul hdg)
  have hdiff : Differentiable ℝ (fun t => star (f t)*g t) := by
    intro t
    exact ((hfd t).hasDerivAt.star.mul ((hgd t).hasDerivAt)).differentiableAt
  have h := fourier_weighted_norm_le_of_variation (fun t => star (f t)*g t)
    (hf.star.mul hg) hdiff hcont θ η hη hsep N hN
  have hend (t : ℝ) (ht : t∈({0,1} : Set ℝ)) : ‖star (f t)*g t‖ ≤
      B*C*Real.sqrt (∫ z in (0 : ℝ)..1, ‖f z‖^2)*
        Real.sqrt (∫ z in (0 : ℝ)..1, ‖g z‖^2) := by
    simp only [norm_mul, norm_star]
    calc
      _ ≤ (B*Real.sqrt (∫ z in (0 : ℝ)..1, ‖f z‖^2))*
          (C*Real.sqrt (∫ z in (0 : ℝ)..1, ‖g z‖^2)) :=
        mul_le_mul (hfend t ht) (hgend t ht) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hv := product_derivative_variation_le_energy f g hf hg hfd hgd hdf hdg
  have hv' := hv.trans (add_le_add
    (mul_le_mul_of_nonneg_right hfder (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_left hgder (Real.sqrt_nonneg _)))
  apply h.trans
  calc
    _ ≤ Real.pi/(2*η)*(
        B*C*Real.sqrt (∫ z in (0 : ℝ)..1, ‖f z‖^2)*
          Real.sqrt (∫ z in (0 : ℝ)..1, ‖g z‖^2)+
        B*C*Real.sqrt (∫ z in (0 : ℝ)..1, ‖f z‖^2)*
          Real.sqrt (∫ z in (0 : ℝ)..1, ‖g z‖^2)+
        (D*Real.sqrt (∫ z in (0 : ℝ)..1, ‖f z‖^2))*
          Real.sqrt (∫ z in (0 : ℝ)..1, ‖g z‖^2)+
        Real.sqrt (∫ z in (0 : ℝ)..1, ‖f z‖^2)*
          (K*Real.sqrt (∫ z in (0 : ℝ)..1, ‖g z‖^2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h0 := hend 0 (by simp)
      have h1 := hend 1 (by simp)
      linarith
    _ = _ := by ring

theorem coefficientPolynomial_continuous {s : ℕ} (c : Fin s → ℂ) :
    Continuous (coefficientPolynomialSignal c) := by
  have he : coefficientPolynomialSignal c=complexPolynomialSignal
      (realCoefficientPolynomial c) (imaginaryCoefficientPolynomial c) :=
    funext (coefficientPolynomialSignal_eq c)
  rw [he]
  exact continuous_complexPolynomialSignal _ _

theorem coefficientPolynomial_differentiable {s : ℕ} (c : Fin s → ℂ) :
    Differentiable ℝ (coefficientPolynomialSignal c) := by
  have he : coefficientPolynomialSignal c=complexPolynomialSignal
      (realCoefficientPolynomial c) (imaginaryCoefficientPolynomial c) :=
    funext (coefficientPolynomialSignal_eq c)
  rw [he]
  exact fun t => (hasDerivAt_complexPolynomialSignal _ _ t).differentiableAt

theorem coefficientPolynomial_deriv_continuous {s : ℕ} (c : Fin s → ℂ) :
    Continuous (deriv (coefficientPolynomialSignal c)) := by
  have he : coefficientPolynomialSignal c=complexPolynomialSignal
      (realCoefficientPolynomial c) (imaginaryCoefficientPolynomial c) :=
    funext (coefficientPolynomialSignal_eq c)
  rw [he]
  rw [show deriv (complexPolynomialSignal (realCoefficientPolynomial c)
      (imaginaryCoefficientPolynomial c))=complexPolynomialSignal
      (realCoefficientPolynomial c).derivative (imaginaryCoefficientPolynomial c).derivative
    from funext (complexPolynomialSignal_deriv _ _)]
  exact continuous_complexPolynomialSignal _ _

theorem coefficientPolynomial_point_le_energy {s : ℕ} (hs : 0<s)
    (c : Fin s → ℂ) {x : ℝ} (hx : x∈Icc (0 : ℝ) 1) :
    ‖coefficientPolynomialSignal c x‖ ≤
      (s : ℝ)*Real.sqrt (∫ t in (0 : ℝ)..1, ‖coefficientPolynomialSignal c t‖^2) := by
  have he : coefficientPolynomialSignal c=complexPolynomialSignal
      (realCoefficientPolynomial c) (imaginaryCoefficientPolynomial c) :=
    funext (coefficientPolynomialSignal_eq c)
  have h := complexPolynomial_unit_row_bound_sharp
    (coefficientPolynomial_natDegree_le hs (fun j => (c j).re))
    (coefficientPolynomial_natDegree_le hs (fun j => (c j).im)) hx
  have hsR : ((s-1 : ℕ) : ℝ)+1=s := by exact_mod_cast (Nat.sub_add_cancel hs)
  have hE : 0≤∫ t in (0 : ℝ)..1, ‖coefficientPolynomialSignal c t‖^2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun t => sq_nonneg _)
  change ‖complexPolynomialSignal (realCoefficientPolynomial c)
    (imaginaryCoefficientPolynomial c) x‖^2≤((↑(s-1) : ℝ)+1)^2*
    (∫ t in (0 : ℝ)..1, ‖complexPolynomialSignal (realCoefficientPolynomial c)
      (imaginaryCoefficientPolynomial c) t‖^2) at h
  rw [← he, hsR] at h
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  simpa only [mul_pow, Real.sq_sqrt hE] using h

theorem coefficientPolynomial_derivative_sqrt_energy_le {s nstar : ℕ}
    (hs : 0<s) (hsn : s≤nstar) (c : Fin s → ℂ) :
    Real.sqrt (∫ t in (0 : ℝ)..1, ‖deriv (coefficientPolynomialSignal c) t‖^2) ≤
      (nstar : ℝ)*Real.sqrt ((nstar : ℝ)^2-1)*
        Real.sqrt (∫ t in (0 : ℝ)..1, ‖coefficientPolynomialSignal c t‖^2) := by
  have hE : 0≤∫ t in (0 : ℝ)..1, ‖coefficientPolynomialSignal c t‖^2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun t => sq_nonneg _)
  have hD : 0≤∫ t in (0 : ℝ)..1, ‖deriv (coefficientPolynomialSignal c) t‖^2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun t => sq_nonneg _)
  have hsR : (1 : ℝ)≤s := by exact_mod_cast (show 1≤s from hs)
  have hsnR : (s : ℝ)≤nstar := by exact_mod_cast hsn
  have hnR : (1 : ℝ)≤nstar := hsR.trans hsnR
  have hn : 0≤(nstar : ℝ)^2-1 := by nlinarith
  have hmono : (s : ℝ)^2*((s : ℝ)^2-1)≤(nstar : ℝ)^2*((nstar : ℝ)^2-1) := by
    apply mul_le_mul
      ((sq_le_sq₀ (by positivity) (by positivity)).2 hsnR)
      (by nlinarith) (by nlinarith) (by positivity)
  have h := (coefficientPolynomial_derivative_energy_le_explicit hs c).trans
    (mul_le_mul_of_nonneg_right hmono hE)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
  simpa only [mul_pow, Real.sq_sqrt hD, Real.sq_sqrt hn, Real.sq_sqrt hE,
    mul_assoc] using h

theorem inner_modulatedPolynomial_eq_fourier_product {s t N : ℕ}
    (c : Fin s → ℂ) (d : Fin t → ℂ) (x y : ℝ) :
    ⟪modulatedPolynomial N x c, modulatedPolynomial N y d⟫_ℂ =
      ∑ k : Fin (N+1), Complex.exp (Complex.I*((k.val : ℝ)*(y-x) : ℝ))*
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

theorem inner_modulatedPolynomial_norm_le_of_size_energy {s t N : ℕ}
    (hs : 0<s) (ht : 0<t) (hN : 0<N)
    (c : Fin s → ℂ) (d : Fin t → ℂ) (x y η : ℝ) (hη : 0<η)
    (hsep : ∀ p : ℤ, η≤|y-x-2*Real.pi*p|) :
    ‖⟪modulatedPolynomial N x c, modulatedPolynomial N y d⟫_ℂ‖ ≤
      (Real.pi/η)*((s : ℝ)*(t : ℝ)+((s : ℝ)^2+(t : ℝ)^2)/2)*
        Real.sqrt (∫ z in (0 : ℝ)..1, ‖coefficientPolynomialSignal c z‖^2)*
        Real.sqrt (∫ z in (0 : ℝ)..1, ‖coefficientPolynomialSignal d z‖^2) := by
  have hpoint {v : ℕ} (hv : 0<v) (a : Fin v → ℂ)
      (z : ℝ) (hz : z∈({0,1} : Set ℝ)) :
      ‖coefficientPolynomialSignal a z‖≤
        (v : ℝ)*Real.sqrt (∫ u in (0 : ℝ)..1, ‖coefficientPolynomialSignal a u‖^2) := by
    have hz01 : z∈Icc (0 : ℝ) 1 := by rcases hz with hz|hz <;> simp_all
    exact coefficientPolynomial_point_le_energy hv a hz01
  have hder {v : ℕ} (hv : 0<v) (a : Fin v → ℂ) :
      Real.sqrt (∫ z in (0 : ℝ)..1, ‖deriv (coefficientPolynomialSignal a) z‖^2)≤
        (v : ℝ)^2*Real.sqrt (∫ z in (0 : ℝ)..1, ‖coefficientPolynomialSignal a z‖^2) := by
    have hsqrt : Real.sqrt ((v : ℝ)^2-1)≤v := by
      have h := Real.sqrt_le_sqrt (sub_le_self ((v : ℝ)^2) (by norm_num : (0 : ℝ)≤1))
      rw [Real.sqrt_sq (show (0 : ℝ)≤v from Nat.cast_nonneg v)] at h
      exact h
    exact (coefficientPolynomial_derivative_sqrt_energy_le hv le_rfl a).trans
      (mul_le_mul_of_nonneg_right
        (by simpa only [pow_two] using
          mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg v)) (Real.sqrt_nonneg _))
  have h := fourier_product_norm_le_of_energy
    (coefficientPolynomialSignal c) (coefficientPolynomialSignal d)
    (coefficientPolynomial_continuous c) (coefficientPolynomial_continuous d)
    (coefficientPolynomial_differentiable c) (coefficientPolynomial_differentiable d)
    (coefficientPolynomial_deriv_continuous c) (coefficientPolynomial_deriv_continuous d)
    (B := (s : ℝ)) (C := (t : ℝ)) (D := (s : ℝ)^2) (K := (t : ℝ)^2)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (hpoint hs c) (hpoint ht d) (hder hs c) (hder ht d)
    (y-x) η hη hsep N hN
  rw [inner_modulatedPolynomial_eq_fourier_product]
  convert h using 1
  field_simp
  ring

/-- The multiplicity-squared cross coefficient obtained from the exact
Legendre derivative energy, rather than a sup-norm Markov estimate. -/
theorem inner_modulatedPolynomial_norm_le_of_energy {s t N nstar : ℕ}
    (hs : 0<s) (ht : 0<t) (hN : 0<N) (hsn : s≤nstar) (htn : t≤nstar)
    (c : Fin s → ℂ) (d : Fin t → ℂ) (x y η : ℝ) (hη : 0<η)
    (hsep : ∀ p : ℤ, η≤|y-x-2*Real.pi*p|) :
    ‖⟪modulatedPolynomial N x c, modulatedPolynomial N y d⟫_ℂ‖ ≤
      (Real.pi/η)*((nstar : ℝ)^2+(nstar : ℝ)*Real.sqrt ((nstar : ℝ)^2-1))*
        Real.sqrt (∫ z in (0 : ℝ)..1, ‖coefficientPolynomialSignal c z‖^2)*
        Real.sqrt (∫ z in (0 : ℝ)..1, ‖coefficientPolynomialSignal d z‖^2) := by
  have hpoint {v : ℕ} (hv : 0<v) (hvn : v≤nstar) (a : Fin v → ℂ)
      (z : ℝ) (hz : z∈({0,1} : Set ℝ)) :
      ‖coefficientPolynomialSignal a z‖≤
        (nstar : ℝ)*Real.sqrt (∫ u in (0 : ℝ)..1, ‖coefficientPolynomialSignal a u‖^2) := by
    have hz01 : z∈Icc (0 : ℝ) 1 := by rcases hz with hz|hz <;> simp_all
    exact (coefficientPolynomial_point_le_energy hv a hz01).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hvn) (Real.sqrt_nonneg _))
  have h := fourier_product_norm_le_of_energy
    (coefficientPolynomialSignal c) (coefficientPolynomialSignal d)
    (coefficientPolynomial_continuous c) (coefficientPolynomial_continuous d)
    (coefficientPolynomial_differentiable c) (coefficientPolynomial_differentiable d)
    (coefficientPolynomial_deriv_continuous c) (coefficientPolynomial_deriv_continuous d)
    (B := (nstar : ℝ)) (C := (nstar : ℝ))
    (D := (nstar : ℝ)*Real.sqrt ((nstar : ℝ)^2-1))
    (K := (nstar : ℝ)*Real.sqrt ((nstar : ℝ)^2-1))
    (by positivity) (by positivity) (by positivity) (by positivity)
    (hpoint hs hsn c) (hpoint ht htn d)
    (coefficientPolynomial_derivative_sqrt_energy_le hs hsn c)
    (coefficientPolynomial_derivative_sqrt_energy_le ht htn d)
    (y-x) η hη hsep N hN
  rw [inner_modulatedPolynomial_eq_fourier_product]
  convert h using 1
  field_simp
  ring

end
end LeanNumDetect.PolynomialCrossCorrelation
