import General.Fourier.SharpPolynomialEvaluation
import General.Fourier.SharperPolynomialEvaluation
import General.Fourier.UniformGridEvaluationBounds

/-! An exact affine cell integral halves the left-rectangle error. -/
set_option autoImplicit false
open scoped Polynomial BigOperators
open Set MeasureTheory
namespace LeanNumDetect.UniformGridEvaluationBounds
open ExponentialSumEstimates
noncomputable section

theorem integral_affine_left_cell (u v F L : ℝ) :
    (∫ t in u..v, F+L*(t-u))=(v-u)*F+L*(v-u)^2/2 := by
  rw [intervalIntegral.integral_add
    (show IntervalIntegrable (fun _ : ℝ => F) volume u v from continuous_const.intervalIntegrable _ _)
    (show IntervalIntegrable (fun t : ℝ => L*(t-u)) volume u v from
      (by fun_prop : Continuous (fun t : ℝ => L*(t-u))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      (show IntervalIntegrable (fun t : ℝ => t) volume u v from continuous_id.intervalIntegrable _ _)
      (show IntervalIntegrable (fun _ : ℝ => u) volume u v from continuous_const.intervalIntegrable _ _),
    integral_id, intervalIntegral.integral_const, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem integral_le_leftRiemannSum_add_half_error {F : ℝ → ℝ} (hF : Continuous F)
    {L : ℝ} (_hL : 0≤L)
    (hLip : ∀ u∈Icc (0 : ℝ) 1, ∀ t∈Icc (0 : ℝ) 1,
      F t≤F u+L*|t-u|) {M : ℕ} (hM : 0<M) :
    (∫ t in (0 : ℝ)..1, F t) ≤
      (∑ k∈Finset.range M, F ((k : ℝ)/M))/M+L/(2*M) := by
  have hMR : (0 : ℝ)<M := by exact_mod_cast hM
  have hM0 : (M : ℝ)≠0 := hMR.ne'
  let a : ℕ → ℝ := fun k => (k : ℝ)/M
  have ha0 : a 0=0 := by simp [a]
  have haM : a M=1 := by simp [a, hM0]
  have hstep (k : ℕ) : a (k+1)-a k=1/(M : ℝ) := by dsimp [a]; push_cast; ring
  have hcell (k : ℕ) (hk : k<M) :
      (∫ t in a k..a (k+1), F t)≤(1/(M : ℝ))*F (a k)+L/(2*(M : ℝ)^2) := by
    have hak : 0≤a k := by dsimp [a]; positivity
    have hab : a k≤a (k+1) := by
      have hh := hstep k
      have hpos : 0<1/(M : ℝ) := by positivity
      linarith
    have hab1 : a (k+1)≤1 := by
      dsimp [a]
      rw [div_le_one hMR]
      exact_mod_cast (show k+1≤M by omega)
    have hau : a k∈Icc (0 : ℝ) 1 := ⟨hak, hab.trans hab1⟩
    have h := intervalIntegral.integral_mono_on (μ := volume) hab
      (hF.intervalIntegrable _ _)
      (show IntervalIntegrable (fun t : ℝ => F (a k)+L*(t-a k)) volume (a k) (a (k+1)) from
        (by fun_prop : Continuous (fun t : ℝ => F (a k)+L*(t-a k))).intervalIntegrable _ _)
      (fun t ht => by
        have ht01 : t∈Icc (0 : ℝ) 1 := ⟨hak.trans ht.1, ht.2.trans hab1⟩
        simpa only [abs_of_nonneg (sub_nonneg.mpr ht.1)] using hLip (a k) hau t ht01)
    rw [integral_affine_left_cell, hstep] at h
    convert h using 1
    field_simp
  have hp := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (a := a) (n := M) (fun k _ => hF.intervalIntegrable (a k) (a (k+1)))
  rw [ha0, haM] at hp
  rw [← hp]
  calc
    _ ≤ ∑ k∈Finset.range M, ((1/(M : ℝ))*F (a k)+L/(2*(M : ℝ)^2)) :=
      Finset.sum_le_sum (fun k hk => hcell k (Finset.mem_range.mp hk))
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, a]
      field_simp [hM0]

theorem unitEnergy_mul_gridSize_sub_derivative_loss_le {f : ℝ → ℂ}
    (hf : Continuous f) (hfdiff : Differentiable ℝ f) {D q : ℝ}
    (hD : 0≤D) (_hq : 0≤q)
    (hsup : unitSupNorm f^2≤q*unitEnergy f)
    (hder : ∀ x∈Icc (0 : ℝ) 1, ‖deriv f x‖≤D*unitSupNorm f)
    {M : ℕ} (hM : 0<M) :
    unitEnergy f*((M : ℝ)-D*q)≤∑ k∈Finset.range (M+1), ‖f ((k : ℝ)/M)‖^2 := by
  let S := unitSupNorm f
  let I := unitEnergy f
  let Q := ∑ k∈Finset.range (M+1), ‖f ((k : ℝ)/M)‖^2
  have hMR : (0 : ℝ)<M := by exact_mod_cast hM
  have hR := integral_le_leftRiemannSum_add_half_error (hf.norm.pow 2)
    (by positivity : 0≤2*D*S^2)
    (fun u hu t ht => norm_sq_lipschitz_of_derivative_bound hf hfdiff hder hu ht) hM
  change I≤(∑ k∈Finset.range M, ‖f ((k : ℝ)/M)‖^2)/M+(2*D*S^2)/(2*M) at hR
  have he : (2*D*S^2)/(2*M)=D*S^2/M := by field_simp
  rw [he, ← add_div] at hR
  have hm := (le_div_iff₀ hMR).mp hR
  have hleft : (∑ k∈Finset.range M, ‖f ((k : ℝ)/M)‖^2)≤Q := by
    dsimp [Q]
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hs := mul_le_mul_of_nonneg_left hsup hD
  change D*S^2≤D*(q*I) at hs
  change I*((M : ℝ)-D*q)≤Q
  nlinarith only [hm, hleft, hs]

end
end LeanNumDetect.UniformGridEvaluationBounds

namespace LeanNumDetect.PolynomialEvaluationBounds
open ExponentialSumEstimates UniformGridEvaluationBounds
noncomputable section

theorem jetPolynomial_energy_mul_gridSize_sub_loss_le {s M : ℕ}
    (hs : 0<s) (hM : 0<M) (a : Fin s → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2)*
      ((M : ℝ)-4*((s-1 : ℕ) : ℝ)^2*(s : ℝ)^2)≤
      ∑ k∈Finset.range (M+1), ‖jetPolynomialSignal a ((k : ℝ)/M)‖^2 := by
  let f := jetPolynomialSignal a
  have hf : Continuous f := continuous_jetPolynomialSignal a
  have he : f=complexPolynomialSignal
      (realCoefficientPolynomial (fun j => a j/(j.val.factorial : ℂ)))
      (imaginaryCoefficientPolynomial (fun j => a j/(j.val.factorial : ℂ))) := by
    funext t
    change jetPolynomialSignal a t=_
    rw [jetPolynomialSignal_eq_coefficientPolynomialSignal]
    exact coefficientPolynomialSignal_eq _ t
  have hdiff : Differentiable ℝ f := by
    rw [he]
    exact fun t => (hasDerivAt_complexPolynomialSignal _ _ t).differentiableAt
  have hE : 0≤unitEnergy f := unitEnergy_nonneg f
  have hsbound : unitSupNorm f≤Real.sqrt ((s : ℝ)^2*unitEnergy f) := by
    apply unitSupNorm_le hf
    intro t ht
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt (mul_nonneg (sq_nonneg _) hE)]
    exact jetPolynomial_unit_row_bound_sharp hs a ht
  have hsup : unitSupNorm f^2≤(s : ℝ)^2*unitEnergy f := by
    have h := (sq_le_sq₀ (unitSupNorm_nonneg hf) (Real.sqrt_nonneg _)).2 hsbound
    rwa [Real.sq_sqrt (mul_nonneg (sq_nonneg _) hE)] at h
  have hder : ∀ x∈Icc (0 : ℝ) 1,
      ‖deriv f x‖≤(4*((s-1 : ℕ) : ℝ)^2)*unitSupNorm f := by
    intro x hx
    have h := complexPolynomial_unit_derivative_le_sharper
      (coefficientPolynomial_natDegree_le hs (fun j => (a j/(j.val.factorial : ℂ)).re))
      (coefficientPolynomial_natDegree_le hs (fun j => (a j/(j.val.factorial : ℂ)).im))
      (unitSupNorm_nonneg hf)
      (fun t ht => by simpa only [he, realCoefficientPolynomial, imaginaryCoefficientPolynomial]
        using norm_le_unitSupNorm hf ht) hx
    simpa only [he, realCoefficientPolynomial, imaginaryCoefficientPolynomial] using h
  exact unitEnergy_mul_gridSize_sub_derivative_loss_le hf hdiff
    (by positivity) (sq_nonneg _) hsup hder hM

end
end LeanNumDetect.PolynomialEvaluationBounds
