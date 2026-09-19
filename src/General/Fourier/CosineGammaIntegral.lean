import General.Fourier.NormalizedCosineIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Topology.Instances.Irrational
import Mathlib.Analysis.Convex.Jensen
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped Topology BigOperators
namespace LeanNumDetect

/-- The zero-frequency integral, in factorial form. -/
theorem cosineHalfMass_eq_factorial (n : ℕ) :
    cosineHalfMass n = Real.pi * ((2*n).factorial : ℝ) /
      (2 * 4^n * (n.factorial : ℝ)^2) := by
  induction n with
  | zero => simp [cosineHalfMass]
  | succ n ih =>
    rw [cosineHalfMass_succ, ih]
    rw [show 2*(n+1) = (2*n+1)+1 by omega]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, pow_succ]
    field_simp
    ring

/-- The base integral in the manuscript's recurrence. -/
theorem normalizedCosineIntegral_base {v : ℝ} (hv : v ≠ 0) :
    normalizedCosineIntegral 0 v = Real.sin (Real.pi*v)/(Real.pi*v) := by
  have hi := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ))
    (b := Real.pi/2) Real.cos (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hv)
  simp only [mul_zero, integral_cos, Real.sin_zero, sub_zero, smul_eq_mul] at hi
  unfold normalizedCosineIntegral cosineHalfMass
  simp only [mul_zero, pow_zero, mul_one, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  have he : 2*v*(Real.pi/2) = Real.pi*v := by ring
  rw [hi, he]
  field_simp

/-- Euler reflection identifies the two Gamma factors at the base index. -/
theorem gamma_pair_base {v : ℝ} (hv : ∀ k : ℤ, v ≠ k) :
    normalizedCosineIntegral 0 v * Real.Gamma (1+v) * Real.Gamma (1-v) = 1 := by
  have hv0 : v ≠ 0 := by simpa using hv 0
  have hs : Real.sin (Real.pi*v) ≠ 0 := by
    rw [Real.sin_ne_zero_iff]
    intro k hk
    apply hv k
    nlinarith [Real.pi_pos]
  rw [normalizedCosineIntegral_base hv0, add_comm 1 v, Real.Gamma_add_one hv0]
  have hg := Real.Gamma_mul_Gamma_one_sub v
  calc
    _ = (Real.sin (Real.pi*v)/(Real.pi*v))*v*
        (Real.Gamma v*Real.Gamma (1-v)) := by ring
    _ = _ := by rw [hg]; field_simp

/-- Iterate the integral and Gamma recurrences away from integer parameters. -/
theorem normalizedCosineIntegral_gamma_mul_noninteger (n : ℕ) {v : ℝ}
    (hv : ∀ k : ℤ, v ≠ k) :
    normalizedCosineIntegral n v * Real.Gamma (n+1+v) * Real.Gamma (n+1-v) =
      (n.factorial : ℝ)^2 := by
  induction n with
  | zero => simpa using gamma_pair_base hv
  | succ n ih =>
    have hp : (n+1 : ℝ)+v ≠ 0 := by
      intro h
      apply hv (-(n+1 : ℤ))
      push_cast
      linarith
    have hm : (n+1 : ℝ)-v ≠ 0 := by
      intro h
      apply hv (n+1)
      push_cast
      linarith
    rw [normalizedCosineIntegral_recurrence n v] at ih
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at ih ⊢
    rw [show (n : ℝ)+1+1+v = (n+1+v)+1 by ring,
      show (n : ℝ)+1+1-v = (n+1-v)+1 by ring,
      Real.Gamma_add_one hp, Real.Gamma_add_one hm]
    field_simp at ih
    nlinarith [ih]

/-- Continuity supplies the integer parameters omitted by the reflection argument. -/
theorem continuous_normalizedCosineIntegral (n : ℕ) :
    Continuous (normalizedCosineIntegral n) := by
  have hi : Continuous (fun v : ℝ => ∫ x in (0 : ℝ)..Real.pi/2,
      Real.cos (2*v*x)*Real.cos x^(2*n)) := by
    simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi/2),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  exact hi.div_const _

theorem normalizedCosineIntegral_gamma_mul (n : ℕ) {v : ℝ} (hv : |v| < n+1) :
    normalizedCosineIntegral n v * Real.Gamma (n+1+v) * Real.Gamma (n+1-v) =
      (n.factorial : ℝ)^2 := by
  have hp : 0 < (n+1 : ℝ)+v := by have := (abs_lt.mp hv).1; linarith
  have hm : 0 < (n+1 : ℝ)-v := by have := (abs_lt.mp hv).2; linarith
  have hG {x : ℝ} (hx : 0 < x) : ContinuousAt Real.Gamma x :=
    (Real.differentiableAt_Gamma (fun m => by have := Nat.cast_nonneg (α := ℝ) m; linarith)).continuousAt
  have hc : ContinuousAt (fun w : ℝ => normalizedCosineIntegral n w *
      Real.Gamma (n+1+w) * Real.Gamma (n+1-w)) v :=
    ((continuous_normalizedCosineIntegral n).continuousAt.mul
      ((hG hp).comp (by fun_prop))).mul ((hG hm).comp (by fun_prop))
  apply tendsto_nhds_unique_of_frequently_eq hc.tendsto tendsto_const_nhds
  have hd : ∃ᶠ w in 𝓝 v, Irrational w := mem_closure_iff_frequently.mp (dense_irrational v)
  exact hd.mono (fun w hw => normalizedCosineIntegral_gamma_mul_noninteger n hw.ne_int)

/-- The normalized Gamma expression, including all integer points in the core interval. -/
theorem normalizedCosineIntegral_eq_gamma (n : ℕ) {v : ℝ} (hv : |v| < n+1) :
    normalizedCosineIntegral n v = (n.factorial : ℝ)^2 /
      (Real.Gamma (n+1+v)*Real.Gamma (n+1-v)) := by
  have hp : 0 < (n+1 : ℝ)+v := by have := (abs_lt.mp hv).1; linarith
  have hm : 0 < (n+1 : ℝ)-v := by have := (abs_lt.mp hv).2; linarith
  apply (eq_div_iff (mul_ne_zero (Real.Gamma_pos_of_pos hp).ne'
    (Real.Gamma_pos_of_pos hm).ne')).2
  simpa only [mul_assoc] using normalizedCosineIntegral_gamma_mul n hv

/-- Convexity and symmetry bound the Gamma product by its endpoint value. -/
theorem gamma_pair_le_factorial (n : ℕ) {v : ℝ} (hv : |v| ≤ n) :
    Real.Gamma (n+1+v)*Real.Gamma (n+1-v) ≤ ((2*n).factorial : ℝ) := by
  let g (w : ℝ) := Real.log (Real.Gamma (n+1+w))+Real.log (Real.Gamma (n+1-w))
  have hpos {w : ℝ} (hw : w ∈ Set.Icc (-(n : ℝ)) n) :
      0 < (n+1 : ℝ)+w ∧ 0 < (n+1 : ℝ)-w := by constructor <;> linarith [hw.1,hw.2]
  have hc : ConvexOn ℝ (Set.Icc (-(n : ℝ)) n) g := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hp := Real.convexOn_log_Gamma.2 (hpos hx).1 (hpos hy).1 ha hb hab
    have hm := Real.convexOn_log_Gamma.2 (hpos hx).2 (hpos hy).2 ha hb hab
    simp only [Function.comp_def, smul_eq_mul] at hp hm ⊢
    have he₁ : (n+1 : ℝ)+(a*x+b*y) = a*(n+1+x)+b*(n+1+y) := by nlinarith [hab]
    have he₂ : (n+1 : ℝ)-(a*x+b*y) = a*(n+1-x)+b*(n+1-y) := by nlinarith [hab]
    dsimp only [g]
    rw [he₁,he₂]
    nlinarith [hp,hm]
  have he₁ : g (-(n : ℝ)) = Real.log ((2*n).factorial : ℝ) := by
    dsimp [g]
    rw [show (n+1 : ℝ)+ -(n : ℝ) = 1 by ring,
      show (n+1 : ℝ)- -(n : ℝ) = (2*n : ℕ)+1 by push_cast; ring,
      Real.Gamma_one,Real.Gamma_nat_eq_factorial,Real.log_one,zero_add]
  have he₂ : g (n : ℝ) = Real.log ((2*n).factorial : ℝ) := by
    dsimp [g]
    rw [show (n+1 : ℝ)+n = (2*n : ℕ)+1 by push_cast; ring,
      show (n+1 : ℝ)-n = 1 by ring,
      Real.Gamma_one,Real.Gamma_nat_eq_factorial,Real.log_one,add_zero]
  have hv' : v ∈ Set.Icc (-(n : ℝ)) n := abs_le.mp hv
  have hh := hc.le_max_of_mem_Icc
    (show -(n : ℝ) ∈ Set.Icc (-(n : ℝ)) n by constructor <;> simp)
    (show (n : ℝ) ∈ Set.Icc (-(n : ℝ)) n by constructor <;> simp) hv'
  rw [he₁,he₂,max_self] at hh
  have hp := Real.Gamma_pos_of_pos (hpos hv').1
  have hm := Real.Gamma_pos_of_pos (hpos hv').2
  rw [← Real.log_le_log_iff (mul_pos hp hm) (by positivity), Real.log_mul hp.ne' hm.ne']
  exact hh

/-- The manuscript's factorial-ratio lower bound follows from log-convexity. -/
theorem normalizedCosineIntegral_factorial_lower (s : ℕ) {v : ℝ} (hv : |v| ≤ s) :
    (s.factorial : ℝ)^2/((2*s).factorial : ℝ) ≤ normalizedCosineIntegral s v := by
  rw [normalizedCosineIntegral_eq_gamma s (by linarith)]
  have hp : 0 < (s+1 : ℝ)+v := by have := (abs_le.mp hv).1; linarith
  have hm : 0 < (s+1 : ℝ)-v := by have := (abs_le.mp hv).2; linarith
  exact div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (Real.Gamma_pos_of_pos hp)
    (Real.Gamma_pos_of_pos hm)) (gamma_pair_le_factorial s hv)

theorem normalizedCosineIntegral_lower_of_gamma (s : ℕ) {v : ℝ} (hv : |v| ≤ s) :
    1/(4 : ℝ)^s ≤ normalizedCosineIntegral s v :=
  (reciprocal_central_factorial_lower s).trans (normalizedCosineIntegral_factorial_lower s hv)
end LeanNumDetect
