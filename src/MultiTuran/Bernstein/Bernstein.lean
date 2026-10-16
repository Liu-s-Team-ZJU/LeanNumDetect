import MultiTuran.Bernstein.BernsteinInner
import MultiTuran.Bernstein.BernsteinOperator
import MultiTuran.Nikolskii.NikolskiiIntervals
import Mathlib.Analysis.Real.Pi.Bounds

/-! Genuine derivative bounds for actual exponential sums. The interval
constant is intentionally generous; its cubic dependence on the number of
terms is sufficient for the manuscript's discretization threshold. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ComplexConjugate
open Set MeasureTheory
open LeanNumDetect.ExponentialSumEstimates

namespace LeanNumDetect.MultiTuran
noncomputable section

open ExponentialInterval

/-- The actual derivative is bounded by the actual interval `L²` energy.
The frequencies may coincide; no separation or coefficient condition occurs. -/
theorem exponentialSum_derivative_energy_norm_le {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) {W : ℝ} (hW : 0 ≤ W)
    (hfrequency : ∀ j, |frequency j| ≤ W) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖deriv (ExponentialSumEstimates.exponentialSum frequency c) t‖ ≤
      (Real.pi*(n : ℝ)/2) *
        Real.sqrt ((n : ℝ)*W^2 + 2*(Real.pi*(n : ℝ)/2)^4) *
        Real.sqrt (unitEnergy (ExponentialSumEstimates.exponentialSum frequency c)) := by
  letI : Fact (0 < n) := ⟨hn⟩
  let f : Space frequency := ofCoefficients frequency c
  have hop := finiteHilbert_derivative_norm_le
    (derivative frequency)
    (evaluation frequency ⟨0,by simp⟩) (evaluation frequency ⟨1,by simp⟩)
    frequency (generator frequency) (K := Real.pi*(n : ℝ)/2) (W := W)
    (by positivity) hW
    (fun f g => by
      change inner ℂ (derivative frequency f) g + inner ℂ f (derivative frequency g) =
        star (f ⟨1,by simp⟩)*g ⟨1,by simp⟩ - star (f ⟨0,by simp⟩)*g ⟨0,by simp⟩
      simpa only [Complex.star_def] using derivative_boundary_form frequency f g)
    (fun f => evaluation_norm_le frequency f ⟨0,by simp⟩)
    (fun f => evaluation_norm_le frequency f ⟨1,by simp⟩)
    (span_generator_eq_top frequency) (derivative_generator frequency) hfrequency f
  have h := (evaluation_norm_le frequency (derivative frequency f) ⟨t,ht⟩).trans
    (mul_le_mul_of_nonneg_left hop (by positivity : 0 ≤ Real.pi*(n : ℝ)/2))
  dsimp only [f] at h
  rw [derivative_value_of_coefficients, norm_of_coefficients] at h
  simpa only [mul_assoc] using h

/-- A cubic Bernstein bound with a universal numerical constant, for angular
frequencies bounded by `2π`. It concerns the genuine scalar derivative. -/
theorem exponentialSum_unit_derivative_norm_le {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    (hfrequency : ∀ j, |frequency j| ≤ 2*Real.pi)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖deriv (ExponentialSumEstimates.exponentialSum frequency c) t‖ ≤
      20*(n : ℝ)^3*unitSupNorm (ExponentialSumEstimates.exponentialSum frequency c) := by
  let N : ℝ := n
  let K : ℝ := Real.pi*N/2
  have hN0 : 0 ≤ N := Nat.cast_nonneg n
  have hN1 : 1 ≤ N := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast (Nat.succ_le_of_lt hn)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hK : K ≤ 2*N := by
    have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hN0
    dsimp [K]
    nlinarith only [hp]
  have hKpow : K^4 ≤ (2*N)^4 := pow_le_pow_left₀ hK0 hK 4
  have hpi : (2*Real.pi)^2 ≤ (64 : ℝ) := by
    have hp := (sq_le_sq₀ Real.pi_pos.le (by norm_num : (0:ℝ) ≤ 4)).mpr Real.pi_lt_four.le
    nlinarith only [hp]
  have hNpow : N ≤ N^4 := le_self_pow₀ hN1 (by norm_num)
  have hR : N*(2*Real.pi)^2+2*K^4 ≤ (10*N^2)^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hpi hN0
    have h₂ := mul_le_mul_of_nonneg_left hNpow (by norm_num : (0:ℝ) ≤ 64)
    have h₃ := pow_nonneg hN0 4
    nlinarith only [hKpow,h₁,h₂,h₃]
  have hroot : Real.sqrt (N*(2*Real.pi)^2+2*K^4) ≤ 10*N^2 :=
    (Real.sqrt_le_iff).mpr ⟨by positivity,hR⟩
  have hcoef : K*Real.sqrt (N*(2*Real.pi)^2+2*K^4) ≤ 20*N^3 := by
    calc
      _ ≤ (2*N)*(10*N^2) := mul_le_mul hK hroot (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have henergy : Real.sqrt (unitEnergy (ExponentialSumEstimates.exponentialSum frequency c)) ≤
      unitSupNorm (ExponentialSumEstimates.exponentialSum frequency c) :=
    (Real.sqrt_le_iff).mpr ⟨unitSupNorm_nonneg (continuous_exponentialSum frequency c),
      unitEnergy_le_unitSupNorm_sq frequency c⟩
  have hd := exponentialSum_derivative_energy_norm_le hn frequency c
    (by positivity : 0 ≤ 2*Real.pi) hfrequency ht
  change ‖deriv (ExponentialSumEstimates.exponentialSum frequency c) t‖ ≤
    K*Real.sqrt (N*(2*Real.pi)^2+2*K^4)*
      Real.sqrt (unitEnergy (ExponentialSumEstimates.exponentialSum frequency c)) at hd
  calc
    _ ≤ K*Real.sqrt (N*(2*Real.pi)^2+2*K^4)*
        Real.sqrt (unitEnergy (ExponentialSumEstimates.exponentialSum frequency c)) := hd
    _ ≤ (20*N^3)*Real.sqrt (unitEnergy (ExponentialSumEstimates.exponentialSum frequency c)) :=
      mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy (by positivity)

/-- The interval form needed by the product norming argument. The derivative,
supremum, interval length and angular-frequency bound are all literal. -/
theorem exponentialSum_interval_derivative_norm_le {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) {a b t : ℝ} (hab : a < b)
    (hfrequency : ∀ j, |frequency j| * (b-a) ≤ 2*Real.pi) (ht : t ∈ Icc a b) :
    ‖deriv (ExponentialSumEstimates.exponentialSum frequency c) t‖ ≤
      20*(n : ℝ)^3/(b-a)*
        setSupNorm (ExponentialSumEstimates.exponentialSum frequency c) (Icc a b) := by
  let L := b-a
  have hL : 0 < L := sub_pos.mpr hab
  let f := ExponentialSumEstimates.exponentialSum frequency c
  let newFrequency : Fin n → ℝ := fun j => L*frequency j
  let newCoeff : Fin n → ℂ := fun j => c j * Complex.exp (Complex.I*((a*frequency j : ℝ) : ℂ))
  let F := ExponentialSumEstimates.exponentialSum newFrequency newCoeff
  let u := (t-a)/L
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hL.le
    · apply (div_le_one hL).mpr
      dsimp [L]
      linarith [ht.2]
  have harg : L*u+a = t := by dsimp [u]; field_simp; ring
  have hnew : ∀ j, |newFrequency j| ≤ 2*Real.pi := by
    intro j
    dsimp [newFrequency]
    rw [abs_mul,abs_of_pos hL,mul_comm]
    exact hfrequency j
  have hFeq : F = fun x => f (L*x+a) := by
    funext x
    exact exponentialSum_affine frequency c a L x
  have hsup : unitSupNorm F ≤ setSupNorm f (Icc a b) := by
    apply unitSupNorm_le (continuous_exponentialSum newFrequency newCoeff)
    intro x hx
    change ‖F x‖ ≤ setSupNorm f (Icc a b)
    rw [hFeq]
    apply le_csSup (isCompact_Icc.bddAbove_image
      (continuous_exponentialSum frequency c).norm.continuousOn)
    refine ⟨L*x+a,?_,rfl⟩
    have hx0 := mul_nonneg hL.le hx.1
    have hx1 := mul_le_mul_of_nonneg_left hx.2 hL.le
    dsimp [L] at *
    constructor <;> nlinarith only [hx0,hx1]
  have hd := exponentialSum_unit_derivative_norm_le hn newFrequency newCoeff hnew hu
  have hf : HasDerivAt f (deriv f t) (L*u+a) := by
    rw [harg]
    exact (differentiable_exponentialSum frequency c t).hasDerivAt
  have hline : HasDerivAt (fun x : ℝ => L*x+a) L u := by
    convert (((hasDerivAt_id u).const_mul L).add_const a) using 1 <;>
      first | rfl | simp
  have hcomp : HasDerivAt (fun x => f (L*x+a)) (L • deriv f t) u := by
    convert hf.scomp u hline using 1 <;> rfl
  rw [← hFeq] at hcomp
  change ‖deriv F u‖ ≤ 20*(n : ℝ)^3*unitSupNorm F at hd
  rw [hcomp.deriv,norm_smul,Real.norm_eq_abs,abs_of_pos hL] at hd
  have hscaled : L*‖deriv f t‖ ≤ 20*(n : ℝ)^3*setSupNorm f (Icc a b) :=
    hd.trans (mul_le_mul_of_nonneg_left hsup (by positivity))
  change ‖deriv f t‖ ≤ 20*(n : ℝ)^3/L*setSupNorm f (Icc a b)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hL).mpr
  nlinarith only [hscaled]

end
end LeanNumDetect.MultiTuran
