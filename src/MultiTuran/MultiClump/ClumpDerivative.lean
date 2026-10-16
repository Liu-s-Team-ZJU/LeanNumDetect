import MultiTuran.Bernstein.Bernstein
import MultiTuran.Bernstein.BernsteinVariation
import MultiTuran.Nikolskii.ProductNikolskii

/-! # Frequency-dependent derivatives used within one source clump

This proved cubic estimate is sufficient for the manuscript's more generous
Riemann threshold. Its frequency term is retained; no aperture localization
is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Set MeasureTheory
open LeanNumDetect.ExponentialSumEstimates
open LeanNumDetect.MultiTuran.ExponentialInterval

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

theorem exponentialSum_unit_derivative_frequency_bound {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) {W : ℝ} (hW : 0 ≤ W)
    (hfrequency : ∀ j, |frequency j| ≤ W) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖deriv (ExponentialSumEstimates.exponentialSum frequency c) t‖ ≤
      (2*(n : ℝ)^2*W + 12*(n : ℝ)^3) *
        unitSupNorm (ExponentialSumEstimates.exponentialSum frequency c) := by
  let N : ℝ := n
  let K : ℝ := Real.pi*N/2
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast hn
  have hN0 : 0 ≤ N := by positivity
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hK : K ≤ 2*N := by
    have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hN0
    dsimp [K]
    nlinarith only [hp]
  have hKpow : K^4 ≤ (2*N)^4 := pow_le_pow_left₀ hK0 hK 4
  have hNpow : N ≤ N^2 := le_self_pow₀ hN1 (by norm_num)
  have hR : N*W^2+2*K^4 ≤ (N*W+6*N^2)^2 := by
    have h₁ := mul_le_mul_of_nonneg_right hNpow (sq_nonneg W)
    have h₂ := mul_nonneg (mul_nonneg hN0 hW) (sq_nonneg N)
    nlinarith only [hKpow,h₁,h₂,sq_nonneg (N^2)]
  have hroot : Real.sqrt (N*W^2+2*K^4) ≤ N*W+6*N^2 :=
    (Real.sqrt_le_iff).mpr ⟨by positivity,hR⟩
  have hcoef : K*Real.sqrt (N*W^2+2*K^4) ≤ 2*N^2*W+12*N^3 := by
    calc
      _ ≤ (2*N)*(N*W+6*N^2) :=
        mul_le_mul hK hroot (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have henergy : Real.sqrt (unitEnergy (ExponentialSumEstimates.exponentialSum frequency c)) ≤
      unitSupNorm (ExponentialSumEstimates.exponentialSum frequency c) :=
    (Real.sqrt_le_iff).mpr ⟨unitSupNorm_nonneg (ExponentialSumEstimates.continuous_exponentialSum frequency c),
      unitEnergy_le_unitSupNorm_sq frequency c⟩
  have hd := exponentialSum_derivative_energy_norm_le hn frequency c hW hfrequency ht
  change ‖deriv (ExponentialSumEstimates.exponentialSum frequency c) t‖ ≤
    K*Real.sqrt (N*W^2+2*K^4)*
      Real.sqrt (unitEnergy (ExponentialSumEstimates.exponentialSum frequency c)) at hd
  calc
    _ ≤ K*Real.sqrt (N*W^2+2*K^4)*
        Real.sqrt (unitEnergy (ExponentialSumEstimates.exponentialSum frequency c)) := hd
    _ ≤ (2*N^2*W+12*N^3)*
        Real.sqrt (unitEnergy (ExponentialSumEstimates.exponentialSum frequency c)) :=
      mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy (by positivity)

/-- An arbitrary interval and an arbitrary frequency radius. In particular,
the length times the clump diameter need not be small. -/
theorem exponentialSum_interval_derivative_frequency_bound {n : ℕ} (hn : 0 < n)
    (frequency : Fin n → ℝ) (c : Fin n → ℂ) {a b t W : ℝ} (hab : a < b)
    (hW : 0 ≤ W) (hfrequency : ∀ j, |frequency j| ≤ W) (ht : t ∈ Icc a b) :
    ‖deriv (ExponentialSumEstimates.exponentialSum frequency c) t‖ ≤
      (2*(n : ℝ)^2*W + 12*(n : ℝ)^3/(b-a)) *
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
  have hnew : ∀ j, |newFrequency j| ≤ L*W := by
    intro j
    dsimp [newFrequency]
    rw [abs_mul, abs_of_pos hL]
    exact mul_le_mul_of_nonneg_left (hfrequency j) hL.le
  have hFeq : F = fun x => f (L*x+a) := by
    funext x
    exact exponentialSum_affine frequency c a L x
  have hsup : unitSupNorm F ≤ setSupNorm f (Icc a b) := by
    apply unitSupNorm_le (ExponentialSumEstimates.continuous_exponentialSum newFrequency newCoeff)
    intro x hx
    change ‖F x‖ ≤ setSupNorm f (Icc a b)
    rw [hFeq]
    apply le_csSup (isCompact_Icc.bddAbove_image
      (ExponentialSumEstimates.continuous_exponentialSum frequency c).norm.continuousOn)
    refine ⟨L*x+a,?_,rfl⟩
    have hx0 := mul_nonneg hL.le hx.1
    have hx1 := mul_le_mul_of_nonneg_left hx.2 hL.le
    dsimp [L] at *
    constructor <;> nlinarith only [hx0,hx1]
  have hd := exponentialSum_unit_derivative_frequency_bound hn newFrequency newCoeff
    (mul_nonneg hL.le hW) hnew hu
  have hf : HasDerivAt f (deriv f t) (L*u+a) := by
    rw [harg]
    exact (differentiable_exponentialSum frequency c t).hasDerivAt
  have hline : HasDerivAt (fun x : ℝ => L*x+a) L u := by
    convert (((hasDerivAt_id u).const_mul L).add_const a) using 1 <;>
      first | rfl | simp
  have hcomp : HasDerivAt (fun x => f (L*x+a)) (L • deriv f t) u := by
    convert hf.scomp u hline using 1 <;> rfl
  rw [← hFeq] at hcomp
  change ‖deriv F u‖ ≤ (2*(n : ℝ)^2*(L*W)+12*(n : ℝ)^3)*unitSupNorm F at hd
  rw [hcomp.deriv,norm_smul,Real.norm_eq_abs,abs_of_pos hL] at hd
  have hscaled : L*‖deriv f t‖ ≤
      (2*(n : ℝ)^2*(L*W)+12*(n : ℝ)^3)*setSupNorm f (Icc a b) :=
    hd.trans (mul_le_mul_of_nonneg_left hsup (by positivity))
  have he : L * ((2*(n : ℝ)^2*W+12*(n : ℝ)^3/L)*setSupNorm f (Icc a b)) =
      (2*(n : ℝ)^2*(L*W)+12*(n : ℝ)^3)*setSupNorm f (Icc a b) := by
    field_simp
  change ‖deriv f t‖ ≤ (2*(n : ℝ)^2*W+12*(n : ℝ)^3/L)*setSupNorm f (Icc a b)
  apply (mul_le_mul_iff_right₀ hL).mp
  nlinarith only [hscaled,he]

end
end LeanNumDetect.MultiTuran.MultiClump
