import MultiTuran.Bernstein.BernsteinSpace
import MultiTuran.Bernstein.BernsteinEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The genuine interval `L²` Hilbert structure on the finite-dimensional
restricted exponential space. The scalar product is its actual integral. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexConjugate InnerProductSpace
open Set MeasureTheory
open LeanNumDetect.ExponentialSumEstimates

namespace LeanNumDetect.MultiTuran.ExponentialInterval
noncomputable section

/-- The coefficient map with the abstract interval-space codomain kept explicit. -/
def ofCoefficients {n : ℕ} (frequency : Fin n → ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] Space frequency := (coefficientMap frequency).rangeRestrict

variable {n : ℕ} (frequency : Fin n → ℝ) [Fact (0 < n)]

/-- Positivity follows from the proved, frequency-independent Nikolskii bound. -/
instance energyCore : InnerProductSpace.Core ℂ (Space frequency) where
  inner f g := coefficientInner frequency (coefficients frequency f) (coefficients frequency g)
  conj_inner_symm f g := coefficientInner_conj_symm frequency _ _
  re_inner_nonneg f := by
    rw [coefficientInner_self]
    exact unitEnergy_nonneg _
  add_left f g h := by
    rw [map_add, coefficientInner_add_left]
  smul_left f g z := by
    rw [map_smul, coefficientInner_smul_left]
  definite f hzero := by
    have henergy : unitEnergy (representative frequency f) = 0 := by
      simpa only [coefficientInner_self, Complex.ofReal_re, Complex.zero_re, representative] using
        congrArg Complex.re hzero
    have hsup := exponentialSum_unitSupNorm_sq_le (Fact.out : 0 < n) frequency
      (coefficients frequency f)
    change unitSupNorm (representative frequency f)^2 ≤
      (Real.pi*(n : ℝ)/2)^2 * unitEnergy (representative frequency f) at hsup
    rw [henergy,mul_zero] at hsup
    have hsup0 : unitSupNorm (representative frequency f) = 0 := by
      nlinarith [unitSupNorm_nonneg (continuous_exponentialSum frequency (coefficients frequency f))]
    apply toContinuousMap_injective frequency
    ext t
    change f t = 0
    rw [← representative_eq_value frequency f t.property]
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have hbound := norm_le_unitSupNorm
      (continuous_exponentialSum frequency (coefficients frequency f)) t.property
    change ‖representative frequency f t.val‖ ≤ unitSupNorm (representative frequency f) at hbound
    rwa [hsup0] at hbound

instance energyNormedAddCommGroup : NormedAddCommGroup (Space frequency) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance energyInnerProductSpace : InnerProductSpace ℂ (Space frequency) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (Space frequency))

/-- The installed Hilbert norm is exactly the genuine interval energy. -/
theorem norm_sq_eq_unitEnergy (f : Space frequency) :
    ‖f‖^2 = unitEnergy (representative frequency f) := by
  have h := norm_sq_eq_re_inner (𝕜 := ℂ) f
  change ‖f‖^2 = (coefficientInner frequency (coefficients frequency f)
    (coefficients frequency f)).re at h
  simpa only [coefficientInner_self, Complex.ofReal_re, representative] using h

/-- The exact point-evaluation bound in the actual Hilbert norm. -/
theorem evaluation_norm_sq_le (f : Space frequency) (t : UnitInterval) :
    ‖f t‖^2 ≤ (Real.pi*(n : ℝ)/2)^2 * ‖f‖^2 := by
  have hp := norm_le_unitSupNorm
    (continuous_exponentialSum frequency (coefficients frequency f)) t.property
  have hs := exponentialSum_unitSupNorm_sq_le (Fact.out : 0 < n) frequency
    (coefficients frequency f)
  have hp2 := (sq_le_sq₀ (norm_nonneg _)
    (unitSupNorm_nonneg (continuous_exponentialSum frequency (coefficients frequency f)))).mpr hp
  have h := hp2.trans hs
  change ‖representative frequency f t.val‖^2 ≤
    (Real.pi*(n : ℝ)/2)^2 * unitEnergy (representative frequency f) at h
  rw [← norm_sq_eq_unitEnergy frequency f, representative_eq_value frequency f t.property] at h
  exact h

theorem evaluation_norm_le (f : Space frequency) (t : UnitInterval) :
    ‖f t‖ ≤ (Real.pi*(n : ℝ)/2) * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  exact evaluation_norm_sq_le frequency f t

/-- A coefficient presentation has exactly its actual interval energy,
regardless of the chosen linear section. -/
theorem norm_sq_of_coefficients (c : Fin n → ℂ) :
    ‖ofCoefficients frequency c‖^2 =
      unitEnergy (ExponentialSumEstimates.exponentialSum frequency c) := by
  rw [norm_sq_eq_unitEnergy]
  unfold unitEnergy
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  change ‖representative frequency ((coefficientMap frequency).rangeRestrict c) t‖^2 = _
  rw [representative_coefficientMap frequency c (by simpa using ht)]

theorem norm_of_coefficients (c : Fin n → ℂ) :
    ‖ofCoefficients frequency c‖ =
      Real.sqrt (unitEnergy (ExponentialSumEstimates.exponentialSum frequency c)) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [norm_sq_of_coefficients, Real.sq_sqrt (unitEnergy_nonneg _)]

/-- The value of the derivative endomorphism is the true derivative of the
original coefficient presentation, without changing its coefficients. -/
theorem derivative_value_of_coefficients (c : Fin n → ℂ) (t : UnitInterval) :
    derivative frequency (ofCoefficients frequency c) t =
      deriv (ExponentialSumEstimates.exponentialSum frequency c) t.val := by
  change derivative frequency ((coefficientMap frequency).rangeRestrict c) t = _
  rw [derivative_of_coefficients]
  change ExponentialSumEstimates.exponentialSum frequency (coefficientDerivative frequency c) t.val = _
  exact (hasDerivAt_exponentialSum frequency c t.val).deriv.symm

/-- The derivative endomorphism is the actual scalar derivative on the interval. -/
theorem representative_derivative_eq_deriv (f : Space frequency) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    representative frequency (derivative frequency f) t = deriv (representative frequency f) t := by
  have h₁ := hasDerivWithinAt_representative frequency f ht
  have h₂ := (differentiable_exponentialSum frequency (coefficients frequency f) t).hasDerivAt.hasDerivWithinAt
    (s := Icc (0 : ℝ) 1)
  have hu := uniqueDiffOn_Icc_zero_one t ht
  exact (h₁.derivWithin hu).symm.trans (h₂.derivWithin hu)

/-- Integration by parts identifies the entire Hermitian part with the two
endpoint evaluation forms. -/
theorem derivative_boundary_form (f g : Space frequency) :
    ⟪derivative frequency f,g⟫_ℂ + ⟪f,derivative frequency g⟫_ℂ =
      conj (f ⟨1,by simp⟩)*g ⟨1,by simp⟩ - conj (f ⟨0,by simp⟩)*g ⟨0,by simp⟩ := by
  change coefficientInner frequency (coefficients frequency (derivative frequency f))
      (coefficients frequency g) +
    coefficientInner frequency (coefficients frequency f)
      (coefficients frequency (derivative frequency g)) = _
  unfold coefficientInner
  change (∫ t in (0 : ℝ)..1,
      conj (representative frequency (derivative frequency f) t)*representative frequency g t) +
    (∫ t in (0 : ℝ)..1,
      conj (representative frequency f t)*representative frequency (derivative frequency g) t) = _
  have h₁ : (∫ t in (0 : ℝ)..1,
      conj (representative frequency (derivative frequency f) t)*representative frequency g t) =
    ∫ t in (0 : ℝ)..1,
      conj (deriv (representative frequency f) t)*representative frequency g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [representative_derivative_eq_deriv frequency f (by simpa using ht)]
  have h₂ : (∫ t in (0 : ℝ)..1,
      conj (representative frequency f t)*representative frequency (derivative frequency g) t) =
    ∫ t in (0 : ℝ)..1,
      conj (representative frequency f t)*deriv (representative frequency g) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [representative_derivative_eq_deriv frequency g (by simpa using ht)]
  have hb := exponentialSum_boundary_form frequency (coefficients frequency f) (coefficients frequency g)
  change (∫ t in (0 : ℝ)..1,
      conj (deriv (representative frequency f) t)*representative frequency g t) +
    (∫ t in (0 : ℝ)..1,
      conj (representative frequency f t)*deriv (representative frequency g) t) =
      conj (representative frequency f 1)*representative frequency g 1 -
      conj (representative frequency f 0)*representative frequency g 0 at hb
  rw [h₁,h₂,hb]
  rw [representative_eq_value frequency f (by simp : (1:ℝ) ∈ Icc 0 1),
    representative_eq_value frequency g (by simp : (1:ℝ) ∈ Icc 0 1),
    representative_eq_value frequency f (by simp : (0:ℝ) ∈ Icc 0 1),
    representative_eq_value frequency g (by simp : (0:ℝ) ∈ Icc 0 1)]

end
end LeanNumDetect.MultiTuran.ExponentialInterval
