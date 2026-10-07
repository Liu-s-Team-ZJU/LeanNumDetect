import General.Fourier.ExponentialCompanion
import General.Fourier.JetPolynomialPerturbation
import General.Fourier.ExponentialSums
import General.Fourier.UniformGridEvaluationBounds

/-!
# Small-frequency exponential spaces

Uniform continuity of the companion evolution at the nilpotent generator
and polynomial point-evaluation bounds give dimension-squared row estimates.
All radii and resolution thresholds depend only on the dimension, and no
frequency gap is required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix.Norms.Operator
open Set MeasureTheory Matrix

namespace LeanNumDetect.SmallFrequencyEvaluationBounds
open ExponentialCompanion PolynomialEvaluationBounds ExponentialSumEstimates
open UniformGridEvaluationBounds
noncomputable section

def evolutionSignal {s : ℕ} (hs : 0 < s) (frequency a : Fin s → ℂ) (t : ℝ) : ℂ :=
  (NormedSpace.exp ((t : ℂ) • generator frequency)).mulVec a ⟨0, hs⟩

def firstRowFunctional {s : ℕ} (hs : 0 < s) (a : Fin s → ℂ) :
    Matrix (Fin s) (Fin s) ℂ →ₗ[ℂ] ℂ where
  toFun A := A.mulVec a ⟨0, hs⟩
  map_add' A B := by simp [Matrix.add_mulVec]
  map_smul' c A := by simp [Matrix.smul_mulVec]

theorem continuous_evolutionSignal {s : ℕ} (hs : 0 < s)
    (frequency a : Fin s → ℂ) : Continuous (evolutionSignal hs frequency a) := by
  have hm : Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • generator frequency)) :=
    NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)
  exact (firstRowFunctional hs a).continuous_of_finiteDimensional.comp hm

theorem hasDerivAt_evolutionSignal {s : ℕ} (hs : 0 < s)
    (frequency a : Fin s → ℂ) (t : ℝ) :
    HasDerivAt (evolutionSignal hs frequency a)
      ((NormedSpace.exp ((t : ℂ) • generator frequency) * generator frequency).mulVec
        a ⟨0, hs⟩) t := by
  let L := (firstRowFunctional hs a).toContinuousLinearMap
  have hm := hasDerivAt_exp_smul_const (generator frequency) (t : ℂ)
  exact (L.hasFDerivAt.comp_hasDerivAt (t : ℂ) hm).comp_ofReal

theorem evolutionSignal_deriv {s : ℕ} (hs : 0 < s)
    (frequency a : Fin s → ℂ) (t : ℝ) :
    deriv (evolutionSignal hs frequency a) t =
      (NormedSpace.exp ((t : ℂ) • generator frequency) * generator frequency).mulVec
        a ⟨0, hs⟩ := (hasDerivAt_evolutionSignal hs frequency a t).deriv

theorem norm_firstRow_mulVec_le {s : ℕ} (hs : 0 < s)
    (A : Matrix (Fin s) (Fin s) ℂ) (a : Fin s → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hentry : ∀ j, ‖A ⟨0, hs⟩ j‖ ≤ L) :
    ‖A.mulVec a ⟨0, hs⟩‖ ≤ (s : ℝ) * L * ‖a‖ := by
  calc
    ‖A.mulVec a ⟨0, hs⟩‖ ≤ ∑ j, ‖A ⟨0, hs⟩ j * a j‖ := by
      change ‖∑ j, A ⟨0, hs⟩ j * a j‖ ≤ ∑ j, ‖A ⟨0, hs⟩ j * a j‖
      exact norm_sum_le Finset.univ (fun j : Fin s => A ⟨0, hs⟩ j * a j)
    _ ≤ ∑ _j : Fin s, L * ‖a‖ := Finset.sum_le_sum (fun j _ => by
      rw [norm_mul]
      exact mul_le_mul (hentry j) (norm_le_pi_norm a j) (norm_nonneg (a j)) hL)
    _ = (s : ℝ) * L * ‖a‖ := by simp [mul_assoc]

theorem exists_evolution_derivative_coefficient_bound {s : ℕ} (hs : 0 < s) :
    ∃ L : ℝ, 0 < L ∧ ∀ (frequency a : Fin s → ℂ), ‖frequency‖ ≤ 1 →
      ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (evolutionSignal hs frequency a) t‖ ≤ L * ‖a‖ := by
  let G : (Fin s → ℂ) × ℝ → Fin s → ℂ := fun p =>
    (NormedSpace.exp ((p.2 : ℂ) • generator p.1) * generator p.1) ⟨0, hs⟩
  have hG : Continuous G := by
    apply (continuous_apply (⟨0, hs⟩ : Fin s)).comp
    exact (NormedSpace.exp_continuous.comp
      ((Complex.continuous_ofReal.comp continuous_snd).smul
        ((continuous_generator s).comp continuous_fst))).mul
      ((continuous_generator s).comp continuous_fst)
  let K := Metric.closedBall (0 : Fin s → ℂ) 1 ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := (isCompact_closedBall (0 : Fin s → ℂ) 1).prod isCompact_Icc
  obtain ⟨H, hH⟩ := hK.bddAbove_image hG.norm.continuousOn
  let L := max H 1
  have hL : 0 < L := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨(s : ℝ) * L, by exact mul_pos (by exact_mod_cast hs) hL, ?_⟩
  intro frequency a hfrequency t ht
  rw [evolutionSignal_deriv]
  apply norm_firstRow_mulVec_le hs _ a hL.le
  intro j
  have hp : (frequency, t) ∈ K := by
    exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hfrequency, ht⟩
  exact (norm_le_pi_norm (G (frequency, t)) j).trans
    ((hH ⟨(frequency, t), hp, rfl⟩).trans (le_max_left _ _))

theorem evolutionSignal_close_to_jetPolynomial {s : ℕ} (hs : 0 < s)
    {ε : ℝ} (hε : 0 ≤ ε) (frequency a : Fin s → ℂ)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j : Fin s,
      ‖NormedSpace.exp ((t : ℂ) • generator frequency) ⟨0, hs⟩ j -
        (t : ℂ)^j.val / (j.val.factorial : ℂ)‖ ≤ ε / s) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖evolutionSignal hs frequency a t - jetPolynomialSignal a t‖ ≤ ε * ‖a‖ := by
  intro t ht
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have heq : evolutionSignal hs frequency a t - jetPolynomialSignal a t =
      ∑ j, (NormedSpace.exp ((t : ℂ) • generator frequency) ⟨0, hs⟩ j -
        (t : ℂ)^j.val / (j.val.factorial : ℂ)) * a j := by
    simp only [evolutionSignal, Matrix.mulVec, dotProduct, jetPolynomialSignal]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  calc
    _ ≤ ∑ j, ‖(NormedSpace.exp ((t : ℂ) • generator frequency) ⟨0, hs⟩ j -
        (t : ℂ)^j.val / (j.val.factorial : ℂ)) * a j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin s, (ε / s) * ‖a‖ := Finset.sum_le_sum (fun j _ => by
      rw [norm_mul]
      exact mul_le_mul (hclose t ht j) (norm_le_pi_norm a j) (norm_nonneg _)
        (by positivity))
    _ = ε * ‖a‖ := by simp; field_simp

theorem smallFrequency_evolution_bounds {s : ℕ} (hs : 0 < s) :
    ∃ η c D : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < c ∧ 0 < D ∧
      ∀ (frequency a : Fin s → ℂ), ‖frequency‖ ≤ η →
        c * ‖a‖^2 ≤ unitEnergy (evolutionSignal hs frequency a) ∧
        unitSupNorm (evolutionSignal hs frequency a)^2 ≤
          128 * (s : ℝ)^2 * unitEnergy (evolutionSignal hs frequency a) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          ‖deriv (evolutionSignal hs frequency a) t‖ ≤
            D * unitSupNorm (evolutionSignal hs frequency a)) := by
  obtain ⟨ε, c, hε, hc, hstable⟩ := jetPolynomial_stability_constants s hs
  obtain ⟨η, hη, hradius⟩ := exists_uniform_jet_radius hs (ε / s)
    (by exact div_pos hε (by exact_mod_cast hs))
  obtain ⟨L, hL, hder⟩ := exists_evolution_derivative_coefficient_bound hs
  refine ⟨min η 1, c, L / Real.sqrt c, lt_min hη zero_lt_one,
    min_le_right _ _, hc, div_pos hL (Real.sqrt_pos.2 hc), ?_⟩
  intro frequency a hfrequency
  let f := evolutionSignal hs frequency a
  have hf : Continuous f := continuous_evolutionSignal hs frequency a
  have hclose := evolutionSignal_close_to_jetPolynomial hs hε.le frequency a
    (hradius frequency (hfrequency.trans (min_le_left _ _)))
  have h := hstable a f hf hclose
  have hE : c * ‖a‖^2 ≤ unitEnergy f := h.1
  have hSqE : 0 ≤ 128 * (s : ℝ)^2 * unitEnergy f := by
    have := unitEnergy_nonneg f
    positivity
  have hsup : unitSupNorm f ≤ Real.sqrt (128 * (s : ℝ)^2 * unitEnergy f) := by
    apply unitSupNorm_le hf
    intro t ht
    have hh := h.2 t ht
    change ‖f t‖^2 ≤ 128 * (s : ℝ)^2 * unitEnergy f at hh
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
      (by rwa [Real.sq_sqrt hSqE])
  refine ⟨hE, ?_, ?_⟩
  · have hsup2 := (sq_le_sq₀ (unitSupNorm_nonneg hf) (Real.sqrt_nonneg _)).2 hsup
    rwa [Real.sq_sqrt hSqE] at hsup2
  · exact derivative_bound_of_coefficient_energy_lower a hf hc hL.le
      (unitSupNorm_nonneg hf) hE (fun t ht => norm_le_unitSupNorm hf ht)
      (hder frequency a (hfrequency.trans (min_le_right _ _)))

theorem smallFrequency_grid_jet_bounds {s : ℕ} (hs : 0 < s) :
    ∃ η B c : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < B ∧ 0 < c ∧
      ∀ (frequency a : Fin s → ℂ) (M : ℕ), ‖frequency‖ ≤ η →
        0 < M → B ≤ (M : ℝ) →
        c * ‖a‖^2 ≤
          (∑ l ∈ Finset.range (M + 1),
            ‖evolutionSignal hs frequency a ((l : ℝ) / M)‖^2) / ((M : ℝ) + 1) ∧
        ∀ k ≤ M, ((M : ℝ) + 1) *
          ‖evolutionSignal hs frequency a ((k : ℝ) / M)‖^2 ≤
          512 * (s : ℝ)^2 *
            ∑ l ∈ Finset.range (M + 1),
              ‖evolutionSignal hs frequency a ((l : ℝ) / M)‖^2 := by
  obtain ⟨η, c, D, hη, hηone, hc, hD, hbounds⟩ := smallFrequency_evolution_bounds hs
  refine ⟨η, 4 * D * (128 * (s : ℝ)^2), c / 4, hη, hηone,
    by positivity, by positivity, ?_⟩
  intro frequency a M hfrequency hM hsize
  have hb := hbounds frequency a hfrequency
  have hf := continuous_evolutionSignal hs frequency a
  have hfdiff : Differentiable ℝ (evolutionSignal hs frequency a) :=
    fun t => (hasDerivAt_evolutionSignal hs frequency a t).differentiableAt
  constructor
  · exact uniformGrid_coefficient_energy_lower a hf hfdiff hc.le hD.le
      (by positivity) hb.1 hb.2.1 hb.2.2 hM hsize
  · intro k hk
    have h := uniformGrid_row_bound hf hfdiff hD.le
      (show 0 ≤ 128 * (s : ℝ)^2 by positivity) hb.2.1 hb.2.2 hM hsize hk
    convert h using 1
    ring

theorem exponentialSum_eq_evolution {s : ℕ} (hs : 0 < s)
    (frequency : Fin s → ℝ) (coefficient : Fin s → ℂ) :
    exponentialSum frequency coefficient =
      evolutionSignal hs (fun j => Complex.I * (frequency j : ℂ))
        (initialJet (fun j => Complex.I * (frequency j : ℂ)) coefficient) := by
  funext t
  rw [evolutionSignal, ← ExponentialCompanion.exponentialSum_eq_evolution hs]
  unfold exponentialSum
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  push_cast
  ring

theorem imaginaryFrequency_norm_le {s : ℕ} (frequency : Fin s → ℝ)
    {η : ℝ} (hη : 0 ≤ η) (hfrequency : ∀ j, |frequency j| ≤ η) :
    ‖fun j => Complex.I * (frequency j : ℂ)‖ ≤ η := by
  apply (pi_norm_le_iff_of_nonneg hη).2
  intro j
  simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    using hfrequency j

theorem smallFrequency_exponentialSum_bounds {s : ℕ} (hs : 0 < s) :
    ∃ η D : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < D ∧
      ∀ (frequency : Fin s → ℝ) (coefficient : Fin s → ℂ),
        (∀ j, |frequency j| ≤ η) →
        unitSupNorm (exponentialSum frequency coefficient)^2 ≤
          128 * (s : ℝ)^2 * unitEnergy (exponentialSum frequency coefficient) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          ‖deriv (exponentialSum frequency coefficient) t‖ ≤
            D * unitSupNorm (exponentialSum frequency coefficient)) := by
  obtain ⟨η, c, D, hη, hηone, hc, hD, hbounds⟩ := smallFrequency_evolution_bounds hs
  refine ⟨η, D, hη, hηone, hD, ?_⟩
  intro frequency coefficient hfrequency
  have hb := hbounds (fun j => Complex.I * (frequency j : ℂ))
    (initialJet (fun j => Complex.I * (frequency j : ℂ)) coefficient)
    (imaginaryFrequency_norm_le frequency hη.le hfrequency)
  rw [← exponentialSum_eq_evolution hs] at hb
  exact hb.2

theorem smallFrequency_exponentialSum_grid_bounds {s : ℕ} (hs : 0 < s) :
    ∃ η B : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < B ∧
      ∀ (frequency : Fin s → ℝ) (coefficient : Fin s → ℂ) (M : ℕ),
        (∀ j, |frequency j| ≤ η) → 0 < M → B ≤ (M : ℝ) →
        ∀ k ≤ M, ((M : ℝ) + 1) *
          ‖exponentialSum frequency coefficient ((k : ℝ) / M)‖^2 ≤
          512 * (s : ℝ)^2 * ∑ l ∈ Finset.range (M + 1),
            ‖exponentialSum frequency coefficient ((l : ℝ) / M)‖^2 := by
  obtain ⟨η, B, c, hη, hηone, hB, hc, hbounds⟩ := smallFrequency_grid_jet_bounds hs
  refine ⟨η, B, hη, hηone, hB, ?_⟩
  intro frequency coefficient M hfrequency hM hsize
  have hb := hbounds (fun j => Complex.I * (frequency j : ℂ))
    (initialJet (fun j => Complex.I * (frequency j : ℂ)) coefficient) M
    (imaginaryFrequency_norm_le frequency hη.le hfrequency) hM hsize
  rw [← exponentialSum_eq_evolution hs] at hb
  exact hb.2

end
end LeanNumDetect.SmallFrequencyEvaluationBounds
