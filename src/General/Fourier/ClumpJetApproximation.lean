import General.Fourier.ClusteredVandermonde
import General.Fourier.ExponentialCompanion
import General.Fourier.PolynomialCrossCorrelation
import General.Fourier.SmallFrequencyEvaluationBounds

/-! Gap-free polynomial approximation of a finite exponential column span. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProductSpace Matrix.Norms.Operator
open WithLp Matrix Set

namespace LeanNumDetect.ClumpJetApproximation
noncomputable section

/-- An unnormalized finite Fourier signal. -/
def angularSignal {s : ℕ} (N : ℕ) (node : Fin s → ℝ) (coefficient : Fin s → ℂ) :
    EuclideanSpace ℂ (Fin (N + 1)) :=
  toLp 2 (fun k => ∑ j, coefficient j * ClusteredVandermonde.vandermonde N node k j)

/-- Every vector in the actual column span has a coefficient representation. -/
theorem clusterSubspace_coefficient_representation {s N : ℕ} (node : Fin s → ℝ)
    (u : EuclideanSpace ℂ (Fin (N + 1)))
    (hu : u ∈ ClusteredVandermonde.clusterSubspace N node) :
    ∃ coefficient : Fin s → ℂ, u = angularSignal N node coefficient := by
  classical
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨j, rfl⟩ := hu
    refine ⟨Pi.single j 1, ?_⟩
    ext k
    simp [angularSignal, Pi.single_apply]
  | zero =>
    refine ⟨0, ?_⟩
    ext k
    simp [angularSignal]
  | add u v hu hv ihu ihv =>
    obtain ⟨c, rfl⟩ := ihu
    obtain ⟨d, rfl⟩ := ihv
    refine ⟨c + d, ?_⟩
    ext k
    simp [angularSignal, add_mul, Finset.sum_add_distrib]
  | smul z u hu ihu =>
    obtain ⟨c, rfl⟩ := ihu
    refine ⟨z • c, ?_⟩
    ext k
    simp [angularSignal, Finset.mul_sum, mul_assoc]

/-- A coordinate bound converts to a Euclidean bound with the exact row count. -/
theorem norm_le_sqrt_card_mul {N : ℕ} (u : EuclideanSpace ℂ (Fin (N + 1)))
    (b : ℝ) (hb : 0 ≤ b) (hu : ∀ k, ‖u k‖ ≤ b) :
    ‖u‖ ≤ Real.sqrt (N + 1 : ℝ) * b := by
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt (∑ k, ‖u k‖ ^ 2) ≤ Real.sqrt (∑ _k : Fin (N + 1), b ^ 2) :=
      Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hu k) 2)
    _ = Real.sqrt (N + 1 : ℝ) * b := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb]

/-- Taylor coefficients of the initial jet. -/
def jetCoefficient {s : ℕ} (jet : Fin s → ℂ) : Fin s → ℂ :=
  fun j => jet j / (j.val.factorial : ℂ)

theorem jetCoefficient_sum_norm_le {s : ℕ} (jet : Fin s → ℂ) :
    (∑ j, ‖jetCoefficient jet j‖) ≤ (s : ℝ) * ‖jet‖ := by
  calc
    _ ≤ ∑ _j : Fin s, ‖jet‖ := by
      apply Finset.sum_le_sum
      intro j _
      have hfac : (1 : ℝ) ≤ (j.val.factorial : ℝ) := by
        exact_mod_cast (show 1 ≤ j.val.factorial from Nat.factorial_pos _)
      rw [jetCoefficient, norm_div, Complex.norm_natCast]
      exact (div_le_self (norm_nonneg _) hfac).trans (norm_le_pi_norm jet j)
    _ = _ := by simp

/-- A modulated evolution vector on the normalized integer grid. -/
def evolutionVector {s : ℕ} (hs : 0 < s) (N : ℕ)
    (frequency jet : Fin s → ℂ) (center : ℝ) :
    EuclideanSpace ℂ (Fin (N + 1)) :=
  toLp 2 (fun k => Complex.exp (Complex.I * (((k.val : ℝ) * center : ℝ) : ℂ)) *
    (NormedSpace.exp ((((k.val : ℝ) / N : ℝ) : ℂ) •
      ExponentialCompanion.generator frequency)).mulVec jet ⟨0, hs⟩)

/-- Entrywise companion convergence gives a vector approximation independent
of the distances between the individual frequencies. -/
theorem evolutionVector_polynomial_approximation {s N : ℕ} (hs : 0 < s) (hN : 0 < N)
    (frequency jet : Fin s → ℂ) (center ε : ℝ) (hε : 0 ≤ ε)
    (hentry : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j : Fin s,
      ‖NormedSpace.exp ((t : ℂ) • ExponentialCompanion.generator frequency) ⟨0, hs⟩ j -
        (t : ℂ) ^ j.val / (j.val.factorial : ℂ)‖ ≤ ε) :
    ‖evolutionVector hs N frequency jet center -
      PolynomialCrossCorrelation.modulatedPolynomial N center (jetCoefficient jet)‖ ≤
      Real.sqrt (N + 1 : ℝ) * ((s : ℝ) * ε * ‖jet‖) := by
  apply norm_le_sqrt_card_mul _ _ (by positivity)
  intro k
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have ht : (k.val : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one hNR).2
      exact_mod_cast (show k.val ≤ N by omega)
  have hphase : ‖Complex.exp (Complex.I * (((k.val : ℝ) * center : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have he : (evolutionVector hs N frequency jet center -
      PolynomialCrossCorrelation.modulatedPolynomial N center (jetCoefficient jet)) k =
      Complex.exp (Complex.I * (((k.val : ℝ) * center : ℝ) : ℂ)) *
        ∑ j : Fin s, (NormedSpace.exp
          ((((k.val : ℝ) / N : ℝ) : ℂ) • ExponentialCompanion.generator frequency)
          ⟨0, hs⟩ j - (((k.val : ℝ) / N : ℝ) : ℂ) ^ j.val /
            (j.val.factorial : ℂ)) * jet j := by
    simp only [evolutionVector, PolynomialCrossCorrelation.modulatedPolynomial,
      PolynomialCrossCorrelation.polynomialValue, jetCoefficient, ofLp_sub,
      Pi.sub_apply, ofLp_toLp, Matrix.mulVec, dotProduct, ← mul_sub, ← Finset.sum_sub_distrib,
      Complex.ofReal_pow]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, norm_mul, hphase, one_mul]
  calc
    _ ≤ ∑ j : Fin s, ‖(NormedSpace.exp
        ((((k.val : ℝ) / N : ℝ) : ℂ) • ExponentialCompanion.generator frequency)
        ⟨0, hs⟩ j - (((k.val : ℝ) / N : ℝ) : ℂ) ^ j.val /
          (j.val.factorial : ℂ)) * jet j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin s, ε * ‖jet‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (hentry _ ht j) (norm_le_pi_norm jet j)
        (norm_nonneg _) hε
    _ = _ := by simp; ring

/-- Modulating the sequence by a real center preserves its Euclidean norm. -/
theorem evolutionVector_norm_eq {s N : ℕ} (hs : 0 < s)
    (frequency jet : Fin s → ℂ) (center : ℝ) :
    ‖evolutionVector hs N frequency jet center‖ =
      ‖evolutionVector hs N frequency jet 0‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hphase : ‖Complex.exp (Complex.I * (((k.val : ℝ) * center : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  simp only [evolutionVector, ofLp_toLp, norm_mul, hphase, one_mul,
    mul_zero, Complex.ofReal_zero, Complex.exp_zero, norm_one]

/-- Convert the normalized grid coefficient lower bound to a norm bound. -/
theorem jet_norm_le_of_grid_lower {s N : ℕ} (hs : 0 < s)
    (frequency jet : Fin s → ℂ) (c : ℝ) (hc : 0 < c)
    (hlower : c * ‖jet‖ ^ 2 ≤
      ‖evolutionVector hs N frequency jet 0‖ ^ 2 / (N + 1 : ℝ)) :
    ‖jet‖ ≤ (1 / Real.sqrt c) / Real.sqrt (N + 1 : ℝ) *
      ‖evolutionVector hs N frequency jet 0‖ := by
  have hN : 0 < (N + 1 : ℝ) := by positivity
  have hcS : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hNS : 0 < Real.sqrt (N + 1 : ℝ) := Real.sqrt_pos.2 hN
  have hsq : (Real.sqrt c * Real.sqrt (N + 1 : ℝ) * ‖jet‖) ^ 2 ≤
      ‖evolutionVector hs N frequency jet 0‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hc.le, Real.sq_sqrt hN.le]
    have h := (le_div_iff₀ hN).1 hlower
    nlinarith
  have hh := (sq_le_sq₀ (by positivity :
      0 ≤ Real.sqrt c * Real.sqrt (N + 1 : ℝ) * ‖jet‖) (norm_nonneg _)).1 hsq
  have hdiv : ‖jet‖ ≤ ‖evolutionVector hs N frequency jet 0‖ /
      (Real.sqrt c * Real.sqrt (N + 1 : ℝ)) :=
    (le_div_iff₀ (mul_pos hcS hNS)).2 (by simpa only [mul_comm] using hh)
  exact hdiv.trans_eq (by field_simp)

/-- Gap-free coefficient control for the sampled companion evolution. -/
theorem exists_evolutionVector_jet_bounds {s : ℕ} (hs : 0 < s) :
    ∃ η B D : ℝ, 0 < η ∧ 0 < B ∧ 0 < D ∧
      ∀ (N : ℕ), B ≤ (N : ℝ) → 0 < N →
        ∀ frequency jet : Fin s → ℂ, ‖frequency‖ ≤ η →
          ‖jet‖ ≤ D / Real.sqrt (N + 1 : ℝ) *
            ‖evolutionVector hs N frequency jet 0‖ := by
  obtain ⟨η, B, c, hη, _, hB, hc, hbounds⟩ :=
    SmallFrequencyEvaluationBounds.smallFrequency_grid_jet_bounds hs
  refine ⟨η, B, 1 / Real.sqrt c, hη, hB, by positivity, ?_⟩
  intro N hsize hN frequency jet hfrequency
  apply jet_norm_le_of_grid_lower hs frequency jet c hc
  have h := (hbounds frequency jet N hfrequency hN hsize).1
  have heq : ‖evolutionVector hs N frequency jet 0‖ ^ 2 =
      ∑ l ∈ Finset.range (N + 1),
        ‖SmallFrequencyEvaluationBounds.evolutionSignal hs frequency jet ((l : ℝ) / N)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [evolutionVector, ofLp_toLp, mul_zero, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, one_mul, SmallFrequencyEvaluationBounds.evolutionSignal]
    exact Fin.sum_univ_eq_sum_range (fun l : ℕ =>
      ‖(NormedSpace.exp ((((l : ℝ) / N : ℝ) : ℂ) •
        ExponentialCompanion.generator frequency)).mulVec jet ⟨0, hs⟩‖ ^ 2) (N + 1)
  simpa only [heq, Nat.cast_add, Nat.cast_one] using h

/-- Center and integer windings may be chosen separately for each node.
The normalized frequencies stay small even when two nodes nearly coincide. -/
theorem angularSignal_eq_evolutionVector {s N : ℕ} (hs : 0 < s) (hN : 0 < N)
    (node : Fin s → ℝ) (coefficient : Fin s → ℂ) (center : ℝ) (p : Fin s → ℤ) :
    angularSignal N node coefficient =
      evolutionVector hs N
        (fun j => Complex.I * (((N : ℝ) * (node j - center + 2 * Real.pi * p j) : ℝ) : ℂ))
        (ExponentialCompanion.initialJet
          (fun j => Complex.I * (((N : ℝ) * (node j - center + 2 * Real.pi * p j) : ℝ) : ℂ))
          coefficient) center := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  ext k
  simp only [angularSignal, evolutionVector, ofLp_toLp]
  rw [← ExponentialCompanion.exponentialSum_eq_evolution hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : (((k.val : ℝ) / N : ℝ) : ℂ) *
      (Complex.I * (((N : ℝ) * (node j - center + 2 * Real.pi * p j) : ℝ) : ℂ)) =
      Complex.I * (((k.val : ℝ) * node j : ℝ) : ℂ) -
        Complex.I * (((k.val : ℝ) * center : ℝ) : ℂ) +
        (((k.val : ℤ) * p j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp [hNC]
    <;> ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_sub]
  have hphase := Complex.exp_ne_zero
    (Complex.I * (((k.val : ℝ) * center : ℝ) : ℂ))
  simp only [ClusteredVandermonde.vandermonde]
  field_simp

end
end LeanNumDetect.ClumpJetApproximation
