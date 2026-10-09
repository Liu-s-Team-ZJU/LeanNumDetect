import General.Fourier.QuantitativeClumpSectionBounds

/-! Explicit evaluation and polynomial approximation for angular clump sections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators InnerProductSpace
open Set MeasureTheory Matrix WithLp

namespace LeanNumDetect.QuantitativeClumpSectionBounds
open AngularClumpSectionBounds PolynomialEvaluationBounds ClumpJetApproximation
open SmallFrequencyEvaluationBounds
noncomputable section

def modulatedUnitGridVector (M : ℕ) (center : ℝ) (f : ℝ → ℂ) :
    EuclideanSpace ℂ (Fin (M + 1)) :=
  toLp 2 (fun k => Complex.exp (Complex.I * (((k.val : ℝ) * center : ℝ) : ℂ)) *
    f ((k.val : ℝ) / M))

theorem modulatedUnitGridVector_norm (M : ℕ) (center : ℝ) (f : ℝ → ℂ) :
    ‖modulatedUnitGridVector M center f‖ = ‖unitGridVector M f‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hphase : ‖Complex.exp (Complex.I * (((k.val : ℝ) * center : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  simp only [modulatedUnitGridVector, unitGridVector, ofLp_toLp, norm_mul, hphase, one_mul]

theorem modulatedUnitGridVector_sub (M : ℕ) (center : ℝ) (f p : ℝ → ℂ) :
    modulatedUnitGridVector M center f - modulatedUnitGridVector M center p =
      modulatedUnitGridVector M center (fun t => f t - p t) := by
  ext k
  simp [modulatedUnitGridVector, mul_sub]

theorem modulatedUnitGridVector_sub_norm (M : ℕ) (center : ℝ) (f p : ℝ → ℂ) :
    ‖modulatedUnitGridVector M center f - modulatedUnitGridVector M center p‖ =
      ‖unitGridVector M f - unitGridVector M p‖ := by
  rw [modulatedUnitGridVector_sub, modulatedUnitGridVector_norm]
  congr 1

theorem modulatedUnitGridVector_jet {s M : ℕ} (center : ℝ) (a : Fin s → ℂ) :
    modulatedUnitGridVector M center (jetPolynomialSignal a) =
      PolynomialCrossCorrelation.modulatedPolynomial M center (jetCoefficient a) := by
  ext k
  simp only [modulatedUnitGridVector, PolynomialCrossCorrelation.modulatedPolynomial,
    PolynomialCrossCorrelation.polynomialValue, jetCoefficient, jetPolynomialSignal,
    ofLp_toLp, Complex.ofReal_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The local sampling-grid estimates use explicit radius and resolution. -/
theorem smallFrequency_explicit_grid_bounds {d h s M : ℕ}
    (hd : 1 ≤ d) (hs : 0 < s) (hM : 0 < M)
    (frequency a : Fin s → ℂ) (hfrequency : ‖frequency‖ ≤ sectionJetRadius d h s)
    (hsize : sectionGridResolution d h s ≤ (M : ℝ)) :
    (∀ k : Fin (M + 1), (M + 1 : ℝ) *
      ‖evolutionSignal hs frequency a ((k.val : ℝ) / M)‖^2 ≤
      sectionRowConstant d * (s : ℝ)^2 *
        ‖unitGridVector M (evolutionSignal hs frequency a)‖^2) ∧
    ‖unitGridVector M (evolutionSignal hs frequency a) - unitGridVector M (jetPolynomialSignal a)‖ ≤
      sectionApproximationError d h s * ‖unitGridVector M (evolutionSignal hs frequency a)‖ ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ‖jetPolynomialSignal a t‖ ≤
      sectionPolynomialSupConstant d h s / Real.sqrt (M + 1 : ℝ) *
        ‖unitGridVector M (evolutionSignal hs frequency a)‖) ∧
    Real.sqrt (∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2) ≤
      ‖unitGridVector M (evolutionSignal hs frequency a)‖ /
        (Real.sqrt (M + 1 : ℝ) * (sectionGridEnergyFactor d h s - sectionRelativeError d h s)) := by
  let E : ℝ := ∫ t in (0 : ℝ)..1, ‖jetPolynomialSignal a t‖^2
  have hE : 0 ≤ E := intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun t => sq_nonneg _)
  have hq := sectionRowConstant_gt_one hd
  have he := sectionRelativeError_pos (n := h) hd hs
  obtain ⟨hb, hb1⟩ := sectionGridEnergyFactor_bounds (n := h) hd hs
  have hδ : 0 ≤ sectionApproximationError d h s := by
    unfold sectionApproximationError
    positivity
  have hb2 : 0 < 1 - (sectionGridEnergyFactor d h s)^2 := by nlinarith only [hb, hb1]
  have hbudget := (div_le_iff₀ hb2).1 hsize
  have hgrid0 := jetPolynomial_energy_mul_gridSize_sub_loss_le hs hM a
  have hgrid : (sectionGridEnergyFactor d h s)^2 * (M + 1 : ℝ) * E ≤
      ‖unitGridVector M (jetPolynomialSignal a)‖^2 := by
    rw [unitGridVector_norm_sq]
    have ht : (sectionGridEnergyFactor d h s)^2 * (M + 1 : ℝ) ≤
        (M : ℝ) - 4 * ((s - 1 : ℕ) : ℝ)^2 * (s : ℝ)^2 := by
      change 4 * ((s - 1 : ℕ) : ℝ)^2 * (s : ℝ)^2 + (sectionGridEnergyFactor d h s)^2 ≤
        (M : ℝ) * (1 - (sectionGridEnergyFactor d h s)^2) at hbudget
      nlinarith only [hbudget]
    have ht' := mul_le_mul_of_nonneg_right ht hE
    exact ht'.trans (by simpa only [E, mul_comm] using hgrid0)
  have hpoly : ∀ t ∈ Icc (0 : ℝ) 1, ‖jetPolynomialSignal a t‖ ≤ (s : ℝ) * Real.sqrt E := by
    intro t ht
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
    simpa only [mul_pow, Real.sq_sqrt hE, E] using jetPolynomial_unit_row_bound_sharp hs a ht
  have hclose := section_signal_error (n := h) hd hs frequency a hfrequency
  obtain ⟨hrowbudget, hsupbudget, herrorbudget, hsupconstant⟩ := sectionGrid_budgets (n := h) hd hs
  obtain ⟨hrow, herr, hsup⟩ := unitGrid_transfer hs hM (jetPolynomialSignal a)
    (evolutionSignal hs frequency a) hE (by linarith) he.le hb.le hδ hpoly hclose hgrid
    hrowbudget.le hsupbudget herrorbudget.le
  refine ⟨hrow, herr, ?_, ?_⟩
  · simpa only [← hsupconstant] using hsup
  · exact unitGrid_sqrt_energy_le hM _ _ hE he.le hb.le
      (sectionGridEnergyFactor_sub_error hd hs) hclose hgrid

/-- Angular modulation preserves all local estimates, including the
continuous polynomial energy needed for the variation correlation bound. -/
theorem angularClump_explicit_section_bounds {d h s M : ℕ}
    (hd : 1 ≤ d) (hs : 0 < s) (hM : 0 < M)
    (hsize : sectionGridResolution d h s ≤ (M : ℝ))
    (node : Fin s → ℝ) (center : ℝ)
    (hwithin : WithinAngularClump M node center (sectionJetRadius d h s))
    (u : EuclideanSpace ℂ (Fin (M + 1)))
    (hu : u ∈ ClusteredVandermonde.clusterSubspace M node) :
    (∀ k : Fin (M + 1), (M + 1 : ℝ) * ‖u k‖^2 ≤
      sectionRowConstant d * (s : ℝ)^2 * ‖u‖^2) ∧
    ∃ c : Fin s → ℂ,
      ‖u - PolynomialCrossCorrelation.modulatedPolynomial M center c‖ ≤
        sectionApproximationError d h s * ‖u‖ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖coefficientPolynomialSignal c t‖ ≤
        sectionPolynomialSupConstant d h s / Real.sqrt (M + 1 : ℝ) * ‖u‖) ∧
      Real.sqrt (∫ t in (0 : ℝ)..1, ‖coefficientPolynomialSignal c t‖^2) ≤
        ‖u‖ / (Real.sqrt (M + 1 : ℝ) *
          (sectionGridEnergyFactor d h s - sectionRelativeError d h s)) := by
  classical
  obtain ⟨coefficient, rfl⟩ := clusterSubspace_coefficient_representation node u hu
  choose p hp using hwithin
  let frequency : Fin s → ℂ := fun j => Complex.I * (((M : ℝ) *
    (node j - center + 2 * Real.pi * p j) : ℝ) : ℂ)
  let a := ExponentialCompanion.initialJet frequency coefficient
  have hfrequency := scaled_frequency_norm_le hM node center (sectionJetRadius d h s)
    (sectionJetRadius_pos hd hs).le p hp
  have heq := angularSignal_eq_evolutionVector hs hM node coefficient center p
  change angularSignal M node coefficient = evolutionVector hs M frequency a center at heq
  have hevol : evolutionVector hs M frequency a center =
      modulatedUnitGridVector M center (evolutionSignal hs frequency a) := rfl
  have hnorm : ‖angularSignal M node coefficient‖ =
      ‖unitGridVector M (evolutionSignal hs frequency a)‖ := by
    rw [heq, hevol, modulatedUnitGridVector_norm]
  obtain ⟨hrow, herr, hsup, henergy⟩ := smallFrequency_explicit_grid_bounds hd hs hM frequency a hfrequency hsize
  refine ⟨?_, jetCoefficient a, ?_, ?_, ?_⟩
  · intro k
    rw [hnorm, heq, evolutionVector_coordinate_norm]
    exact hrow k
  · rw [heq, hevol, ← modulatedUnitGridVector_jet, modulatedUnitGridVector_sub_norm, modulatedUnitGridVector_norm]
    exact herr
  · rw [hnorm]
    have hp : coefficientPolynomialSignal (jetCoefficient a) = jetPolynomialSignal a :=
      (jetPolynomialSignal_eq_coefficientPolynomialSignal a).symm
    rw [hp]
    exact hsup
  · rw [hnorm]
    have hp : coefficientPolynomialSignal (jetCoefficient a) = jetPolynomialSignal a :=
      (jetPolynomialSignal_eq_coefficientPolynomialSignal a).symm
    rw [hp]
    exact henergy

end
end LeanNumDetect.QuantitativeClumpSectionBounds
