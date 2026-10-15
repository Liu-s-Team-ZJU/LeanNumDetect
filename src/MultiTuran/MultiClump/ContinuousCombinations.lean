import MultiTuran.MultiClump.Convolution
import MultiTuran.MultiClump.RowShift

/-! # Actual continuous energy of finite weighted combinations

The estimates integrate finite Cauchy--Schwarz over the measured thickening.
Polynomial multipliers are expanded into genuine translations of the source
coefficients before applying this estimate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
open MeasureTheory

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

theorem exponentialSum_weighted_sum {σ : Type*} [Fintype σ] {d n : ℕ}
    (Y : Fin n → Point d) (a : σ → ℂ) (c : σ → Fin n → ℂ) (t : Point d) :
    exponentialSum Y (fun j => ∑ i, a i * c i j) t =
      ∑ i, a i * exponentialSum Y (c i) t := by
  classical
  unfold exponentialSum
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem norm_weighted_sum_sq_le {σ : Type*} [Fintype σ]
    (a z : σ → ℂ) :
    ‖∑ i, a i * z i‖ ^ 2 ≤
      (∑ i, ‖a i‖) * ∑ i, ‖a i‖ * ‖z i‖ ^ 2 := by
  classical
  calc
    _ ≤ (∑ i, ‖a i * z i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ = (∑ i, ‖a i‖ * ‖z i‖) ^ 2 := by simp only [norm_mul]
    _ ≤ _ := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
        (r := fun i => ‖a i‖ * ‖z i‖)
        (f := fun i => ‖a i‖)
        (g := fun i => ‖a i‖ * ‖z i‖ ^ 2) Finset.univ
      · intro i _; exact norm_nonneg _
      · intro i _; positivity
      · intro i _; exact le_of_eq (by ring)

/-- Weighted finite Cauchy--Schwarz for the actual integral over `E_Λ`. -/
theorem continuousEnergy_weighted_sum_le {σ : Type*} [Fintype σ] {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d)
    (a : σ → ℂ) (c : σ → Fin n → ℂ) :
    continuousEnergy G Y (fun j => ∑ i, a i * c i j) ≤
      (∑ i, ‖a i‖) * ∑ i, ‖a i‖ * continuousEnergy G Y (c i) := by
  classical
  have hi (i : σ) : IntegrableOn
      (fun t => ‖exponentialSum Y (c i) t‖ ^ 2) G.thickening :=
    exponentialSum_energy_integrableOn Y (c i) G.thickening_isCompact
  have hw (i : σ) : IntegrableOn
      (fun t => ‖a i‖ * ‖exponentialSum Y (c i) t‖ ^ 2) G.thickening :=
    (hi i).const_mul ‖a i‖
  have hsum : IntegrableOn
      (fun t => ∑ i, ‖a i‖ * ‖exponentialSum Y (c i) t‖ ^ 2) G.thickening :=
    integrable_finsetSum _ (fun i _ => hw i)
  unfold continuousEnergy setEnergy
  calc
    _ ≤ ∫ t in G.thickening,
        (∑ i, ‖a i‖) * ∑ i, ‖a i‖ * ‖exponentialSum Y (c i) t‖ ^ 2 := by
      apply setIntegral_mono_on
        (exponentialSum_energy_integrableOn Y _ G.thickening_isCompact)
        (hsum.const_mul _) G.thickening_isCompact.measurableSet
      intro t _
      rw [exponentialSum_weighted_sum]
      exact norm_weighted_sum_sq_le a (fun i => exponentialSum Y (c i) t)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum]
      · simp only [integral_const_mul]
      · exact fun i _ => hw i

private theorem angularValue_one_block {d W D : ℕ}
    (P : NumDetect.SegmentedPolynomial d W 0 D) (y : Point d) :
    P.angularValue y = ∑ i, P.coeff i * Complex.exp
      (Complex.I * ((∑ q, ((i q).2 : ℝ) * y q : ℝ) : ℂ)) := by
  rw [NumDetect.SegmentedPolynomial.angularValue_eq_angularTrigPolynomial]
  unfold angularTrigPolynomial NumDetect.segmentedPolynomialFrequency
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  apply congrArg (fun t : ℝ => Complex.I * (t : ℂ))
  apply Finset.sum_congr rfl
  intro q _
  simp

/-- The multiplier coefficients are an exact finite sum of translated
coefficient families, with the positive translation sign. -/
theorem multiplier_coefficients_eq_sum {d n W D : ℕ}
    (P : NumDetect.SegmentedPolynomial d W 0 D) (Y : Fin n → Point d)
    (c : Fin n → ℂ) (k : Fin n) :
    c k * P.angularValue (Y k) =
      ∑ i, P.coeff i * phaseCoefficients Y c (fun q => ((i q).2 : ℝ)) k := by
  classical
  rw [angularValue_one_block]
  simp only [Finset.mul_sum, phaseCoefficients]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A genuine common bound for all translated energies controls the
polynomial multiplier by the square of its Fourier coefficient mass. -/
theorem multiplier_continuousEnergy_le {d n W D : ℕ}
    (G : SegmentedGrid d) (P : NumDetect.SegmentedPolynomial d W 0 D)
    (Y : Fin n → Point d) (c : Fin n → ℂ) {C E : ℝ}
    (htranslated : ∀ i : NumDetect.SegmentedIndex d W 0,
      continuousEnergy G Y (phaseCoefficients Y c (fun q => ((i q).2 : ℝ))) ≤ C * E) :
    continuousEnergy G Y (fun j => c j * P.angularValue (Y j)) ≤ P.mass ^ 2 * C * E := by
  classical
  have hvec : (fun j => c j * P.angularValue (Y j)) =
      (fun j => ∑ i, P.coeff i * phaseCoefficients Y c (fun q => ((i q).2 : ℝ)) j) := by
    funext j
    exact multiplier_coefficients_eq_sum P Y c j
  rw [hvec]
  have hsum : (∑ i, ‖P.coeff i‖ *
      continuousEnergy G Y (phaseCoefficients Y c (fun q => ((i q).2 : ℝ)))) ≤
        P.mass * (C * E) := by
    calc
      _ ≤ ∑ i, ‖P.coeff i‖ * (C * E) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (htranslated i) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; rfl
  calc
    _ ≤ P.mass * ∑ i, ‖P.coeff i‖ *
        continuousEnergy G Y (phaseCoefficients Y c (fun q => ((i q).2 : ℝ))) :=
      continuousEnergy_weighted_sum_le G Y P.coeff
        (fun i => phaseCoefficients Y c (fun q => ((i q).2 : ℝ)))
    _ ≤ P.mass * (P.mass * (C * E)) :=
      mul_le_mul_of_nonneg_left hsum (NumDetect.SegmentedPolynomial.mass_nonneg P)
    _ = _ := by ring

end
end LeanNumDetect.MultiTuran.MultiClump
