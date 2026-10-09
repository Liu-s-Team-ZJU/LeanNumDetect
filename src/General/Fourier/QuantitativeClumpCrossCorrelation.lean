import General.Fourier.QuantitativeAngularSectionBounds

/-! Independently selected clump width, grid bandwidth, and separation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators InnerProductSpace
open Set MeasureTheory Matrix WithLp

namespace LeanNumDetect.QuantitativeClumpSectionBounds
open AngularClumpSectionBounds PolynomialEvaluationBounds ClumpJetApproximation
open PolynomialCrossCorrelation
noncomputable section

/-- The sharp polynomial-energy correlation estimate is supplied separately
from the radius and finite-grid transfer. -/
def PolynomialEnergyCorrelationBound (s t M nstar : ℕ) : Prop :=
  ∀ (c : Fin s → ℂ) (c' : Fin t → ℂ) (x y η : ℝ), 0 < η →
    (∀ p : ℤ, η ≤ |y - x - 2 * Real.pi * p|) →
    ‖⟪modulatedPolynomial M x c, modulatedPolynomial M y c'⟫_ℂ‖ ≤
      (Real.pi / η) * ((nstar : ℝ)^2 + (nstar : ℝ) * Real.sqrt ((nstar : ℝ)^2 - 1)) *
        Real.sqrt (∫ z in (0 : ℝ)..1, ‖coefficientPolynomialSignal c z‖^2) *
        Real.sqrt (∫ z in (0 : ℝ)..1, ‖coefficientPolynomialSignal c' z‖^2)

theorem angularClump_explicit_cross_bound {d n nstar s t M : ℕ}
    (hd : 1 ≤ d) (hnstar : 0 < nstar) (hsize : nstar < n)
    (hs : 0 < s) (hsmax : s ≤ nstar) (ht : 0 < t) (htmax : t ≤ nstar)
    (hM : quantitativeClumpBandwidth d n nstar hnstar ≤ (M : ℝ))
    (hcorrelation : PolynomialEnergyCorrelationBound s t M nstar)
    (node : Fin s → ℝ) (node' : Fin t → ℝ) (x y : ℝ)
    (hwithin : WithinAngularClump M node x (quantitativeClumpRadius d (n - nstar) nstar hnstar))
    (hwithin' : WithinAngularClump M node' y (quantitativeClumpRadius d (n - nstar) nstar hnstar))
    (hsep : ∀ p : ℤ, quantitativeClumpPairSeparation d n nstar hnstar / (M : ℝ) ≤
      |y - x - 2 * Real.pi * p|)
    (u : EuclideanSpace ℂ (Fin (M + 1))) (hu : u ∈ ClusteredVandermonde.clusterSubspace M node)
    (v : EuclideanSpace ℂ (Fin (M + 1))) (hv : v ∈ ClusteredVandermonde.clusterSubspace M node') :
    ‖⟪u, v⟫_ℂ‖ ≤ sectionCorrelationConstant (n - nstar) * ‖u‖ * ‖v‖ := by
  have hn : 0 < n := by omega
  have hMR : 0 < (M : ℝ) :=
    (by exact_mod_cast hn : (0 : ℝ) < n).trans_le ((quantitativeClumpBandwidth_ge_total hnstar).trans hM)
  have hMN : 0 < M := by exact_mod_cast hMR
  have hN : 0 < (M + 1 : ℝ) := by positivity
  have hNs : 0 < Real.sqrt (M + 1 : ℝ) := Real.sqrt_pos.2 hN
  have hrS := explicitSectionRadius_le hnstar (sectionJetRadius d (n - nstar)) hs hsmax
  have hrT := explicitSectionRadius_le hnstar (sectionJetRadius d (n - nstar)) ht htmax
  obtain ⟨_, c, huc, _, hEc⟩ := angularClump_explicit_section_bounds hd hs hMN
    ((quantitativeClumpBandwidth_ge_grid hnstar hs hsmax).trans hM) node x
    (hwithin.mono hMN hrS) u hu
  obtain ⟨_, c', hvc, _, hEc'⟩ := angularClump_explicit_section_bounds hd ht hMN
    ((quantitativeClumpBandwidth_ge_grid hnstar ht htmax).trans hM) node' y
    (hwithin'.mono hMN hrT) v hv
  let H := maximumPolynomialEnergyConstant d (n - nstar) nstar hnstar
  let Δ := maximumApproximationError d (n - nstar) nstar hnstar
  let K := Real.pi * ((nstar : ℝ)^2 + (nstar : ℝ) * Real.sqrt ((nstar : ℝ)^2 - 1))
  let S := quantitativeClumpPairSeparation d n nstar hnstar
  let g := sectionCrossBudget d (n - nstar) nstar hnstar
  have hH : 0 < H := maximumPolynomialEnergyConstant_pos hd hnstar
  have hS : 0 < S := quantitativeClumpPairSeparation_pos hd hnstar hsize
  have hK : 0 < K := by
    have hstarR : (0 : ℝ) < nstar := by exact_mod_cast hnstar
    dsimp [K]
    positivity
  have hΔ : 0 ≤ Δ := (maximumApproximationError_bounds hd (by omega) hnstar).1
  have hEcH : Real.sqrt (∫ z in (0 : ℝ)..1, ‖coefficientPolynomialSignal c z‖^2) ≤
      (H / Real.sqrt (M + 1 : ℝ)) * ‖u‖ := by
    calc
      _ ≤ ‖u‖ / (Real.sqrt (M + 1 : ℝ) *
          (sectionGridEnergyFactor d (n - nstar) s - sectionRelativeError d (n - nstar) s)) := hEc
      _ = sectionPolynomialEnergyConstant d (n - nstar) s / Real.sqrt (M + 1 : ℝ) * ‖u‖ := by
        unfold sectionPolynomialEnergyConstant
        field_simp
      _ ≤ _ := by
        gcongr
        exact le_finiteDimensionMaximum hnstar _ hs hsmax
  have hEc'H : Real.sqrt (∫ z in (0 : ℝ)..1, ‖coefficientPolynomialSignal c' z‖^2) ≤
      (H / Real.sqrt (M + 1 : ℝ)) * ‖v‖ := by
    calc
      _ ≤ ‖v‖ / (Real.sqrt (M + 1 : ℝ) *
          (sectionGridEnergyFactor d (n - nstar) t - sectionRelativeError d (n - nstar) t)) := hEc'
      _ = sectionPolynomialEnergyConstant d (n - nstar) t / Real.sqrt (M + 1 : ℝ) * ‖v‖ := by
        unfold sectionPolynomialEnergyConstant
        field_simp
      _ ≤ _ := by
        gcongr
        exact le_finiteDimensionMaximum hnstar _ ht htmax
  have hpoly := hcorrelation c c' x y (S / (M : ℝ)) (div_pos hS hMR) hsep
  have hscale : K / (S / (M : ℝ)) * (H / Real.sqrt (M + 1 : ℝ)) *
      (H / Real.sqrt (M + 1 : ℝ)) ≤ g := by
    have heq : K / (S / (M : ℝ)) * (H / Real.sqrt (M + 1 : ℝ)) *
        (H / Real.sqrt (M + 1 : ℝ)) =
        (K * H^2 / S) * ((M : ℝ) / (M + 1 : ℝ)) := by
      field_simp [hS.ne', hMR.ne', hNs.ne']
      ring_nf
      simpa only [add_comm] using (Real.sq_sqrt hN.le).symm
    have hratio : K * H^2 / S = g := by
      apply (div_eq_iff hS.ne').2
      simpa only [K, H, S, g, sectionCrossNumerator, mul_comm] using
        (quantitativeClumpPairSeparation_mul_budget hd hnstar hsize).symm
    rw [heq, hratio]
    exact mul_le_of_le_one_right (sectionCrossBudget_pos hd (by omega) hnstar).le
      ((div_le_one hN).2 (by linarith))
  have hpoly' : ‖⟪modulatedPolynomial M x c, modulatedPolynomial M y c'⟫_ℂ‖ ≤
      g * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ K / (S / (M : ℝ)) *
          ((H / Real.sqrt (M + 1 : ℝ)) * ‖u‖) *
          ((H / Real.sqrt (M + 1 : ℝ)) * ‖v‖) := by
        have h := hpoly
        have hk : Real.pi / (S / (M : ℝ)) *
            ((nstar : ℝ)^2 + (nstar : ℝ) * Real.sqrt ((nstar : ℝ)^2 - 1)) =
            K / (S / (M : ℝ)) := by dsimp [K]; ring
        rw [hk] at h
        exact h.trans (by gcongr)
      _ = (K / (S / (M : ℝ)) * (H / Real.sqrt (M + 1 : ℝ)) *
          (H / Real.sqrt (M + 1 : ℝ))) * ‖u‖ * ‖v‖ := by ring
      _ ≤ _ := by gcongr
  have huΔ : ‖u - modulatedPolynomial M x c‖ ≤ Δ * ‖u‖ := huc.trans
    (mul_le_mul_of_nonneg_right (le_finiteDimensionMaximum hnstar _ hs hsmax) (norm_nonneg u))
  have hvΔ : ‖v - modulatedPolynomial M y c'‖ ≤ Δ * ‖v‖ := hvc.trans
    (mul_le_mul_of_nonneg_right (le_finiteDimensionMaximum hnstar _ ht htmax) (norm_nonneg v))
  have hresult := inner_approximation_bound u v _ _ hΔ huΔ hvΔ hpoly'
  have hbudget : g + 2 * Δ + Δ^2 = sectionCorrelationConstant (n - nstar) := by
    dsimp [g, Δ, sectionCrossBudget]
    ring
  simpa only [hbudget] using hresult

def PolynomialSizeEnergyCorrelationBound (s t M : ℕ) : Prop :=
  ∀ (c : Fin s → ℂ) (c' : Fin t → ℂ) (x y η : ℝ), 0 < η →
    (∀ p : ℤ, η ≤ |y - x - 2 * Real.pi * p|) →
    ‖⟪modulatedPolynomial M x c, modulatedPolynomial M y c'⟫_ℂ‖ ≤
      (Real.pi / η) * ((s : ℝ) * (t : ℝ) + ((s : ℝ)^2 + (t : ℝ)^2) / 2) *
        Real.sqrt (∫ z in (0 : ℝ)..1, ‖coefficientPolynomialSignal c z‖^2) *
        Real.sqrt (∫ z in (0 : ℝ)..1, ‖coefficientPolynomialSignal c' z‖^2)

theorem angularClump_global_polynomial_bounds {d n nstar s M : ℕ}
    (hd : 1 ≤ d) (hnstar : 0 < nstar) (hn : 0 < n)
    (hs : 0 < s) (hsmax : s ≤ nstar)
    (hM : quantitativeClumpBandwidth d n nstar hnstar ≤ (M : ℝ))
    (node : Fin s → ℝ) (x : ℝ)
    (hwithin : WithinAngularClump M node x (quantitativeClumpRadius d (n - nstar) nstar hnstar))
    (u : EuclideanSpace ℂ (Fin (M + 1))) (hu : u ∈ ClusteredVandermonde.clusterSubspace M node) :
    ∃ c : Fin s → ℂ,
      ‖u - modulatedPolynomial M x c‖ ≤ maximumApproximationError d (n - nstar) nstar hnstar * ‖u‖ ∧
      Real.sqrt (∫ z in (0 : ℝ)..1, ‖coefficientPolynomialSignal c z‖^2) ≤
        maximumPolynomialEnergyConstant d (n - nstar) nstar hnstar /
          Real.sqrt (M + 1 : ℝ) * ‖u‖ := by
  have hMR : 0 < (M : ℝ) := (by exact_mod_cast hn : (0 : ℝ) < n).trans_le
    ((quantitativeClumpBandwidth_ge_total hnstar).trans hM)
  have hMN : 0 < M := by exact_mod_cast hMR
  have hr := explicitSectionRadius_le hnstar (sectionJetRadius d (n - nstar)) hs hsmax
  obtain ⟨_, c, herr, _, henergy⟩ := angularClump_explicit_section_bounds hd hs hMN
    ((quantitativeClumpBandwidth_ge_grid hnstar hs hsmax).trans hM) node x
    (hwithin.mono hMN hr) u hu
  refine ⟨c, herr.trans (mul_le_mul_of_nonneg_right
    (le_finiteDimensionMaximum hnstar _ hs hsmax) (norm_nonneg u)), ?_⟩
  calc
    _ ≤ ‖u‖ / (Real.sqrt (M + 1 : ℝ) *
        (sectionGridEnergyFactor d (n - nstar) s - sectionRelativeError d (n - nstar) s)) := henergy
    _ = sectionPolynomialEnergyConstant d (n - nstar) s / Real.sqrt (M + 1 : ℝ) * ‖u‖ := by
      unfold sectionPolynomialEnergyConstant
      field_simp
    _ ≤ _ := by
      gcongr
      exact le_finiteDimensionMaximum hnstar _ hs hsmax

theorem angularClump_explicit_size_cross_bound {d n nstar s t M : ℕ}
    (hd : 1 ≤ d) (hnstar : 0 < nstar) (hsize : nstar < n)
    (hs : 0 < s) (hsmax : s ≤ nstar) (ht : 0 < t) (htmax : t ≤ nstar)
    (hM : quantitativeClumpBandwidth d n nstar hnstar ≤ (M : ℝ))
    (hcorrelation : PolynomialSizeEnergyCorrelationBound s t M)
    (node : Fin s → ℝ) (node' : Fin t → ℝ) (x y S : ℝ) (hS : 0 < S)
    (hwithin : WithinAngularClump M node x (quantitativeClumpRadius d (n - nstar) nstar hnstar))
    (hwithin' : WithinAngularClump M node' y (quantitativeClumpRadius d (n - nstar) nstar hnstar))
    (hsep : ∀ p : ℤ, S / (M : ℝ) ≤ |y - x - 2 * Real.pi * p|)
    (u : EuclideanSpace ℂ (Fin (M + 1))) (hu : u ∈ ClusteredVandermonde.clusterSubspace M node)
    (v : EuclideanSpace ℂ (Fin (M + 1))) (hv : v ∈ ClusteredVandermonde.clusterSubspace M node') :
    ‖⟪u, v⟫_ℂ‖ ≤
      ((Real.pi * (maximumPolynomialEnergyConstant d (n - nstar) nstar hnstar)^2 / S) *
        ((s : ℝ) * (t : ℝ) + ((s : ℝ)^2 + (t : ℝ)^2) / 2) +
        2 * maximumApproximationError d (n - nstar) nstar hnstar +
        (maximumApproximationError d (n - nstar) nstar hnstar)^2) * ‖u‖ * ‖v‖ := by
  have hn : 0 < n := by omega
  have hMR : 0 < (M : ℝ) := (by exact_mod_cast hn : (0 : ℝ) < n).trans_le
    ((quantitativeClumpBandwidth_ge_total hnstar).trans hM)
  have hN : 0 < (M + 1 : ℝ) := by positivity
  have hNs : 0 < Real.sqrt (M + 1 : ℝ) := Real.sqrt_pos.2 hN
  obtain ⟨c, huc, hEc⟩ := angularClump_global_polynomial_bounds hd hnstar hn hs hsmax hM node x hwithin u hu
  obtain ⟨c', hvc, hEc'⟩ := angularClump_global_polynomial_bounds hd hnstar hn ht htmax hM node' y hwithin' v hv
  let H := maximumPolynomialEnergyConstant d (n - nstar) nstar hnstar
  let Δ := maximumApproximationError d (n - nstar) nstar hnstar
  let K := (s : ℝ) * (t : ℝ) + ((s : ℝ)^2 + (t : ℝ)^2) / 2
  let α := Real.pi * H^2 / S
  have hH : 0 < H := maximumPolynomialEnergyConstant_pos hd hnstar
  have hΔ : 0 ≤ Δ := (maximumApproximationError_bounds hd (by omega) hnstar).1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoly := hcorrelation c c' x y (S / (M : ℝ)) (div_pos hS hMR) hsep
  have hscale : Real.pi / (S / (M : ℝ)) * (H / Real.sqrt (M + 1 : ℝ)) *
      (H / Real.sqrt (M + 1 : ℝ)) ≤ α := by
    have heq : Real.pi / (S / (M : ℝ)) * (H / Real.sqrt (M + 1 : ℝ)) *
        (H / Real.sqrt (M + 1 : ℝ)) = α * ((M : ℝ) / (M + 1 : ℝ)) := by
      dsimp [α]
      field_simp [hS.ne', hMR.ne', hNs.ne']
      ring_nf
      simpa only [add_comm] using (Real.sq_sqrt hN.le).symm
    rw [heq]
    exact mul_le_of_le_one_right (by dsimp [α]; positivity) ((div_le_one hN).2 (by linarith))
  have hpoly' : ‖⟪modulatedPolynomial M x c, modulatedPolynomial M y c'⟫_ℂ‖ ≤ α * K * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ Real.pi / (S / (M : ℝ)) * K * (H / Real.sqrt (M + 1 : ℝ) * ‖u‖) *
          (H / Real.sqrt (M + 1 : ℝ) * ‖v‖) := hpoly.trans (by gcongr)
      _ = (Real.pi / (S / (M : ℝ)) * (H / Real.sqrt (M + 1 : ℝ)) *
          (H / Real.sqrt (M + 1 : ℝ))) * K * ‖u‖ * ‖v‖ := by ring
      _ ≤ _ := by gcongr
  exact inner_approximation_bound u v _ _ hΔ huc hvc hpoly'

end
end LeanNumDetect.QuantitativeClumpSectionBounds
