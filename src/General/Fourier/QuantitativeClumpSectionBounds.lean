import General.Fourier.AngularClumpSectionBounds
import General.Fourier.SharpPolynomialEvaluation
import General.Fourier.QuantitativeCompanionBounds
import General.Fourier.QuantitativePolynomialBounds
import General.Fourier.QuantitativePolynomialGridBounds
import General.Fourier.QuantitativePolynomialCrossCorrelation
import Mathlib.Data.Finset.Lattice.Fold

/-! Explicit finite-grid transfer and independently chosen clump geometry.
The radius, grid resolution and cross-correlation coefficient remain separate;
none is squared merely because it also controls a different threshold. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators InnerProductSpace
open Set MeasureTheory Matrix WithLp

namespace LeanNumDetect.QuantitativeClumpSectionBounds
open AngularClumpSectionBounds PolynomialEvaluationBounds ClumpJetApproximation
noncomputable section

def unitGridVector (M : ℕ) (f : ℝ → ℂ) : EuclideanSpace ℂ (Fin (M + 1)) :=
  toLp 2 (fun k => f ((k.val : ℝ) / M))

theorem unitGridVector_norm_sq (M : ℕ) (f : ℝ → ℂ) :
    ‖unitGridVector M f‖^2 =
      ∑ k ∈ Finset.range (M + 1), ‖f ((k : ℝ) / M)‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => ‖f ((k : ℝ) / M)‖^2) (M + 1)

/-- A finite-grid triangle argument uses only a uniform signal error;
no derivative estimate for the perturbed exponential signal is needed. -/
theorem unitGrid_transfer {s M : ℕ} (hs : 0 < s) (hM : 0 < M)
    (p f : ℝ → ℂ) {E q e b δ : ℝ}
    (hE : 0 ≤ E) (hq : 0 < q) (he : 0 ≤ e) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (hpoly : ∀ t ∈ Icc (0 : ℝ) 1, ‖p t‖ ≤ (s : ℝ) * Real.sqrt E)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t - p t‖ ≤ e * Real.sqrt E)
    (hgrid : b^2 * (M + 1 : ℝ) * E ≤ ‖unitGridVector M p‖^2)
    (hrowbudget : (s : ℝ) + e ≤ Real.sqrt q * (s : ℝ) * (b - e))
    (hsupbudget : 1 ≤ Real.sqrt q * (b - e))
    (herrorbudget : e ≤ δ * (b - e)) :
    (∀ k : Fin (M + 1), (M + 1 : ℝ) * ‖f ((k.val : ℝ) / M)‖^2 ≤
      q * (s : ℝ)^2 * ‖unitGridVector M f‖^2) ∧
    ‖unitGridVector M f - unitGridVector M p‖ ≤ δ * ‖unitGridVector M f‖ ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ‖p t‖ ≤
      ((s : ℝ) / (b - e) / Real.sqrt (M + 1 : ℝ)) * ‖unitGridVector M f‖) := by
  have hN : 0 < (M + 1 : ℝ) := by positivity
  have hNs : 0 < Real.sqrt (M + 1 : ℝ) := Real.sqrt_pos.2 hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hunit (k : Fin (M + 1)) : (k.val : ℝ) / M ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hMR).2 (by exact_mod_cast (show k.val ≤ M by omega))⟩
  have hP : b * Real.sqrt (M + 1 : ℝ) * Real.sqrt E ≤ ‖unitGridVector M p‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).1
    simpa only [mul_pow, Real.sq_sqrt hN.le, Real.sq_sqrt hE] using hgrid
  have herror : ‖unitGridVector M f - unitGridVector M p‖ ≤
      Real.sqrt (M + 1 : ℝ) * (e * Real.sqrt E) := by
    apply norm_le_sqrt_card_mul _ _ (by positivity)
    intro k
    exact hclose _ (hunit k)
  have htriangle : ‖unitGridVector M p‖ ≤
      ‖unitGridVector M f‖ + ‖unitGridVector M f - unitGridVector M p‖ := by
    simpa [add_comm, norm_sub_rev] using
      norm_add_le (unitGridVector M f) (unitGridVector M p - unitGridVector M f)
  have hF : (b - e) * Real.sqrt (M + 1 : ℝ) * Real.sqrt E ≤
      ‖unitGridVector M f‖ := by nlinarith only [hP, herror, htriangle]
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have hpoint : ‖f ((k.val : ℝ) / M)‖ ≤ ((s : ℝ) + e) * Real.sqrt E := by
      have ht : ‖f ((k.val : ℝ) / M)‖ ≤
          ‖p ((k.val : ℝ) / M)‖ + ‖f ((k.val : ℝ) / M) - p ((k.val : ℝ) / M)‖ := by
        simpa [add_comm] using norm_add_le (p ((k.val : ℝ) / M))
          (f ((k.val : ℝ) / M) - p ((k.val : ℝ) / M))
      nlinarith only [ht, hpoly _ (hunit k), hclose _ (hunit k)]
    have h₁ := mul_le_mul_of_nonneg_left hpoint hNs.le
    have h₂ := mul_le_mul_of_nonneg_right hrowbudget
      (mul_nonneg hNs.le (Real.sqrt_nonneg E))
    have h₃ := mul_le_mul_of_nonneg_left hF
      (show 0 ≤ Real.sqrt q * (s : ℝ) by positivity)
    have hn : Real.sqrt (M + 1 : ℝ) * ‖f ((k.val : ℝ) / M)‖ ≤
        Real.sqrt q * (s : ℝ) * ‖unitGridVector M f‖ := by
      nlinarith only [h₁, h₂, h₃]
    have hh := (sq_le_sq₀ (by positivity) (by positivity)).2 hn
    simpa only [mul_pow, Real.sq_sqrt hN.le, Real.sq_sqrt hq.le] using hh
  · have h₁ := mul_le_mul_of_nonneg_right herrorbudget
      (mul_nonneg hNs.le (Real.sqrt_nonneg E))
    have h₂ := mul_le_mul_of_nonneg_left hF hδ
    nlinarith only [herror, h₁, h₂]
  · intro t ht
    have hbe : 0 < b - e := by nlinarith [Real.sqrt_pos.2 hq]
    have h₁ := mul_le_mul_of_nonneg_left (hpoly t ht)
      (mul_nonneg hbe.le hNs.le)
    have h₂ := mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg s)
    rw [div_div, div_mul_eq_mul_div]
    apply (le_div_iff₀ (mul_pos hbe hNs)).2
    nlinarith only [h₁, h₂]

def finiteDimensionMaximum (nstar : ℕ) (hnstar : 0 < nstar) (f : ℕ → ℝ) : ℝ :=
  Finset.univ.sup' (show (Finset.univ : Finset (Fin nstar)).Nonempty from
    ⟨⟨0, hnstar⟩, Finset.mem_univ _⟩) (fun i : Fin nstar => f (i.val + 1))

def finiteDimensionMinimum (nstar : ℕ) (hnstar : 0 < nstar) (f : ℕ → ℝ) : ℝ :=
  Finset.univ.inf' (show (Finset.univ : Finset (Fin nstar)).Nonempty from
    ⟨⟨0, hnstar⟩, Finset.mem_univ _⟩) (fun i : Fin nstar => f (i.val + 1))

theorem le_finiteDimensionMaximum {nstar s : ℕ} (hnstar : 0 < nstar)
    (f : ℕ → ℝ) (hs : 0 < s) (hmax : s ≤ nstar) :
    f s ≤ finiteDimensionMaximum nstar hnstar f := by
  let i : Fin nstar := ⟨s - 1, by omega⟩
  have hi : i.val + 1 = s := by dsimp [i]; omega
  have h := Finset.le_sup' (fun j : Fin nstar => f (j.val + 1)) (Finset.mem_univ i)
  simpa only [hi, finiteDimensionMaximum] using h

theorem finiteDimensionMinimum_le {nstar s : ℕ} (hnstar : 0 < nstar)
    (f : ℕ → ℝ) (hs : 0 < s) (hmax : s ≤ nstar) :
    finiteDimensionMinimum nstar hnstar f ≤ f s := by
  let i : Fin nstar := ⟨s - 1, by omega⟩
  have hi : i.val + 1 = s := by dsimp [i]; omega
  have h := Finset.inf'_le (fun j : Fin nstar => f (j.val + 1)) (Finset.mem_univ i)
  simpa only [hi, finiteDimensionMinimum] using h

theorem finiteDimensionMinimum_pos {nstar : ℕ} (hnstar : 0 < nstar)
    (f : ℕ → ℝ) (hpos : ∀ s, 0 < s → s ≤ nstar → 0 < f s) :
    0 < finiteDimensionMinimum nstar hnstar f := by
  unfold finiteDimensionMinimum
  apply (Finset.lt_inf'_iff _).2
  intro i _
  exact hpos (i.val + 1) (by omega) (by omega)

def explicitSectionRadius (nstar : ℕ) (hnstar : 0 < nstar) (radius : ℕ → ℝ) : ℝ :=
  min (1 / 2) (finiteDimensionMinimum nstar hnstar radius)

def explicitSectionResolution (n nstar : ℕ) (hnstar : 0 < nstar)
    (resolution : ℕ → ℝ) (crossBound budget : ℝ) : ℝ :=
  max (n : ℝ) (max (8 * (nstar : ℝ))
    (max (finiteDimensionMaximum nstar hnstar resolution) (crossBound / budget)))

theorem explicitSectionRadius_pos {nstar : ℕ} (hnstar : 0 < nstar)
    (radius : ℕ → ℝ) (hpos : ∀ s, 0 < s → s ≤ nstar → 0 < radius s) :
    0 < explicitSectionRadius nstar hnstar radius :=
  lt_min (by norm_num) (finiteDimensionMinimum_pos hnstar radius hpos)

theorem explicitSectionRadius_lt_one {nstar : ℕ} (hnstar : 0 < nstar)
    (radius : ℕ → ℝ) : explicitSectionRadius nstar hnstar radius < 1 :=
  lt_of_le_of_lt (min_le_left _ _) (by norm_num)

theorem explicitSectionRadius_le {nstar s : ℕ} (hnstar : 0 < nstar)
    (radius : ℕ → ℝ) (hs : 0 < s) (hmax : s ≤ nstar) :
    explicitSectionRadius nstar hnstar radius ≤ radius s :=
  (min_le_right _ _).trans (finiteDimensionMinimum_le hnstar radius hs hmax)

theorem explicitSectionResolution_ge {n nstar s : ℕ} (hnstar : 0 < nstar)
    (resolution : ℕ → ℝ) (crossBound budget : ℝ) (hs : 0 < s) (hmax : s ≤ nstar) :
    resolution s ≤ explicitSectionResolution n nstar hnstar resolution crossBound budget :=
  (le_finiteDimensionMaximum hnstar resolution hs hmax).trans
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

def sectionRowConstant (d : ℕ) : ℝ := 1 + 1 / (16 * (d : ℝ))

def sectionCorrelationConstant (n : ℕ) : ℝ := 1 / (4 * (n : ℝ))

def sectionRelativeError (d n s : ℕ) : ℝ :=
  if n = 0 then (Real.sqrt (sectionRowConstant d) - 1) /
    (2 * (Real.sqrt (sectionRowConstant d) + 1 / (s : ℝ))) else
  min ((Real.sqrt (sectionRowConstant d) - 1) /
    (2 * (Real.sqrt (sectionRowConstant d) + 1 / (s : ℝ))))
    (sectionCorrelationConstant n / (16 * Real.sqrt (sectionRowConstant d)))

def sectionGridEnergyFactor (d n s : ℕ) : ℝ :=
  sectionRelativeError d n s +
    (1 + sectionRelativeError d n s / (s : ℝ)) / Real.sqrt (sectionRowConstant d)

def sectionApproximationError (d n s : ℕ) : ℝ :=
  sectionRelativeError d n s * Real.sqrt (sectionRowConstant d) /
    (1 + sectionRelativeError d n s / (s : ℝ))

def sectionPolynomialSupConstant (d n s : ℕ) : ℝ :=
  (s : ℝ) * Real.sqrt (sectionRowConstant d) /
    (1 + sectionRelativeError d n s / (s : ℝ))

def sectionGridResolution (d n s : ℕ) : ℝ :=
  (4 * ((s - 1 : ℕ) : ℝ)^2 * (s : ℝ)^2 + (sectionGridEnergyFactor d n s)^2) /
    (1 - (sectionGridEnergyFactor d n s)^2)

theorem sectionRowConstant_gt_one {d : ℕ} (hd : 1 ≤ d) :
    1 < sectionRowConstant d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  unfold sectionRowConstant
  have : 0 < 1 / (16 * (d : ℝ)) := by positivity
  linarith

theorem sectionCorrelationConstant_pos {n : ℕ} (hn : 0 < n) :
    0 < sectionCorrelationConstant n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold sectionCorrelationConstant
  positivity

theorem sectionRelativeError_row_cap (d n s : ℕ) :
    sectionRelativeError d n s ≤ (Real.sqrt (sectionRowConstant d) - 1) /
      (2 * (Real.sqrt (sectionRowConstant d) + 1 / (s : ℝ))) := by
  unfold sectionRelativeError
  split_ifs <;> first | exact le_rfl | exact min_le_left _ _

theorem sectionRelativeError_pos {d n s : ℕ} (hd : 1 ≤ d) (hs : 0 < s) :
    0 < sectionRelativeError d n s := by
  have hq := sectionRowConstant_gt_one hd
  have hroot : 1 < Real.sqrt (sectionRowConstant d) :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2 (by simpa using hq)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  unfold sectionRelativeError
  split_ifs with hn
  · exact div_pos (by linarith) (by positivity)
  · have hκ := sectionCorrelationConstant_pos (show 0 < n by omega)
    exact lt_min (div_pos (by linarith) (by positivity)) (by positivity)

theorem sectionGridEnergyFactor_bounds {d n s : ℕ} (hd : 1 ≤ d) (hs : 0 < s) :
    0 < sectionGridEnergyFactor d n s ∧ sectionGridEnergyFactor d n s < 1 := by
  let a := Real.sqrt (sectionRowConstant d)
  let e := sectionRelativeError d n s
  have ha : 1 < a := (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2
    (by simpa using sectionRowConstant_gt_one hd)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have he : 0 < e := sectionRelativeError_pos (n := n) hd hs
  have hcap : e ≤ (a - 1) / (2 * (a + 1 / (s : ℝ))) := sectionRelativeError_row_cap d n s
  have hcap' := (le_div_iff₀ (by positivity : 0 < 2 * (a + 1 / (s : ℝ)))).1 hcap
  have hmid : 1 + e / (s : ℝ) < (1 - e) * a := by
    simp only [div_eq_mul_inv] at hcap' ⊢
    nlinarith only [hcap', ha]
  constructor
  · dsimp [sectionGridEnergyFactor]
    positivity
  · change e + (1 + e / (s : ℝ)) / a < 1
    have ht := (div_lt_iff₀ (show 0 < a by linarith)).2 hmid
    linarith only [ht]

theorem sectionGridEnergyFactor_sub_error {d n s : ℕ}
    (hd : 1 ≤ d) (hs : 0 < s) :
    0 < sectionGridEnergyFactor d n s - sectionRelativeError d n s := by
  have hq := sectionRowConstant_gt_one hd
  have he := sectionRelativeError_pos (n := n) hd hs
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  dsimp [sectionGridEnergyFactor]
  have : 0 < (1 + sectionRelativeError d n s / (s : ℝ)) /
      Real.sqrt (sectionRowConstant d) := by positivity
  linarith

theorem sectionGrid_budgets {d n s : ℕ} (hd : 1 ≤ d) (hs : 0 < s) :
    (s : ℝ) + sectionRelativeError d n s =
      Real.sqrt (sectionRowConstant d) * (s : ℝ) *
        (sectionGridEnergyFactor d n s - sectionRelativeError d n s) ∧
    1 ≤ Real.sqrt (sectionRowConstant d) *
        (sectionGridEnergyFactor d n s - sectionRelativeError d n s) ∧
    sectionRelativeError d n s = sectionApproximationError d n s *
        (sectionGridEnergyFactor d n s - sectionRelativeError d n s) ∧
    sectionPolynomialSupConstant d n s = (s : ℝ) /
        (sectionGridEnergyFactor d n s - sectionRelativeError d n s) := by
  have hq := sectionRowConstant_gt_one hd
  have hroot : 0 < Real.sqrt (sectionRowConstant d) := Real.sqrt_pos.2 (by linarith)
  have he := sectionRelativeError_pos (n := n) hd hs
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hden : 0 < (s : ℝ) + sectionRelativeError d n s := by positivity
  have hbe : sectionGridEnergyFactor d n s - sectionRelativeError d n s =
      ((s : ℝ) + sectionRelativeError d n s) / ((s : ℝ) * Real.sqrt (sectionRowConstant d)) := by
    unfold sectionGridEnergyFactor
    field_simp [hsR.ne', hroot.ne']
    ring
  rw [hbe]
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp [hsR.ne', hroot.ne']
  · have ht : Real.sqrt (sectionRowConstant d) *
        (((s : ℝ) + sectionRelativeError d n s) / ((s : ℝ) * Real.sqrt (sectionRowConstant d))) =
        1 + sectionRelativeError d n s / (s : ℝ) := by
      field_simp [hsR.ne', hroot.ne']
    rw [ht]
    exact le_add_of_nonneg_right (by positivity)
  · unfold sectionApproximationError
    field_simp [hsR.ne', hroot.ne', hden.ne']
  · unfold sectionPolynomialSupConstant
    field_simp [hsR.ne', hroot.ne', hden.ne']

theorem sectionApproximationError_bounds {d n s : ℕ} (hd : 1 ≤ d) (hn : 0 < n) (hs : 0 < s) :
    0 < sectionApproximationError d n s ∧
      sectionApproximationError d n s ≤ sectionCorrelationConstant n / 16 := by
  have hq := sectionRowConstant_gt_one hd
  have hroot : 0 < Real.sqrt (sectionRowConstant d) := Real.sqrt_pos.2 (by linarith)
  have he := sectionRelativeError_pos (n := n) hd hs
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · unfold sectionApproximationError
    positivity
  · have hcap : sectionRelativeError d n s ≤ sectionCorrelationConstant n /
        (16 * Real.sqrt (sectionRowConstant d)) := by
      simp only [sectionRelativeError, if_neg (show n ≠ 0 by omega)]
      exact min_le_right _ _
    have hcap' := (le_div_iff₀ (by positivity : 0 < 16 * Real.sqrt (sectionRowConstant d))).1 hcap
    have hdiv : sectionApproximationError d n s ≤
        sectionRelativeError d n s * Real.sqrt (sectionRowConstant d) := by
      exact div_le_self (by positivity) (le_add_of_nonneg_right (by positivity))
    nlinarith only [hcap', hdiv]

def sectionJetRadius (d n s : ℕ) : ℝ :=
  min (1 / (2 * (s : ℝ)))
    (sectionRelativeError d n s * (s.factorial : ℝ) /
      (2 * ((s : ℝ) + 1) * jetCoefficientEnergyConstant s))

theorem sectionJetRadius_pos {d n s : ℕ} (hd : 1 ≤ d) (hs : 0 < s) :
    0 < sectionJetRadius d n s := by
  have he := sectionRelativeError_pos (n := n) hd hs
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hJ := jetCoefficientEnergyConstant_pos hs
  have hfac : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  unfold sectionJetRadius
  positivity

theorem sectionJetRadius_le_half (d n s : ℕ) :
    sectionJetRadius d n s ≤ 1 / (2 * (s : ℝ)) := min_le_left _ _

theorem section_signal_error {d n s : ℕ} (hd : 1 ≤ d) (hs : 0 < s)
    (frequency a : Fin s → ℂ) (hfrequency : ‖frequency‖ ≤ sectionJetRadius d n s)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖SmallFrequencyEvaluationBounds.evolutionSignal hs frequency a t - jetPolynomialSignal a t‖ ≤
      sectionRelativeError d n s *
        Real.sqrt (∫ x in (0 : ℝ)..1, ‖jetPolynomialSignal a x‖^2) := by
  have hr := sectionJetRadius_pos (n := n) hd hs
  have hJ := jetCoefficientEnergyConstant_pos hs
  have hfac : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  have hcoeff := jetPolynomial_coefficient_norm_le_energy_explicit hs a
  have hrad : sectionJetRadius d n s ≤ sectionRelativeError d n s * (s.factorial : ℝ) /
      (2 * ((s : ℝ) + 1) * jetCoefficientEnergyConstant s) := min_le_right _ _
  have hrad' := (le_div_iff₀ (by positivity :
    0 < 2 * ((s : ℝ) + 1) * jetCoefficientEnergyConstant s)).1 hrad
  have hbudget : (2 * ((s : ℝ) + 1) * sectionJetRadius d n s / (s.factorial : ℝ)) *
      jetCoefficientEnergyConstant s ≤ sectionRelativeError d n s := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hfac).2
    nlinarith only [hrad']
  have herr := QuantitativeCompanionBounds.companion_signal_error_bound hs frequency a
    hr.le (sectionJetRadius_le_half d n s) hfrequency t ht
  change ‖SmallFrequencyEvaluationBounds.evolutionSignal hs frequency a t - jetPolynomialSignal a t‖ ≤ _ at herr
  calc
    _ ≤ (2 * ((s : ℝ) + 1) * sectionJetRadius d n s / (s.factorial : ℝ)) * ‖a‖ := herr
    _ ≤ (2 * ((s : ℝ) + 1) * sectionJetRadius d n s / (s.factorial : ℝ)) *
        (jetCoefficientEnergyConstant s * Real.sqrt (∫ x in (0 : ℝ)..1, ‖jetPolynomialSignal a x‖^2)) := by
      gcongr
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hbudget (Real.sqrt_nonneg _)

def quantitativeClumpRadius (d n nstar : ℕ) (hnstar : 0 < nstar) : ℝ :=
  explicitSectionRadius nstar hnstar (sectionJetRadius d n)

def maximumApproximationError (d n nstar : ℕ) (hnstar : 0 < nstar) : ℝ :=
  finiteDimensionMaximum nstar hnstar (sectionApproximationError d n)

def maximumPolynomialSupConstant (d n nstar : ℕ) (hnstar : 0 < nstar) : ℝ :=
  finiteDimensionMaximum nstar hnstar (sectionPolynomialSupConstant d n)

def sectionCrossBudget (d n nstar : ℕ) (hnstar : 0 < nstar) : ℝ :=
  sectionCorrelationConstant n - 2 * maximumApproximationError d n nstar hnstar -
    (maximumApproximationError d n nstar hnstar)^2

def sectionPolynomialEnergyConstant (d n s : ℕ) : ℝ :=
  1 / (sectionGridEnergyFactor d n s - sectionRelativeError d n s)

def maximumPolynomialEnergyConstant (d n nstar : ℕ) (hnstar : 0 < nstar) : ℝ :=
  finiteDimensionMaximum nstar hnstar (sectionPolynomialEnergyConstant d n)

def sectionCrossNumerator (d n nstar : ℕ) (hnstar : 0 < nstar) : ℝ :=
  Real.pi * ((nstar : ℝ)^2 + (nstar : ℝ) * Real.sqrt ((nstar : ℝ)^2 - 1)) *
    (maximumPolynomialEnergyConstant d n nstar hnstar)^2

def quantitativeClumpResolution (d n nstar : ℕ) (hnstar : 0 < nstar) : ℝ :=
  explicitSectionResolution n nstar hnstar (sectionGridResolution d (n - nstar))
    (if n = nstar then 0 else sectionCrossNumerator d (n - nstar) nstar hnstar)
    (if n = nstar then 1 else sectionCrossBudget d (n - nstar) nstar hnstar)

theorem quantitativeClumpRadius_pos {d n nstar : ℕ} (hd : 1 ≤ d) (hnstar : 0 < nstar) :
    0 < quantitativeClumpRadius d n nstar hnstar :=
  explicitSectionRadius_pos hnstar _ (fun _ hs _ => sectionJetRadius_pos hd hs)

theorem maximumApproximationError_bounds {d n nstar : ℕ} (hd : 1 ≤ d) (hn : 0 < n)
    (hnstar : 0 < nstar) :
    0 ≤ maximumApproximationError d n nstar hnstar ∧
      maximumApproximationError d n nstar hnstar ≤ sectionCorrelationConstant n / 16 := by
  constructor
  · exact (sectionApproximationError_bounds hd hn (show 0 < 1 by omega)).1.le.trans
      (le_finiteDimensionMaximum hnstar _ (by omega) hnstar)
  · unfold maximumApproximationError finiteDimensionMaximum
    apply (Finset.sup'_le_iff _ _).2
    intro i _
    exact (sectionApproximationError_bounds hd hn (show 0 < i.val + 1 by omega)).2

theorem sectionCrossBudget_pos {d n nstar : ℕ} (hd : 1 ≤ d) (hn : 0 < n)
    (hnstar : 0 < nstar) : 0 < sectionCrossBudget d n nstar hnstar := by
  have hκ := sectionCorrelationConstant_pos hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hκ1 : sectionCorrelationConstant n ≤ 1 / 4 := by
    unfold sectionCorrelationConstant
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  obtain ⟨hD0, hD⟩ := maximumApproximationError_bounds hd hn hnstar
  unfold sectionCrossBudget
  nlinarith only [hκ, hκ1, hD0, hD, sq_nonneg (maximumApproximationError d n nstar hnstar)]

theorem quantitativeClumpResolution_ge_grid {d n nstar s : ℕ}
    (hnstar : 0 < nstar) (hs : 0 < s) (hmax : s ≤ nstar) :
    sectionGridResolution d (n - nstar) s ≤ quantitativeClumpResolution d n nstar hnstar :=
  explicitSectionResolution_ge hnstar _ _ _ hs hmax

theorem quantitativeClumpResolution_ge_total {d n nstar : ℕ} (hnstar : 0 < nstar) :
    (n : ℝ) ≤ quantitativeClumpResolution d n nstar hnstar := le_max_left _ _

theorem quantitativeClumpResolution_ge_spectral {d n nstar : ℕ} (hnstar : 0 < nstar) :
    8 * (nstar : ℝ) ≤ quantitativeClumpResolution d n nstar hnstar :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem unitGrid_sqrt_energy_le {M : ℕ} (hM : 0 < M) (p f : ℝ → ℂ)
    {E e b : ℝ} (hE : 0 ≤ E) (he : 0 ≤ e) (hb : 0 ≤ b) (hbe : 0 < b - e)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t - p t‖ ≤ e * Real.sqrt E)
    (hgrid : b^2 * (M + 1 : ℝ) * E ≤ ‖unitGridVector M p‖^2) :
    Real.sqrt E ≤ ‖unitGridVector M f‖ /
      (Real.sqrt (M + 1 : ℝ) * (b - e)) := by
  have hN : 0 < (M + 1 : ℝ) := by positivity
  have hNs : 0 < Real.sqrt (M + 1 : ℝ) := Real.sqrt_pos.2 hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hunit (k : Fin (M + 1)) : (k.val : ℝ) / M ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hMR).2 (by exact_mod_cast (show k.val ≤ M by omega))⟩
  have hP : b * Real.sqrt (M + 1 : ℝ) * Real.sqrt E ≤ ‖unitGridVector M p‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).1
    simpa only [mul_pow, Real.sq_sqrt hN.le, Real.sq_sqrt hE] using hgrid
  have herror : ‖unitGridVector M f - unitGridVector M p‖ ≤
      Real.sqrt (M + 1 : ℝ) * (e * Real.sqrt E) := by
    apply norm_le_sqrt_card_mul _ _ (by positivity)
    intro k
    exact hclose _ (hunit k)
  have htriangle : ‖unitGridVector M p‖ ≤
      ‖unitGridVector M f‖ + ‖unitGridVector M f - unitGridVector M p‖ := by
    simpa [add_comm, norm_sub_rev] using
      norm_add_le (unitGridVector M f) (unitGridVector M p - unitGridVector M f)
  apply (le_div_iff₀ (mul_pos hNs hbe)).2
  nlinarith only [hP, herror, htriangle]

theorem sectionRowConstant_pow_le {d : ℕ} (hd : 1 ≤ d) :
    (sectionRowConstant d)^d ≤ (16 / 15 : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let y : ℝ := 1 - 1 / (16 * (d : ℝ) + 1)
  have hden : 0 < 16 * (d : ℝ) + 1 := by positivity
  have hr : (d : ℝ) / (16 * (d : ℝ) + 1) ≤ 1 / 16 := by
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 16)).2
    linarith
  have hb := one_add_mul_le_pow (a := -(1 / (16 * (d : ℝ) + 1))) (by
    have : 1 / (16 * (d : ℝ) + 1) ≤ (1 : ℝ) := (div_le_one hden).2 (by linarith)
    linarith) d
  have hylower : (15 / 16 : ℝ) ≤ y^d := by
    dsimp [y]
    have he : (d : ℝ) * -(1 / (16 * (d : ℝ) + 1)) = -(d / (16 * (d : ℝ) + 1)) := by ring
    rw [he] at hb
    simp only [← sub_eq_add_neg] at hb
    linarith only [hb, hr]
  have hx : 0 ≤ sectionRowConstant d := le_trans (by norm_num) (sectionRowConstant_gt_one hd).le
  have hxy : sectionRowConstant d * y = 1 := by
    dsimp [sectionRowConstant, y]
    field_simp
    ring
  have hprod : (sectionRowConstant d)^d * y^d = 1 := by rw [← mul_pow, hxy, one_pow]
  have h := mul_le_mul_of_nonneg_left hylower (pow_nonneg hx d)
  nlinarith only [h, hprod]

theorem sectionRowConstant_leverage_le {d : ℕ} (hd : 1 ≤ d) :
    (sectionRowConstant d)^d / (3 / 4 : ℝ) ≤ 3 / 2 := by
  have h := sectionRowConstant_pow_le hd
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 4)).2
  linarith

def quantitativeClumpBandwidth (d n nstar : ℕ) (hnstar : 0 < nstar) : ℝ :=
  max (n : ℝ) (max (16 * (nstar : ℝ))
    (finiteDimensionMaximum nstar hnstar (sectionGridResolution d (n - nstar))))

def quantitativeClumpPairSeparation (d n nstar : ℕ) (hnstar : 0 < nstar) : ℝ :=
  if n = nstar then 0 else sectionCrossNumerator d (n - nstar) nstar hnstar /
    sectionCrossBudget d (n - nstar) nstar hnstar

theorem quantitativeClumpBandwidth_ge_grid {d n nstar s : ℕ}
    (hnstar : 0 < nstar) (hs : 0 < s) (hmax : s ≤ nstar) :
    sectionGridResolution d (n - nstar) s ≤ quantitativeClumpBandwidth d n nstar hnstar :=
  (le_finiteDimensionMaximum hnstar _ hs hmax).trans
    ((le_max_right _ _).trans (le_max_right _ _))

theorem quantitativeClumpBandwidth_ge_total {d n nstar : ℕ} (hnstar : 0 < nstar) :
    (n : ℝ) ≤ quantitativeClumpBandwidth d n nstar hnstar := le_max_left _ _

theorem quantitativeClumpBandwidth_ge_spectral {d n nstar : ℕ} (hnstar : 0 < nstar) :
    16 * (nstar : ℝ) ≤ quantitativeClumpBandwidth d n nstar hnstar :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem sectionPolynomialEnergyConstant_pos {d n s : ℕ} (hd : 1 ≤ d) (hs : 0 < s) :
    0 < sectionPolynomialEnergyConstant d n s :=
  div_pos (by norm_num) (sectionGridEnergyFactor_sub_error hd hs)

theorem maximumPolynomialEnergyConstant_pos {d n nstar : ℕ} (hd : 1 ≤ d)
    (hnstar : 0 < nstar) : 0 < maximumPolynomialEnergyConstant d n nstar hnstar :=
  (sectionPolynomialEnergyConstant_pos (n := n) hd (show 0 < 1 by omega)).trans_le
    (le_finiteDimensionMaximum hnstar _ (by omega) hnstar)

theorem sectionCrossNumerator_pos {d n nstar : ℕ} (hd : 1 ≤ d) (hnstar : 0 < nstar) :
    0 < sectionCrossNumerator d n nstar hnstar := by
  have hnstarR : (0 : ℝ) < nstar := by exact_mod_cast hnstar
  have hE := maximumPolynomialEnergyConstant_pos (n := n) hd hnstar
  unfold sectionCrossNumerator
  positivity

theorem quantitativeClumpPairSeparation_pos {d n nstar : ℕ} (hd : 1 ≤ d)
    (hnstar : 0 < nstar) (hsize : nstar < n) :
    0 < quantitativeClumpPairSeparation d n nstar hnstar := by
  have hneq : n ≠ nstar := by omega
  simp only [quantitativeClumpPairSeparation, if_neg hneq]
  exact div_pos (sectionCrossNumerator_pos hd hnstar)
    (sectionCrossBudget_pos hd (by omega) hnstar)

theorem quantitativeClumpPairSeparation_mul_budget {d n nstar : ℕ}
    (hd : 1 ≤ d) (hnstar : 0 < nstar) (hsize : nstar < n) :
    quantitativeClumpPairSeparation d n nstar hnstar *
      sectionCrossBudget d (n - nstar) nstar hnstar =
      sectionCrossNumerator d (n - nstar) nstar hnstar := by
  have hneq : n ≠ nstar := by omega
  simp only [quantitativeClumpPairSeparation, if_neg hneq]
  exact div_mul_cancel₀ _ (sectionCrossBudget_pos hd (by omega) hnstar).ne'

def quantitativeClumpGlobalMomentConstant (n nstar : ℕ) : ℝ :=
  (n : ℝ) * (nstar : ℝ) + Real.sqrt (((n - nstar + 1 : ℕ) : ℝ) * (n : ℝ) * (nstar : ℝ)^3)

def quantitativeClumpGlobalSeparation (d n nstar : ℕ) (hnstar : 0 < nstar) : ℝ :=
  if n = nstar then 0 else
    Real.pi * (maximumPolynomialEnergyConstant d (n - nstar) nstar hnstar)^2 *
      quantitativeClumpGlobalMomentConstant n nstar /
        (((n - nstar : ℕ) : ℝ) * sectionCrossBudget d (n - nstar) nstar hnstar)

def quantitativeClumpSeparation (d n nstar : ℕ) (hnstar : 0 < nstar) : ℝ :=
  min (quantitativeClumpPairSeparation d n nstar hnstar)
    (quantitativeClumpGlobalSeparation d n nstar hnstar)

theorem quantitativeClumpGlobalSeparation_pos {d n nstar : ℕ} (hd : 1 ≤ d)
    (hnstar : 0 < nstar) (hsize : nstar < n) :
    0 < quantitativeClumpGlobalSeparation d n nstar hnstar := by
  have hneq : n ≠ nstar := by omega
  have hhR : (0 : ℝ) < (n - nstar : ℕ) := by exact_mod_cast (show 0 < n - nstar by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hstarR : (0 : ℝ) < nstar := by exact_mod_cast hnstar
  have hH := maximumPolynomialEnergyConstant_pos (n := n - nstar) hd hnstar
  have hg := sectionCrossBudget_pos hd (show 0 < n - nstar by omega) hnstar
  simp only [quantitativeClumpGlobalSeparation, if_neg hneq]
  unfold quantitativeClumpGlobalMomentConstant
  positivity

theorem quantitativeClumpSeparation_pos {d n nstar : ℕ} (hd : 1 ≤ d)
    (hnstar : 0 < nstar) (hsize : nstar < n) :
    0 < quantitativeClumpSeparation d n nstar hnstar :=
  lt_min (quantitativeClumpPairSeparation_pos hd hnstar hsize)
    (quantitativeClumpGlobalSeparation_pos hd hnstar hsize)

theorem quantitativeClumpGlobalSeparation_budget {d n nstar : ℕ}
    (hd : 1 ≤ d) (hnstar : 0 < nstar) (hsize : nstar < n) :
    (Real.pi * (maximumPolynomialEnergyConstant d (n - nstar) nstar hnstar)^2 /
        quantitativeClumpGlobalSeparation d n nstar hnstar) *
        quantitativeClumpGlobalMomentConstant n nstar +
      (2 * maximumApproximationError d (n - nstar) nstar hnstar +
        (maximumApproximationError d (n - nstar) nstar hnstar)^2) * ((n - nstar : ℕ) : ℝ) = 1 / 4 := by
  have hneq : n ≠ nstar := by omega
  have hh : 0 < n - nstar := by omega
  have hhR : (0 : ℝ) < (n - nstar : ℕ) := by exact_mod_cast hh
  have hH := maximumPolynomialEnergyConstant_pos (n := n - nstar) hd hnstar
  have hg := sectionCrossBudget_pos hd hh hnstar
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hstarR : (0 : ℝ) < nstar := by exact_mod_cast hnstar
  have hG : 0 < quantitativeClumpGlobalMomentConstant n nstar := by
    unfold quantitativeClumpGlobalMomentConstant
    positivity
  have he : sectionCorrelationConstant (n - nstar) * ((n - nstar : ℕ) : ℝ) = 1 / 4 := by
    unfold sectionCorrelationConstant
    field_simp
  simp only [quantitativeClumpGlobalSeparation, if_neg hneq]
  field_simp [hH.ne', hg.ne', hG.ne', Real.pi_ne_zero]
  unfold sectionCrossBudget at *
  nlinarith only [he]

/-- The auxiliary cap in the definition is redundant: every local radius
already lies below one half. -/
theorem quantitativeClumpRadius_eq_finiteMinimum {d n nstar : ℕ} (hnstar : 0 < nstar) :
    quantitativeClumpRadius d n nstar hnstar =
      finiteDimensionMinimum nstar hnstar (sectionJetRadius d n) := by
  unfold quantitativeClumpRadius explicitSectionRadius
  apply min_eq_right
  exact (finiteDimensionMinimum_le hnstar _ (show 0 < 1 by omega) hnstar).trans
    (by simpa using sectionJetRadius_le_half d n 1)

end
end LeanNumDetect.QuantitativeClumpSectionBounds
