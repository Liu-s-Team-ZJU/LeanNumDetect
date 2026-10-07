import General.Fourier.SmallFrequencyEvaluationBounds
import RandSamp.RandomModel
import RandSamp.ClumpSubspaceGeometry
import Mathlib.Tactic

/-!
# Single-clump leverage on consecutive integer rows

The row estimate is proved through small-frequency companion evolution and
polynomial evaluation bounds. No external theorem or internal frequency gap
is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set MeasureTheory

namespace LeanNumDetect.RandSamp
open ExponentialSumEstimates SmallFrequencyEvaluationBounds
noncomputable section

/-- A sufficient scaled clump radius, depending only on its cardinality. -/
def singleClumpRadius (s : ℕ) : ℝ :=
  if hs : 0 < s then
    Classical.choose (smallFrequency_exponentialSum_grid_bounds hs)
  else 1

/-- Sufficient grid resolution, chosen with the same frequency radius. -/
def singleClumpGridThreshold (s : ℕ) : ℝ :=
  if hs : 0 < s then
    Classical.choose (Classical.choose_spec (smallFrequency_exponentialSum_grid_bounds hs))
  else 1

theorem singleClumpRadius_pos (s : ℕ) : 0 < singleClumpRadius s := by
  by_cases hs : 0 < s
  · simp only [singleClumpRadius, dif_pos hs]
    exact (Classical.choose_spec (Classical.choose_spec
      (smallFrequency_exponentialSum_grid_bounds hs))).1
  · simp [singleClumpRadius, hs]

theorem singleClumpRadius_le_one (s : ℕ) : singleClumpRadius s ≤ 1 := by
  by_cases hs : 0 < s
  · simp only [singleClumpRadius, dif_pos hs]
    exact (Classical.choose_spec (Classical.choose_spec
      (smallFrequency_exponentialSum_grid_bounds hs))).2.1
  · simp [singleClumpRadius, hs]

theorem singleClumpGridThreshold_pos (s : ℕ) : 0 < singleClumpGridThreshold s := by
  by_cases hs : 0 < s
  · simp only [singleClumpGridThreshold, dif_pos hs]
    exact (Classical.choose_spec (Classical.choose_spec
      (smallFrequency_exponentialSum_grid_bounds hs))).2.2.1
  · simp [singleClumpGridThreshold, hs]

/-- The deterministic row bound for a sufficiently resolved unit grid.
The absolute row constant is `512`; the permitted bandwidth and resolution
threshold depend only on cardinality. -/
theorem exponentialSum_grid_row_bound {s M : ℕ} (hs : 0 < s) (hM : 0 < M)
    (frequency : Fin s → ℝ) (coefficient : Fin s → ℂ)
    (hfrequency : ∀ j, |frequency j| ≤ singleClumpRadius s)
    (hsize : singleClumpGridThreshold s ≤ (M : ℝ))
    {k : ℕ} (hk : k ≤ M) :
    ((M : ℝ) + 1) * ‖exponentialSum frequency coefficient ((k : ℝ) / M)‖^2 ≤
      512 * (s : ℝ)^2 * ∑ l ∈ Finset.range (M + 1),
        ‖exponentialSum frequency coefficient ((l : ℝ) / M)‖^2 := by
  have h := (Classical.choose_spec (Classical.choose_spec
    (smallFrequency_exponentialSum_grid_bounds hs))).2.2.2
  have hfrequency' := hfrequency
  have hsize' := hsize
  simp only [singleClumpRadius, dif_pos hs] at hfrequency'
  simp only [singleClumpGridThreshold, dif_pos hs] at hsize'
  exact h frequency coefficient M hfrequency' hM hsize' k hk

/-- Shifting a real cluster to its center and rescaling the time interval
preserves each integer-row energy. The removed center is a unit phase. -/
theorem centeredExponentialSum_grid_energy {s M : ℕ} (hM : 0 < M)
    (node : Fin s → ℝ) (coefficient : Fin s → ℂ) (center : ℝ) (k : ℕ) :
    ‖exponentialSum (fun j => (M : ℝ) * (node j - center)) coefficient
      ((k : ℝ) / M)‖ ^ 2 = fourierRowEnergy node k coefficient := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  let phase := Complex.exp (Complex.I * (((k : ℝ) * center : ℝ) : ℂ))
  have hphase : ‖phase‖ = 1 := by
    simpa [phase, mul_comm] using Complex.norm_exp_ofReal_mul_I ((k : ℝ) * center)
  have heq : phase * exponentialSum (fun j => (M : ℝ) * (node j - center))
      coefficient ((k : ℝ) / M) = ∑ j, fourierRow node k j * coefficient j := by
    unfold exponentialSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change phase * (coefficient j *
      Complex.exp (Complex.I * (((k : ℝ) / M * ((M : ℝ) * (node j - center)) : ℝ) : ℂ))) = _
    calc
      _ = coefficient j * (phase *
          Complex.exp (Complex.I * (((k : ℝ) / M * ((M : ℝ) * (node j - center)) : ℝ) : ℂ))) := by ring
      _ = coefficient j * Complex.exp
          (Complex.I * (((k : ℝ) * center : ℝ) : ℂ) +
           Complex.I * (((k : ℝ) / M * ((M : ℝ) * (node j - center)) : ℝ) : ℂ)) := by
        rw [Complex.exp_add]
      _ = coefficient j * fourierRow node k j := by
        unfold fourierRow
        congr 2
        have hscaled : (k : ℝ) / M * ((M : ℝ) * (node j - center)) =
            (k : ℝ) * (node j - center) := by field_simp [hM0]
        rw [hscaled]
        push_cast
        ring
      _ = _ := by ring
  have hnorm := congrArg (fun z : ℂ => ‖z‖ ^ 2) heq
  simpa only [norm_mul, hphase, one_mul, fourierRowEnergy] using hnorm

/-- A real clump contained in the chosen radius divided by `M` satisfies the integer-row
leverage estimate, uniformly over all coefficients and internal gaps. -/
theorem singleClump_integer_row_bound {s M : ℕ} (hs : 0 < s) (hM : 0 < M)
    (node : Fin s → ℝ) (coefficient : Fin s → ℂ) (center : ℝ)
    (hclump : ∀ j, |(M : ℝ) * (node j - center)| ≤ singleClumpRadius s)
    (hsize : singleClumpGridThreshold s ≤ (M : ℝ)) {k : ℕ} (hk : k ≤ M) :
    ((M : ℝ) + 1) * fourierRowEnergy node k coefficient ≤
      512 * (s : ℝ) ^ 2 *
        ∑ l ∈ Finset.range (M + 1), fourierRowEnergy node l coefficient := by
  have h := exponentialSum_grid_row_bound hs hM
    (fun j => (M : ℝ) * (node j - center)) coefficient hclump hsize hk
  simpa only [centeredExponentialSum_grid_energy hM node coefficient center] using h

/-- Integer frequencies make a full winding of each source invisible. -/
theorem fourierRow_sub_winding {s : ℕ} (node : Fin s → ℝ) (p : Fin s → ℤ)
    (k : ℕ) (j : Fin s) :
    fourierRow (fun i => node i - 2 * Real.pi * p i) k j = fourierRow node k j := by
  unfold fourierRow
  have he : Complex.I * (((k : ℝ) * (node j - 2 * Real.pi * p j) : ℝ) : ℂ) =
      Complex.I * (((k : ℝ) * node j : ℝ) : ℂ) +
        (((-(k : ℤ) * p j : ℤ) : ℂ)) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem fourierRowEnergy_sub_winding {s : ℕ} (node : Fin s → ℝ)
    (p : Fin s → ℤ) (coefficient : Fin s → ℂ) (k : ℕ) :
    fourierRowEnergy (fun i => node i - 2 * Real.pi * p i) k coefficient =
      fourierRowEnergy node k coefficient := by
  simp only [fourierRowEnergy, fourierRow_sub_winding]

/-- The same row bound for actual torus nodes, without choosing a preferred
real lift in the hypotheses. Short clumps can always be lifted to a real
interval of the same diameter. -/
theorem singleClump_circular_row_bound {s M : ℕ} (hs : 0 < s) (hM : 0 < M)
    (node : Fin s → ℝ) (coefficient : Fin s → ℂ)
    {c0 : ℝ} (hc0 : 0 ≤ c0) (hc0radius : c0 ≤ singleClumpRadius s)
    (hclump : ∀ i j, angularTorusDistance (node i) (node j) ≤ c0 / (M : ℝ))
    (hsize : singleClumpGridThreshold s ≤ (M : ℝ)) {k : ℕ} (hk : k ≤ M) :
    fourierRowEnergy node k coefficient ≤
      (512 * (s : ℝ) ^ 2 / ((M : ℝ) + 1)) *
        ∑ l ∈ Finset.range (M + 1), fourierRowEnergy node l coefficient := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hc0one : c0 ≤ 1 := hc0radius.trans (singleClumpRadius_le_one s)
  have hw : 0 ≤ c0 / (M : ℝ) := div_nonneg hc0 hMR.le
  have hwone : c0 / (M : ℝ) ≤ 1 := (div_le_one hMR).2 (hc0one.trans hMone)
  have hshort : 3 * (c0 / (M : ℝ)) < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  obtain ⟨p, hdiam⟩ := angular_short_clump_lift hs node hw hshort hclump
  let X : Fin s → ℝ := fun j => node j - 2 * Real.pi * p j
  let i₀ : Fin s := ⟨0, hs⟩
  have hbound : ∀ j, |(M : ℝ) * (X j - X i₀)| ≤ singleClumpRadius s := by
    intro j
    have hd := Metric.dist_le_diam_of_mem (Set.finite_range X).isBounded
      (Set.mem_range_self j) (Set.mem_range_self i₀)
    have hd' : |X j - X i₀| ≤ c0 / (M : ℝ) := by
      have hdd : |X j - X i₀| ≤ Metric.diam (Set.range X) := by
        simpa only [Real.dist_eq] using hd
      exact hdd.trans hdiam
    rw [abs_mul, abs_of_pos hMR]
    have hm := mul_le_mul_of_nonneg_left hd' hMR.le
    rw [mul_div_cancel₀ _ hMR.ne'] at hm
    exact hm.trans hc0radius
  have h := singleClump_integer_row_bound hs hM X coefficient (X i₀) hbound hsize hk
  have he (l : ℕ) : fourierRowEnergy X l coefficient = fourierRowEnergy node l coefficient :=
    fourierRowEnergy_sub_winding node p coefficient l
  simp only [he] at h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) + 1)).2
  nlinarith

end
end LeanNumDetect.RandSamp
