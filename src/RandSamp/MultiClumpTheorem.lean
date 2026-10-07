import RandSamp.MultiClumpSampling
import RandSamp.MultidimensionalMultiClumpTheorem

/-!
# The exact one-dimensional multiclump theorem as a cube specialization

All original statement definitions, quantifier order, angular geometry, and
sampling constant `3072` are preserved. The three public main theorems below
are direct dimension-one corollaries of the multidimensional result. Cube
frequencies, actual sampled subsets, Gram matrices, and ordered singular
values are transported by the proved dimension-one bijection.
-/

set_option autoImplicit false

namespace LeanNumDetect.RandSamp
noncomputable section

/-- Geometry supplies the original row radius and spectral scaling as the
exact dimension-one specialization of the cube deterministic theorem. -/
theorem multiClump_deterministic_control (n nstar : ℕ)
    (hnstar : 2 ≤ nstar) (hn : nstar ≤ n) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
      MultiClumpDeterministicControl n nstar c0 C0 := by
  obtain ⟨c0, C0, hc0, hc01, hC0, hcontrol⟩ :=
    multidimensionalMultiClump_deterministic_control 1 (by norm_num) n nstar hnstar hn
  exact ⟨c0, C0, hc0, hc01, hC0,
    multiClumpDeterministicControl_of_multidimensional_one hcontrol⟩

/-- The original random-row theorem, including its absolute constant and
both smallest-singular-value exponents, follows from cube sampling at `d=1`. -/
theorem multiClump_random_row_sampling :
    ∀ (n nstar : ℕ), 2 ≤ nstar → nstar ≤ n →
      ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 < 1 ∧ (n : ℝ) ≤ C0 ∧
        MultiClumpSamplingConclusion multiClumpSamplingConstant n nstar c0 C0 := by
  intro n nstar hnstar hn
  obtain ⟨c0, C0, hc0, hc01, hC0, hsample⟩ :=
    multidimensionalMultiClump_random_row_sampling 1 (by norm_num) n nstar hnstar hn
  refine ⟨c0, C0, hc0, hc01, hC0, ?_⟩
  simpa only [multidimensionalMultiClumpSamplingConstant_one, multiClumpSamplingConstant] using
    multiClumpSamplingConclusion_of_multidimensional_one hsample

/-- The original existential-absolute-constant formulation is unchanged. -/
theorem multiClump_sampling_statement : MultiClumpSamplingStatement :=
  ⟨multiClumpSamplingConstant, multiClumpSamplingConstant_pos, multiClump_random_row_sampling⟩

end
end LeanNumDetect.RandSamp
