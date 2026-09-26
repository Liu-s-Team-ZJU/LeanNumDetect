import RandSamp.CubeRandomModel
import RandSamp.SingularValues
import RandSamp.SamplingRate

/-! The fixed-support sampling argument for a frequency cube. The probability
space consists of actual subsets of the cube, without choosing an ordering. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- Singular-value bounds for a fixed cube node tuple and a sampled subset. -/
def CubeSingularValueEvent {d M s m : ℕ} (Y : Fin s → Fin d → ℝ) (a b δ : ℝ)
    (Ω : FiniteSample (CubeFrequency d M) m) : Prop :=
  Real.sqrt ((1 - δ) * a) ≤ matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (s - 1) ∧
    matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (s - 1) ≤
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) 0 ∧
    matrixSingularValue (cubeSampledVandermonde m Y Ω.val) 0 ≤ Real.sqrt ((1 + δ) * b)

theorem cubeSingularValueEvent_of_sampleMean_bounds {d M s m : ℕ} (hs : 0 < s)
    (Y : Fin s → Fin d → ℝ) {a b δ : ℝ} (ha : 0 ≤ a) (hδ : δ ≤ 1)
    (Ω : FiniteSample (CubeFrequency d M) m)
    (hbound : ∀ z : EuclideanSpace ℂ (Fin s),
      (1 - δ) * a * ‖z‖ ^ 2 ≤
        FiniteMatrixSampling.quadratic (finiteSampleMean (cubeFourierPopulation Y) Ω) z ∧
      FiniteMatrixSampling.quadratic (finiteSampleMean (cubeFourierPopulation Y) Ω) z ≤
        (1 + δ) * b * ‖z‖ ^ 2) : CubeSingularValueEvent Y a b δ Ω := by
  apply matrixSingularValue_bounds_of_norm_sq_bounds _ hs
    (mul_nonneg (sub_nonneg.mpr hδ) ha)
  intro z
  simpa only [quadratic_cubeFourier_sampleMean] using hbound z

/-- The fixed-node-set lemma for cube frequencies. The number of rows is
`(M+1)^d`, but the dimension and row bound in the Chernoff rate remain `s`. -/
theorem cubeFixedSupport_singularValues {d M s m : ℕ} (hs : 0 < s)
    (hm : 1 ≤ m) (hmN : m ≤ (M + 1) ^ d) (Y : Fin s → Fin d → ℝ)
    {a b δ η : ℝ} (ha : 0 < a) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hη0 : 0 < η)
    (hgram : ∀ z : EuclideanSpace ℂ (Fin s),
      a * ‖z‖ ^ 2 ≤ FiniteMatrixSampling.quadratic (cubeFullGram M Y) z ∧
        FiniteMatrixSampling.quadratic (cubeFullGram M Y) z ≤ b * ‖z‖ ^ 2)
    (hsample : 3 * (s : ℝ) / (a * δ ^ 2) * Real.log (2 * s / η) ≤ m) :
    1 - η ≤ probability (fun Ω : FiniteSample (CubeFrequency d M) m =>
      CubeSingularValueEvent Y a b δ Ω) := by
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hcard : 0 < Fintype.card (CubeFrequency d M) := by
    rw [card_cubeFrequency]
    exact pow_pos (Nat.succ_pos M) d
  have hmcard : m ≤ Fintype.card (CubeFrequency d M) := by simpa using hmN
  have hprob := finiteSampleMean_bounds_probability hcard hs hm hmcard
    (cubeFourierPopulation Y) hsr ha hδ0 hδ1
    (fun k => cubeFourierRowGram_posSemidef Y k)
    (fun k z => (cubeFourierPopulation_bound Y k z).2) hgram
  have htail := fourier_chernoff_failure_bound_of_sample_size
    (Nat.cast_nonneg m) hsr ha (le_refl a) hδ0 hη0 hsample
  apply (sub_le_sub_left htail 1).trans (hprob.trans _)
  apply probability_mono
  intro Ω hΩ
  exact cubeSingularValueEvent_of_sampleMean_bounds hs Y ha.le hδ1.le Ω hΩ

end

end LeanNumDetect.RandSamp
