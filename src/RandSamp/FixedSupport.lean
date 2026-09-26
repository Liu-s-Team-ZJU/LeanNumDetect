import RandSamp.RandomGram
import RandSamp.SingularValues
import RandSamp.SamplingRate
import General.Probability.MatrixChernoffBounds
import General.Probability.UniformCounting

/-! Fixed-support singular-value concentration, corresponding to
`lem:fixed-support-singular-values` in the RandSamp manuscript. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open WithLp

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The full, normalized Gram matrix for frequencies `0,...,M`. -/
def fullGram {s : ℕ} (M : ℕ) (Y : Fin s → ℝ) : Matrix (Fin s) (Fin s) ℂ :=
  mean (fourierPopulation (N := M + 1) Y)

/-- The singular-value event in the fixed-support lemma. The node tuple is a
fixed parameter, outside the probability space of frequency subsets. -/
def SingularValueEvent {N s m : ℕ} (Y : Fin s → ℝ) (a b δ : ℝ)
    (Ω : Sample N m) : Prop :=
  Real.sqrt ((1 - δ) * a) ≤ matrixSingularValue (sampledVandermonde m Y Ω.val) (s - 1) ∧
    matrixSingularValue (sampledVandermonde m Y Ω.val) (s - 1) ≤
      matrixSingularValue (sampledVandermonde m Y Ω.val) 0 ∧
    matrixSingularValue (sampledVandermonde m Y Ω.val) 0 ≤ Real.sqrt ((1 + δ) * b)

theorem singularValueEvent_of_sampleMean_bounds {N s m : ℕ} (hs : 0 < s)
    (Y : Fin s → ℝ) {a b δ : ℝ} (ha : 0 ≤ a) (hδ : δ ≤ 1)
    (Ω : Sample N m)
    (hbound : ∀ z : EuclideanSpace ℂ (Fin s),
      (1 - δ) * a * ‖z‖ ^ 2 ≤ FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z ∧
        FiniteMatrixSampling.quadratic (sampleMean (fourierPopulation Y) Ω) z ≤ (1 + δ) * b * ‖z‖ ^ 2) :
    SingularValueEvent Y a b δ Ω := by
  apply matrixSingularValue_bounds_of_norm_sq_bounds _ hs (mul_nonneg (sub_nonneg.mpr hδ) ha)
  intro z
  simpa only [quadratic_fourier_sampleMean] using hbound z

/-- Manuscript `lem:fixed-support-singular-values`. The full-Gram hypothesis is
written in quadratic-form order. The probability is uniform on the finite type
of all `m`-element subsets of `Fin (M+1)`, not on independent repeated draws. -/
theorem fixedSupport_singularValues {M s m : ℕ}
    (_hM : 1 ≤ M) (hs : 0 < s) (hm : 1 ≤ m) (hmM : m ≤ M + 1)
    (Y : Fin s → ℝ) {a b δ η : ℝ}
    (ha : 0 < a) (_hab : a ≤ b) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hη0 : 0 < η) (_hη1 : η < 1)
    (hgram : ∀ z : EuclideanSpace ℂ (Fin s),
      a * ‖z‖ ^ 2 ≤ FiniteMatrixSampling.quadratic (fullGram M Y) z ∧
        FiniteMatrixSampling.quadratic (fullGram M Y) z ≤ b * ‖z‖ ^ 2)
    (hsample : 3 * (s : ℝ) / (a * δ ^ 2) * Real.log (2 * s / η) ≤ m) :
    1 - η ≤ probability (fun Ω : Sample (M + 1) m => SingularValueEvent Y a b δ Ω) := by
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hprob := sampleMean_bounds_probability (by omega : 0 < M + 1) hs hm hmM
    (fourierPopulation Y) hsr ha hδ0 hδ1
    (fun k => fourierRowGram_posSemidef Y k.val)
    (fun k z => (fourierPopulation_bound Y k z).2) hgram
  have htail := fourier_chernoff_failure_bound_of_sample_size
    (Nat.cast_nonneg m) hsr ha (le_refl a) hδ0 hη0 hsample
  apply (sub_le_sub_left htail 1).trans (hprob.trans _)
  apply probability_mono
  intro Ω hΩ
  exact singularValueEvent_of_sampleMean_bounds hs Y ha.le hδ1.le Ω hΩ

end

end LeanNumDetect.RandSamp
