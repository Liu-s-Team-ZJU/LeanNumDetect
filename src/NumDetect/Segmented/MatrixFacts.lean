import NumDetect.Preliminaries.MatrixFacts
import NumDetect.Segmented.MatrixDefinitions

/-! Fourier factorization and amplitude facts for segmented GHMs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Exact segmented-grid factorization, including the manuscript's phase shift. -/
theorem segmentedMeasurementMatrix_fourier_eq_noiseless
    {d n : ℕ} (m r D : ℕ) (μ : AtomicMeasure d n) :
    segmentedMeasurementMatrix m r D (fourier μ) =
      segmentedNoiselessMatrix m r D μ := by
  classical
  ext α β
  rw [segmentedNoiselessMatrix, Matrix.mul_assoc]
  simp only [segmentedMeasurementMatrix,
    segmentedVandermonde, segmentedColumnVandermonde, generalizedVandermonde,
    steeringVector, fourier, segmentedPhaseAmplitude, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.transpose_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hphase :
      dot (μ.node j) (fun k =>
          segmentedFrequency d m r D α k + segmentedFrequency d m r D β k -
            segmentedCutoff m r D) =
        dot (μ.node j) (segmentedFrequency d m r D α) +
        dot (μ.node j) (segmentedFrequency d m r D β) -
        (segmentedCutoff m r D : ℝ) * ∑ k, μ.node j k := by
    simp only [dot]
    calc
      _ = ∑ k, (μ.node j k * segmentedFrequency d m r D α k +
          μ.node j k * segmentedFrequency d m r D β k -
          (segmentedCutoff m r D : ℝ) * μ.node j k) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hphase, Complex.ofReal_sub, Complex.ofReal_add]
  rw [show Complex.I *
      ((dot (μ.node j) (segmentedFrequency d m r D α) : ℂ) +
        dot (μ.node j) (segmentedFrequency d m r D β) -
        ((segmentedCutoff m r D : ℝ) * ∑ k, μ.node j k : ℝ)) =
      Complex.I * (dot (μ.node j) (segmentedFrequency d m r D α) : ℂ) +
        (-Complex.I *
          ((segmentedCutoff m r D : ℝ) * ∑ k, μ.node j k : ℝ)) +
        Complex.I * (dot (μ.node j) (segmentedFrequency d m r D β) : ℂ) by
        push_cast
        ring]
  rw [Complex.exp_add, Complex.exp_add]
  rw [dot_comm (μ.node j) (segmentedFrequency d m r D α),
    dot_comm (μ.node j) (segmentedFrequency d m r D β)]
  ring

/-- The phase-shifted amplitudes in the segmented factorization preserve moduli. -/
theorem norm_segmentedPhaseAmplitude {d n : ℕ} (m r D : ℕ)
    (μ : AtomicMeasure d n) (j : Fin n) :
    ‖segmentedPhaseAmplitude m r D μ j‖ = ‖μ.amplitude j‖ := by
  rw [segmentedPhaseAmplitude, norm_mul, Complex.norm_exp]
  simp

theorem minAmplitude_le_norm_segmentedPhaseAmplitude
    {d n : ℕ} (m r D : ℕ) (μ : AtomicMeasure d n) (hn : 0 < n) (j : Fin n) :
    minAmplitude μ hn ≤ ‖segmentedPhaseAmplitude m r D μ j‖ := by
  rw [norm_segmentedPhaseAmplitude]
  exact minAmplitude_le μ hn j

end

end NumDetect
end LeanNumDetect
