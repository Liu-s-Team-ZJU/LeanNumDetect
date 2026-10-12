import NumDetect.Preliminaries.MatrixFacts
import NumDetect.Uniform.MatrixDefinitions

/-! Fourier factorization and amplitude facts for uniform GHMs. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Exact contiguous-grid factorization, including the manuscript's phase shift. -/
theorem uniformMeasurementMatrix_fourier_eq_noiseless
    {d n : ℕ} (s : ℕ) (Ω : ℝ) (μ : AtomicMeasure d n) (hs : 0 < s) :
    uniformMeasurementMatrix s Ω (fourier μ) =
      uniformNoiselessMatrix s Ω μ := by
  classical
  ext α β
  rw [uniformNoiselessMatrix, Matrix.mul_assoc]
  simp only [uniformMeasurementMatrix, uniformVandermonde,
    generalizedVandermonde, steeringVector, fourier, uniformPhaseAmplitude,
    Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hphase :
      dot (μ.node j) (fun k =>
          Ω / s * ((α k : ℝ) + (β k : ℝ) - s)) =
        dot (μ.node j) (uniformFrequency d s Ω α) +
        dot (μ.node j) (uniformFrequency d s Ω β) -
        Ω * ∑ k, μ.node j k := by
    simp only [dot, uniformFrequency]
    have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    calc
      _ = ∑ k, (μ.node j k * (Ω / s * (α k : ℝ)) +
          μ.node j k * (Ω / s * (β k : ℝ)) - Ω * μ.node j k) := by
        apply Finset.sum_congr rfl
        intro k _
        field_simp
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hphase, Complex.ofReal_sub, Complex.ofReal_add]
  rw [show Complex.I *
      ((dot (μ.node j) (uniformFrequency d s Ω α) : ℂ) +
        dot (μ.node j) (uniformFrequency d s Ω β) -
        (Ω * ∑ k, μ.node j k : ℝ)) =
      Complex.I * (dot (μ.node j) (uniformFrequency d s Ω α) : ℂ) +
        (-Complex.I * (Ω * ∑ k, μ.node j k : ℝ)) +
        Complex.I * (dot (μ.node j) (uniformFrequency d s Ω β) : ℂ) by
        push_cast
        ring]
  rw [Complex.exp_add, Complex.exp_add]
  rw [dot_comm (μ.node j) (uniformFrequency d s Ω α),
    dot_comm (μ.node j) (uniformFrequency d s Ω β)]
  ring

/-- The phase-shifted amplitudes in the uniform factorization preserve moduli. -/
theorem norm_uniformPhaseAmplitude {d n : ℕ} (Ω : ℝ)
    (μ : AtomicMeasure d n) (j : Fin n) :
    ‖uniformPhaseAmplitude Ω μ j‖ = ‖μ.amplitude j‖ := by
  rw [uniformPhaseAmplitude, norm_mul, Complex.norm_exp]
  simp

theorem minAmplitude_le_norm_uniformPhaseAmplitude
    {d n : ℕ} (Ω : ℝ) (μ : AtomicMeasure d n) (hn : 0 < n) (j : Fin n) :
    minAmplitude μ hn ≤ ‖uniformPhaseAmplitude Ω μ j‖ := by
  rw [norm_uniformPhaseAmplitude]
  exact minAmplitude_le μ hn j

end

end NumDetect
end LeanNumDetect
