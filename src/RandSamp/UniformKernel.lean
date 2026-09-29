import RandSamp.UniformKernelModel
import General.Fourier.FiniteTorusGrid
import General.Probability.FiniteUniformConcentration

/-! Uniform concentration of the sampled Fourier kernel over the entire
`d`-dimensional angular torus, with an explicit finite-net sample rate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The deterministic net extension loses at most half the requested tolerance. -/
theorem cubeKernelError_grid_cover {d M m : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε)
    (Ω : FiniteSample (CubeFrequency d M) m) (t : Fin d → ℝ) :
    ∃ j : Fin d → Fin (torusCoverSize d M ε),
      ‖cubeKernelError Ω t‖ ≤ ‖cubeKernelError Ω (torusGridPoint j)‖ + ε / 2 := by
  obtain ⟨j, hj⟩ := exists_torusGridPoint_near hd hM hε t
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hdifference :
      ‖cubeKernelError Ω (torusWrap t) - cubeKernelError Ω (torusGridPoint j)‖ ≤ ε / 2 := by
    calc
      _ ≤ 2 * (M : ℝ) * ∑ r, |torusWrap t r - torusGridPoint j r| :=
        norm_cubeKernelError_sub_le hm Ω _ _
      _ ≤ 2 * (M : ℝ) * (ε / (4 * M)) :=
        mul_le_mul_of_nonneg_left hj (by positivity)
      _ = ε / 2 := by field_simp; ring
  have hwrap : cubeKernelError Ω (torusWrap t) = cubeKernelError Ω t :=
    cubeKernelError_wrap Ω t
  rw [hwrap] at hdifference
  have hnorm := norm_sub_norm_le (cubeKernelError Ω t) (cubeKernelError Ω (torusGridPoint j))
  exact ⟨j, by linarith⟩

/-- The finite-grid union bound and deterministic extension give a single event
controlling the kernel at every torus point. -/
theorem uniformCubeKernel_probability_ge {d M m : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hm : 1 ≤ m) (hmN : m ≤ (M + 1) ^ d) {ε : ℝ} (hε : 0 < ε) :
    1 - (torusCoverSize d M ε : ℝ) ^ d *
        (4 * Real.exp (-(m : ℝ) * ε ^ 2 / 16)) ≤
      probability (fun Ω : FiniteSample (CubeFrequency d M) m =>
        ∀ t : Fin d → ℝ, ‖cubeKernelError Ω t‖ ≤ ε) := by
  have h := finiteSample_uniform_complex_probability_ge hm (by simpa using hmN)
    (fun t (k : CubeFrequency d M) => cubePhase k t)
    (fun t k => (norm_cubePhase k t).le)
    (fun j : Fin d → Fin (torusCoverSize d M ε) => torusGridPoint j) hε
    (by
      intro Ω t
      simpa only [cubeKernelError, sampledCubeKernel, fullCubeKernel, card_cubeFrequency]
        using cubeKernelError_grid_cover hd hM hm hε Ω t)
  simpa [cubeKernelError, sampledCubeKernel, fullCubeKernel] using h

/-- The explicit logarithmic sampling rate makes the uniform kernel-error
event have probability at least `1-η`, with the same constants in every dimension. -/
theorem uniformCubeKernel_probability {d M m : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hm : 1 ≤ m) (hmN : m ≤ (M + 1) ^ d) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η)
    (hsample : 16 / ε ^ 2 *
      Real.log (4 * (1 + 8 * Real.pi * d * M / ε) ^ d / η) ≤ m) :
    1 - η ≤ probability (fun Ω : FiniteSample (CubeFrequency d M) m =>
      ∀ t : Fin d → ℝ, ‖cubeKernelError Ω t‖ ≤ ε) := by
  have h := uniformCubeKernel_probability_ge hd hM hm hmN hε
  have hQ : 0 < (1 + 8 * Real.pi * d * M / ε) ^ d := by positivity
  have hfail := finite_net_failure_bound_of_sample_size hQ hε hη hsample
  have hcard := torusCoverSize_pow_le hd hM hε
  have htail : (torusCoverSize d M ε : ℝ) ^ d *
      (4 * Real.exp (-(m : ℝ) * ε ^ 2 / 16)) ≤ η :=
    (mul_le_mul_of_nonneg_right hcard (by positivity)).trans hfail
  exact (by linarith : 1 - η ≤ 1 - (torusCoverSize d M ε : ℝ) ^ d *
    (4 * Real.exp (-(m : ℝ) * ε ^ 2 / 16))).trans h

end

end LeanNumDetect.RandSamp
