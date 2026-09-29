import RandSamp.UniformKernelModel
import General.MatrixAnalysis.GramPerturbation

/-! A single uniform kernel event controls every separated node configuration
whose full Gram matrix has the specified deterministic bounds. -/

set_option autoImplicit false

open Matrix

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- Kernel approximation and full-Gram bounds imply the exact additive
singular-value interval, for an arbitrary node tuple. -/
theorem cube_singularValues_of_uniform_kernel {d M s m : ℕ}
    (hs : 1 ≤ s) (hm : 1 ≤ m) (Y : Fin s → Fin d → ℝ)
    (Ω : FiniteSample (CubeFrequency d M) m) {ε a b : ℝ}
    (hkernel : ∀ t : Fin d → ℝ, ‖cubeKernelError Ω t‖ ≤ ε)
    (hfull : ∀ z : EuclideanSpace ℂ (Fin s),
      a * ‖z‖ ^ 2 ≤ FiniteMatrixSampling.quadratic (cubeFullGram M Y) z ∧
        FiniteMatrixSampling.quadratic (cubeFullGram M Y) z ≤ b * ‖z‖ ^ 2)
    (hlow : 0 ≤ a - ((s : ℝ) - 1) * ε) :
    Real.sqrt (a - ((s : ℝ) - 1) * ε) ≤
        matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (s - 1) ∧
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (s - 1) ≤
        matrixSingularValue (cubeSampledVandermonde m Y Ω.val) 0 ∧
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) 0 ≤
        Real.sqrt (b + ((s : ℝ) - 1) * ε) := by
  classical
  have h := matrixSingularValue_bounds_of_gram_perturbation
    (cubeSampledVandermonde m Y Ω.val)
    (cubeSampledVandermonde ((M + 1) ^ d) Y Finset.univ)
    (by simpa using (show 0 < s by omega))
    (by
      intro j
      rw [cubeFullVandermonde_gram, cubeSampledVandermonde_gram_diag hm,
        cubeFullGram_diag])
    (by
      intro j k _
      rw [cubeFullVandermonde_gram, cubeGram_difference_entry]
      exact hkernel _)
    (by
      intro z
      rw [cubeFullVandermonde_energy]
      exact hfull z)
    (by simpa using hlow)
  simpa using h

end

end LeanNumDetect.RandSamp
