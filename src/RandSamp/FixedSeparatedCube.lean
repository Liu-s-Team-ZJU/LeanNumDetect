import RandSamp.CubeFixedSupport
import RandSamp.CubeGramBounds

/-! The fixed well-separated node-set theorem in arbitrary positive dimension,
with the explicit constants and sample rate of the RandSamp manuscript. -/

set_option autoImplicit false

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- Manuscript `thm:fixed-separated-singular-values-higher-dimensional`.
Each pair of nodes is separated in at least one coordinate; the coordinate may
depend on the pair. There is no Cartesian-product assumption on the node set.
The probability is uniform on actual `m`-element subsets of `{0,...,M}^d`. -/
theorem fixedSeparatedCube_singularValues {d M s m : ℕ}
    (hd : 1 ≤ d) (hM : 1 ≤ M) (hs : 2 ≤ s)
    (hm : 1 ≤ m) (hmN : m ≤ (M + 1) ^ d)
    {Δ δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hη0 : 0 < η) (_hη1 : η < 1)
    (hΔlow : 2 * Real.pi * (2 * (d : ℝ) - 1) / M < Δ)
    (hΔhigh : Δ ≤ Real.pi)
    (Y : Fin s → Fin d → ℝ) (hsep : CubeAngularSeparated Δ Y)
    (hsample : 3 * (s : ℝ) / (cubeSeparatedLower d M Δ * δ ^ 2) *
      Real.log (2 * s / η) ≤ m) :
    1 - η ≤ probability (fun Ω : FiniteSample (CubeFrequency d M) m =>
      Real.sqrt ((1 - δ) * cubeSeparatedLower d M Δ) ≤
        matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (s - 1) ∧
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (s - 1) ≤
        matrixSingularValue (cubeSampledVandermonde m Y Ω.val) 0 ∧
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) 0 ≤
        Real.sqrt ((1 + δ) * cubeSeparatedUpper d M Δ)) := by
  exact cubeFixedSupport_singularValues (by omega) hm hmN Y
    (cubeSeparatedLower_pos hd hM hΔlow) hδ0 hδ1 hη0
    (cube_separated_full_gram_bounds hd hM hΔlow hΔhigh Y hsep) hsample

end

end LeanNumDetect.RandSamp
