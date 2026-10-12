import NumDetect.Random.NormalizedRows
import General.Fourier.CubeFrameLogDet

/-! The logarithmic determinant average for the canonical normalized Fourier
rows in the manuscript. The canonical-row identities from CubeNormalizedRows
convert the general cube-frame result without adding whitening data to the
public hypotheses. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators ComplexOrder

namespace LeanNumDetect.NumDetect

open RandSamp FiniteMatrixSampling

noncomputable section

/-- Manuscript `lem:cube-logdet-mean`, with its canonical rows
`G⁻¹ᐟ² [exp(-i k · y_j)]`, rather than an additional whitening matrix as input.
The angular-cube assumption preserves exactly the manuscript's node domain. -/
theorem cubeNormalizedFourierRow_logDetMean_lower {d n L : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hL : 2 * n ≤ L)
    (Y : Fin n → Point d) (_hY : ∀ j, InAngularCube (Y j))
    (hfull : HasFullColumnRank (cubeFourierRow (M := L) Y))
    {R : ℝ} (hR : 0 < R)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    (1 / (2 * (n : ℝ))) * Real.log
      (1 + (CubeFrameBasis.cubeFrameThreshold d n ^ 2 / R) • A).det.re ≤
      (((L + 1) ^ d : ℕ) : ℝ)⁻¹ * ∑ k : CubeFrequency d L,
        Real.log (1 + FiniteMatrixSampling.quadratic A
          (cubeNormalizedFourierRow L Y (fun r => ((k r).val : ℤ))) / R) := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨hP, hwhite⟩ := cubeCanonicalWhitening_valid Y hfull
  have hrow (k : CubeFrequency d L) :
      cubeNormalizedFourierRow L Y (fun r => ((k r).val : ℤ)) =
        CubeFrameBasis.cubeFrameRow (cubeUnitRoots Y) (cubeCanonicalWhitening L Y) L k :=
    cubeNormalizedFourierRow_nat_eq_cubeFrameRow Y hfull k
  have h := CubeFrameLogDet.cubeFrameRow_logDetMean_lower
    (cubeUnitRoots Y) (cubeCanonicalWhitening L Y) hP hwhite
    (norm_cubeUnitRoots Y) hn hL hR A hA
  simpa only [← hrow, ConnectedBasisBounds.card_cubePoint] using h

#print axioms cubeNormalizedFourierRow_logDetMean_lower

end
end LeanNumDetect.NumDetect
