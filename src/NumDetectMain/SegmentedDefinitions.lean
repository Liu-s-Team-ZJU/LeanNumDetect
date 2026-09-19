import NumDetectMain.Matrices

/-! Definitions used by both segmented Vandermonde and threshold proofs. -/

set_option autoImplicit false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- `m₁ = ⌈m/2⌉` for an integer `m`. -/
def localizationHalfWidth (m : ℕ) : ℕ :=
  (m + 1) / 2

/-- `K_loc = ⌊m₁/n⋆⌋`. -/
def localizationOrder (m nStar : ℕ) : ℕ :=
  localizationHalfWidth m / nStar

/-- Explicit lower bound in `thm:segmented-vandermonde`. -/
def segmentedVandermondeLowerBound
    (d n nStar m r D : ℕ) (β Δ₁ : ℝ) : ℝ :=
  1 / Real.sqrt n *
    (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
    Real.sqrt
      (((r : ℝ) / nStar) ^ d *
        (((m / 2 + 1 : ℕ) : ℝ) ^ d)) /
    (Real.sqrt 2) ^ (nStar - 1) *
    (((r * D : ℕ) : ℝ) / (Real.pi * nStar) * Δ₁) ^ (nStar - 1)

/-- Separation threshold in `eq:separation_condition_segmented`. -/
def segmentedDetectionSeparationThreshold
    (d n nStar m r D : ℕ) (β σ mMin : ℝ) : ℝ :=
  Real.sqrt 2 * Real.pi * ((nStar : ℝ) + 1 / 2) *
      (Real.sqrt 5) ^ d /
      ((segmentedCutoff m r D : ℝ) *
        (2 - Real.exp (1 / (2 * β)))) *
    (2 * n * σ / mMin) ^ (1 / (2 * (nStar : ℝ) - 2))

end

end NumDetect
end LeanNumDetect
