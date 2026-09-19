import NumDetectMain.Matrices

/-! Definitions used by the contiguous-grid NumDetect results. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- The normalized minimum separation `θ_min(Ω,n)`. -/
def normalizedMinimumSeparation {d n : ℕ} (Ω : ℝ)
    (node : Fin n → Point d) (hn : 2 ≤ n) : ℝ :=
  Ω / (2 * n * Real.pi) * minimumL1Separation node hn

/-- Right-hand side of `eq:uniform-Vandermonde`. -/
def uniformVandermondeLowerBound {d n : ℕ} (s : ℕ) (Ω : ℝ)
    (node : Fin n → Point d) (hn : 2 ≤ n) : ℝ :=
  Real.sqrt
      (1 / ((n : ℝ) * 2 ^ (n - 1)) *
        (((2 * (s / (2 * n)) + 1 : ℕ) : ℝ) ^ d)) *
    normalizedMinimumSeparation Ω node hn ^ (n - 1)

/-- Separation threshold in `liueq5.4v2`. -/
def uniformDetectionSeparationThreshold {d n : ℕ}
    (s : ℕ) (Ω σ mMin : ℝ) : ℝ :=
  2 * n * Real.pi / Ω *
    ((n * 2 ^ n : ℝ) /
        (mMin * (((2 * (s / (2 * n)) + 1 : ℕ) : ℝ) ^ d)) *
      ((s + 1 : ℕ) : ℝ) ^ d * σ) ^
      (1 / (2 * (n : ℝ) - 2))

/-- Explicit separation threshold in `equ:sepa_condi_1`. -/
def numberDetectionSeparationThreshold (d n : ℕ)
    (Ω σ mMin : ℝ) : ℝ :=
  4 * Real.sqrt 2 * n * Real.pi / Ω *
    (3 / Real.sqrt 5) ^ d *
    (σ / mMin) ^ (1 / (2 * (n : ℝ) - 2))

end

end NumDetect
end LeanNumDetect
