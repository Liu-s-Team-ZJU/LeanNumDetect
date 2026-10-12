import NumDetect.Preliminaries.Basic

/-! Number-detection guarantees and computational resolution limits. -/

set_option autoImplicit false

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- A separation threshold guarantees number detection if every admissible measure has at least
the true number of supports. -/
def NumberDetectionGuarantee (d n : ℕ) (p : LpIndex) (Ω σ mMin D : ℝ)
    (hn : 0 < n) : Prop :=
  ∀ μ : AtomicMeasure d n,
    minAmplitude μ hn = mMin →
    (∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ.node j)) →
    (∀ i j, i ≠ j → D ≤ normAt p (μ.node i - μ.node j)) →
    ∀ Y, IsBandMeasurement μ Ω σ Y →
    ∀ (k : ℕ) (ν : AtomicMeasure d k), IsAdmissible ν Ω σ Y → n ≤ k

/-- The computational resolution limit for number detection. -/
noncomputable def numberDetectionCRL (d n : ℕ) (p : LpIndex) (Ω σ mMin : ℝ)
    (hn : 0 < n) : ℝ :=
  sInf {D : ℝ | 0 ≤ D ∧ NumberDetectionGuarantee d n p Ω σ mMin D hn}

/-- Positive-amplitude version of the number-detection guarantee. -/
def PositiveNumberDetectionGuarantee (d n : ℕ) (p : LpIndex) (Ω σ mMin D : ℝ)
    (hn : 0 < n) : Prop :=
  ∀ μ : AtomicMeasure d n,
    μ.IsPositive →
    minAmplitude μ hn = mMin →
    (∀ j, InOpenL1Ball (Real.pi * n / Ω) 0 (μ.node j)) →
    (∀ i j, i ≠ j → D ≤ normAt p (μ.node i - μ.node j)) →
    ∀ Y, IsBandMeasurement μ Ω σ Y →
    ∀ (k : ℕ) (ν : AtomicMeasure d k), IsPositiveAdmissible ν Ω σ Y → n ≤ k

/-- The positive-amplitude computational resolution limit. -/
noncomputable def positiveNumberDetectionCRL (d n : ℕ) (p : LpIndex)
    (Ω σ mMin : ℝ)
    (hn : 0 < n) : ℝ :=
  sInf {D : ℝ | 0 ≤ D ∧ PositiveNumberDetectionGuarantee d n p Ω σ mMin D hn}

end

end NumDetect
end LeanNumDetect
