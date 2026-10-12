import NumDetect.Preliminaries.Matrices

/-! Segmented-grid GHM and Vandermonde definitions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- One row-coordinate of the segmented index set. -/
abbrev SegmentedCoordinateIndex (m r : ℕ) := Fin (r + 1) × Fin (m + 1)

/-- The Cartesian product `Λ^d`, with its canonical block/offset ordering. -/
abbrev SegmentedIndex (d m r : ℕ) := Fin d → SegmentedCoordinateIndex m r

/-- Integer frequency `D s + h` represented as a real vector. -/
def segmentedFrequency (d m r D : ℕ) (α : SegmentedIndex d m r) : Point d :=
  fun k => (D * (α k).1 + (α k).2 : ℕ)

/-- Maximum segmented frequency `Ω = rD + m`. -/
def segmentedCutoff (m r D : ℕ) : ℕ :=
  r * D + m

/-- Number of one-dimensional segmented indices `L = (r+1)(m+1)`. -/
def segmentedLength (m r : ℕ) : ℕ :=
  (r + 1) * (m + 1)

/-- The segmented multidimensional Vandermonde matrix `V₁`. -/
def segmentedVandermonde {d n : ℕ} (m r D : ℕ)
    (node : Fin n → Point d) :
    Matrix (SegmentedIndex d m r) (Fin n) ℂ :=
  generalizedVandermonde (segmentedFrequency d m r D) node

/-- Column Vandermonde factor in the symmetric segmented GHM construction. -/
def segmentedColumnVandermonde {d n : ℕ} (m r D : ℕ)
    (node : Fin n → Point d) :
    Matrix (SegmentedIndex d m r) (Fin n) ℂ :=
  generalizedVandermonde (segmentedFrequency d m r D) node

/-- A frequency in the segmented sampling set `Γ_seg = Λ^d + Λ^d - Ω 1`. -/
def segmentedQueryFrequency (d m r D : ℕ)
    (α β : SegmentedIndex d m r) : Point d :=
  fun k =>
    segmentedFrequency d m r D α k + segmentedFrequency d m r D β k -
      segmentedCutoff m r D

/-- Membership in the frequencies queried by the segmented GHM. -/
def InSegmentedSamplingSet (d m r D : ℕ) (ω : Point d) : Prop :=
  ∃ α β : SegmentedIndex d m r, ω = segmentedQueryFrequency d m r D α β

/-- Bounded-noise Fourier measurements on `Γ_seg` only. -/
def IsSegmentedMeasurement {d n : ℕ} (μ : AtomicMeasure d n)
    (m r D : ℕ) (σ : ℝ) (Y : Point d → ℂ) : Prop :=
  ∃ W : Point d → ℂ,
    (∀ ω, InSegmentedSamplingSet d m r D ω → ‖W ω‖ < σ) ∧
    ∀ ω, InSegmentedSamplingSet d m r D ω → Y ω = fourier μ ω + W ω

/-- The segmented measurement matrix `GH(m,r,D)`. -/
def segmentedMeasurementMatrix {d : ℕ} (m r D : ℕ)
    (Y : Point d → ℂ) :
    Matrix (SegmentedIndex d m r) (SegmentedIndex d m r) ℂ :=
  fun α β => Y fun k =>
    segmentedFrequency d m r D α k + segmentedFrequency d m r D β k -
      segmentedCutoff m r D

/-- Phase-shifted diagonal in the segmented GHM factorization. -/
def segmentedPhaseAmplitude {d n : ℕ} (m r D : ℕ) (μ : AtomicMeasure d n) :
    Fin n → ℂ :=
  fun j => μ.amplitude j *
    Complex.exp (-Complex.I *
      ((segmentedCutoff m r D : ℝ) * ∑ k, μ.node j k : ℝ))

/-- Noiseless segmented GHM `V₁ Σ V₁ᵀ`. -/
def segmentedNoiselessMatrix {d n : ℕ} (m r D : ℕ)
    (μ : AtomicMeasure d n) :
    Matrix (SegmentedIndex d m r) (SegmentedIndex d m r) ℂ :=
  segmentedVandermonde m r D μ.node *
    Matrix.diagonal (segmentedPhaseAmplitude m r D μ) *
    (segmentedColumnVandermonde m r D μ.node)ᵀ

end

end NumDetect
end LeanNumDetect
