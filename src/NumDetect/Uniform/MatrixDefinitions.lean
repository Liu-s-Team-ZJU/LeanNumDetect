import NumDetect.Preliminaries.Matrices

/-! Contiguous-grid GHM and Vandermonde definitions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Multi-index set `{0, …, s}^d` for the contiguous construction. -/
abbrev UniformIndex (d s : ℕ) := Fin d → Fin (s + 1)

/-- Membership in the frequencies queried by the contiguous GHM, `Γ_s`. -/
def InUniformSamplingSet (d s : ℕ) (Ω : ℝ) (ω : Point d) : Prop :=
  ∃ α β : UniformIndex d s,
    ω = fun k => Ω / s * ((α k : ℝ) + (β k : ℝ) - s)

/-- Bounded-noise Fourier measurements on `Γ_s` only. -/
def IsUniformMeasurement {d n : ℕ} (μ : AtomicMeasure d n)
    (s : ℕ) (Ω σ : ℝ) (Y : Point d → ℂ) : Prop :=
  ∃ W : Point d → ℂ,
    (∀ ω, InUniformSamplingSet d s Ω ω → ‖W ω‖ < σ) ∧
    ∀ ω, InUniformSamplingSet d s Ω ω → Y ω = fourier μ ω + W ω

/-- Physical row frequency `(Ω/s) α` of the contiguous Vandermonde matrix. -/
def uniformFrequency (d s : ℕ) (Ω : ℝ) (α : UniformIndex d s) : Point d :=
  fun k => Ω / s * α k

/-- The contiguous multidimensional Vandermonde matrix `V₁`. -/
def uniformVandermonde {d n : ℕ} (s : ℕ) (Ω : ℝ)
    (node : Fin n → Point d) : Matrix (UniformIndex d s) (Fin n) ℂ :=
  generalizedVandermonde (uniformFrequency d s Ω) node

/-- The queried GHM `GH(s)` on the scaled grid from the manuscript. -/
def uniformMeasurementMatrix {d : ℕ} (s : ℕ) (Ω : ℝ)
    (Y : Point d → ℂ) : Matrix (UniformIndex d s) (UniformIndex d s) ℂ :=
  fun α β => Y fun k => Ω / s * ((α k : ℝ) + (β k : ℝ) - s)

/-- Phase-shifted diagonal in the contiguous GHM factorization. -/
def uniformPhaseAmplitude {d n : ℕ} (Ω : ℝ) (μ : AtomicMeasure d n) :
    Fin n → ℂ :=
  fun j => μ.amplitude j *
    Complex.exp (-Complex.I * (Ω * ∑ k, μ.node j k : ℝ))

/-- Noiseless contiguous GHM `V₁ Σ V₁ᵀ`. -/
def uniformNoiselessMatrix {d n : ℕ} (s : ℕ) (Ω : ℝ)
    (μ : AtomicMeasure d n) :
    Matrix (UniformIndex d s) (UniformIndex d s) ℂ :=
  uniformVandermonde s Ω μ.node *
    Matrix.diagonal (uniformPhaseAmplitude Ω μ) *
    (uniformVandermonde s Ω μ.node)ᵀ

end

end NumDetect
end LeanNumDetect
