import Mathlib

/-!
Definitions for separated-node cube Fourier estimates in Li's source
normalization. Nodes lie in the half-open unit cube, Fourier phases use
`-2πi ω · x`, and the sampling cube has real radius `m`.

The former admitted statement of Li's Theorem 2.3 was removed after source
audit: its continuous and discrete conclusions require different separation
metrics, and the published proof's reduction from real to integer sampling
radius does not preserve its separation hypothesis. The proved reductions
toward corrected continuous and discrete statements live under
`General.Fourier`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace External

noncomputable section

/-- A point in the source's unit-torus normalization. -/
abbrev UnitTorusPoint (d : ℕ) := Fin d → ℝ

/-- The source representative convention `[-1/2, 1/2)^d`. -/
def InUnitHalfOpenCube {d : ℕ} (x : UnitTorusPoint d) : Prop :=
  ∀ k, -(1 : ℝ) / 2 ≤ x k ∧ x k < (1 : ℝ) / 2

/-- Wrapped distance in one coordinate of the unit torus. -/
def unitPeriodicCoordinateDistance (u v : ℝ) : ℝ :=
  min |u - v| (1 - |u - v|)

/-- Periodic `ℓ∞` distance on the unit torus, for half-open-cube representatives. -/
def unitPeriodicLInfDistance {d : ℕ}
    (u v : UnitTorusPoint d) : ℝ :=
  ‖fun k => unitPeriodicCoordinateDistance (u k) (v k)‖

/-- Integer points in the centered cube `Q_m`. -/
abbrev CenteredInteger (m : ℝ) :=
  ↥(Finset.Icc (-⌊m⌋) ⌊m⌋)

/-- The integer sampling set `Q_m ∩ ℤ^d`. -/
abbrev CenteredCubeFrequency (d : ℕ) (m : ℝ) :=
  Fin d → CenteredInteger m

/-- Squared Euclidean norm of a finite coefficient family. -/
def coefficientEnergy {ι : Type*} [Fintype ι] (c : ι → ℂ) : ℝ :=
  ∑ j, ‖c j‖ ^ 2

/-- Squared `L²(Q_m)` norm of the source's continuous Fourier transform. -/
noncomputable def continuousCubeFourierEnergy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m : ℝ) (x : ι → UnitTorusPoint d) (c : ι → ℂ) : ℝ :=
  ∫ ω in {ω : Fin d → ℝ | ∀ k, |ω k| ≤ m},
    ‖∑ j, c j * Complex.exp
      (-2 * Real.pi * Complex.I * (∑ k, (ω k : ℂ) * x j k))‖ ^ 2

/-- Squared Euclidean norm of the source's integer-sampled Fourier transform. -/
noncomputable def discreteCubeFourierEnergy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (m : ℝ) (x : ι → UnitTorusPoint d) (c : ι → ℂ) : ℝ :=
  ∑ ω : CenteredCubeFrequency d m,
    ‖∑ j, c j * Complex.exp
      (-2 * Real.pi * Complex.I *
        (∑ k, ((ω k : ℤ) : ℂ) * x j k))‖ ^ 2

end

end External
