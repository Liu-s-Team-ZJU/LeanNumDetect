import General.Fourier.SeparatedCubeFourier

/-!
The translated-cube form of the discrete well-separated Fourier-frame bound.

Li states the multivariate result for the centered cube `Q_m`; the classical
Beurling--Selberg interval minorant supplies the same conclusion for `d = 1`.
In the discrete proof
(Section 5.1, using Theorem 2.2 and Lemma 2.1), the extremal-function argument
applies without change to a translate of the frequency cube.  Taking the real
cube centered at `(N - 1) / 2` with radius `N / 2` makes its integer points
exactly `{0, ..., N - 1}`.  This formulation avoids replacing a real radius by
its floor and is valid for both parities of `N`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace External

noncomputable section

/-- The integer points in a translated cube containing `N` consecutive
frequencies in every coordinate. -/
abbrev OneSidedCubeFrequency (d N : ℕ) := Fin d → Fin N

/-- Fourier energy on the translated integer cube `{0, ..., N - 1}^d`, in
Li's unit-torus normalization. -/
noncomputable def translatedCubeFourierEnergy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (N : ℕ) (x : ι → UnitTorusPoint d) (c : ι → ℂ) : ℝ :=
  ∑ ω : OneSidedCubeFrequency d N,
    ‖∑ j, c j * Complex.exp
      (-2 * Real.pi * Complex.I *
        (∑ k, (((ω k : Fin N) : ℕ) : ℂ) * x j k))‖ ^ 2

/-- Weilin Li, *Nonharmonic multivariate Fourier transforms and matrices:
condition numbers and hyperplane geometry*, Applied and Computational Harmonic
Analysis 79 (2025), 101791, the Beurling--Selberg discussion preceding
Theorem 2.2, Theorem 2.2, and the discrete argument in the proof of Theorem 2.3
(Section 5.1).

This is the translated-cube quadratic-frame formulation.  The real cube is
centered at `(N - 1) / 2` and has radius `N / 2`, so its intersection with the
integer lattice is exactly `{0, ..., N - 1}^d`.  Translation only modulates the
columns of the Fourier matrix and the proof of Lemma 2.1 is unchanged. -/
theorem translatedCubeFourier_lowerFrame
    {d N : ℕ} {ι : Type*} [Fintype ι]
    (β : ℝ) (x : ι → UnitTorusPoint d)
    (hd : 1 ≤ d) (hN : 2 ≤ N)
    (hβ : 1 / (2 * Real.log 2) ≤ β)
    (hx : ∀ j, InUnitHalfOpenCube (x j))
    (hsep : ∀ i j, i ≠ j →
      2 * β * d / N ≤ unitPeriodicLInfDistance (x i) (x j)) :
    ∀ c,
      (2 - Real.exp (1 / (2 * β))) * (N ^ d : ℕ) *
          coefficientEnergy c ≤
        translatedCubeFourierEnergy N x c := by
  sorry

end

end External
