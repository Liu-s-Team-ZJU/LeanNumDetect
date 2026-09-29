import RandSamp.UniformSeparatedCube

/-! The original one-dimensional uniform separated-node statement, retained
only as the `d = 1` corollary of the arbitrary-dimensional theorem. -/

set_option autoImplicit false

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The original one-dimensional normalized lower constant. -/
def uniformSeparatedLower (M : ℕ) (Δ : ℝ) : ℝ :=
  ((M : ℝ) + 3 / 2 - 2 * Real.pi / Δ) / (M + 1)

/-- Positivity of the original lower endpoint follows from the cube theorem. -/
theorem uniformSeparated_lower_bound_pos {M : ℕ} (hM : 2 ≤ M) {Δ ρ : ℝ}
    (hΔ : 2 * Real.pi / ((M : ℝ) + 3 / 2) < Δ) (hρ : ρ < 1) :
    0 < Real.sqrt ((1 - ρ) * uniformSeparatedLower M Δ) := by
  simpa only [uniformCubeLower_one, uniformSeparatedLower] using
    uniformCube_lower_bound_pos (d := 1) (by decide) hM (by norm_num; exact hΔ) hρ

/-- Manuscript `thm:uniform-separated-singular-values`, the one-dimensional
corollary with exactly its original hypotheses, sample rate, and endpoints.
The single random-sampling event controls every separated tuple simultaneously. -/
theorem uniformSeparated_singularValues {M s m : ℕ}
    (hM : 2 ≤ M) (hs : 2 ≤ s) (hm : 1 ≤ m) (hmM : m ≤ M + 1)
    {Δ ρ η : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hΔlow : 2 * Real.pi / ((M : ℝ) + 3 / 2) < Δ)
    (hΔhigh : Δ ≤ 2 * Real.pi / s)
    (hsample : 16 * ((s : ℝ) - 1) ^ 2 /
      (ρ ^ 2 * (uniformSeparatedLower M Δ) ^ 2) *
      Real.log (4 * (1 + 8 * Real.pi * M * ((s : ℝ) - 1) /
        (ρ * uniformSeparatedLower M Δ)) / η) ≤ m) :
    1 - η ≤ probability (fun Ω : Sample (M + 1) m =>
      ∀ Y : Fin s → ℝ, AngularSeparated Δ Y →
        Real.sqrt ((1 - ρ) * uniformSeparatedLower M Δ) ≤
          matrixSingularValue (sampledVandermonde m Y Ω.val) (s - 1) ∧
        matrixSingularValue (sampledVandermonde m Y Ω.val) (s - 1) ≤
          matrixSingularValue (sampledVandermonde m Y Ω.val) 0 ∧
        matrixSingularValue (sampledVandermonde m Y Ω.val) 0 ≤
          Real.sqrt (separatedUpper M Δ + ρ * uniformSeparatedLower M Δ)) := by
  have hsr : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hΔpi : Δ ≤ Real.pi := hΔhigh.trans
    ((div_le_iff₀ (by positivity : (0 : ℝ) < s)).2 (by nlinarith [Real.pi_pos]))
  have hrate : 16 * ((s : ℝ) - 1) ^ 2 /
      (ρ ^ 2 * (uniformCubeLower 1 M Δ) ^ 2) *
      Real.log (4 * (1 + 8 * Real.pi * (1 : ℝ) * M * ((s : ℝ) - 1) /
        (ρ * uniformCubeLower 1 M Δ)) ^ 1 / η) ≤ m := by
    simpa only [uniformCubeLower_one, uniformSeparatedLower, mul_one, pow_one] using hsample
  have h := uniformSeparatedCube_singularValues (d := 1) (by decide) hM hs hm
    (by simpa using hmM) hρ0 hρ1 hη0 hη1 (by norm_num; exact hΔlow) hΔpi
    (by simpa only [Nat.cast_one] using hrate)
  let P : FiniteSample (CubeFrequency 1 M) m → Prop := fun Ω =>
    ∀ Y : Fin s → Fin 1 → ℝ, CubeAngularSeparated Δ Y →
      Real.sqrt ((1 - ρ) * uniformCubeLower 1 M Δ) ≤
        matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (s - 1) ∧
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (s - 1) ≤
        matrixSingularValue (cubeSampledVandermonde m Y Ω.val) 0 ∧
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) 0 ≤
        Real.sqrt (cubeSeparatedUpper 1 M Δ + ρ * uniformCubeLower 1 M Δ)
  change 1 - η ≤ probability P at h
  rw [← probability_comp_equiv
    (finiteSampleEquiv (Equiv.funUnique (Fin 1) (Fin (M + 1))).symm m) P] at h
  apply h.trans
  apply probability_mono
  intro Ω hΩ Y hsep
  have hy := hΩ (fun j (_ : Fin 1) => Y j) (by
    intro i j hij
    exact ⟨0, hsep i j hij⟩)
  simpa only [cubeSampledVandermonde_one_singularValue,
    uniformCubeLower_one, uniformSeparatedLower, cubeSeparatedUpper_one] using hy

end

end LeanNumDetect.RandSamp
