import RandSamp.FixedSeparatedCube

/-! The one-dimensional corollary of the fixed separated-node theorem in
arbitrary dimension. The original hypotheses, sampling rate, and singular-value
endpoints are retained, with the proof obtained by specializing to `d = 1`. -/

set_option autoImplicit false

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- Positivity of the lower endpoint, specialized from the cube bound at `d = 1`. -/
theorem fixedSeparated_lower_bound_pos {M : ℕ} (hM : 0 < M) {Δ ρ : ℝ}
    (hΔ : 2 * Real.pi / M < Δ) (hρ : ρ < 1) :
    0 < Real.sqrt ((1 - ρ) * ((M : ℝ) - 2 * Real.pi / Δ) / (M + 1)) := by
  simpa only [cubeSeparatedLower_one, separatedLower, mul_div_assoc] using
    cubeSeparated_lower_bound_pos (d := 1) (by decide) hM (by norm_num; exact hΔ) hρ

/-- The `d = 1` corollary of manuscript
`thm:fixed-separated-singular-values-higher-dimensional`. The original
one-dimensional interface is retained, and the tuple `Y` is fixed before
drawing the uniformly random subset. -/
theorem fixedSeparated_singularValues {M s m : ℕ}
    (hM : 3 ≤ M) (hs : 2 ≤ s) (_hsM : s < M)
    (hm : 1 ≤ m) (hmM : m ≤ M + 1)
    {Δ ρ η : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hΔlow : 2 * Real.pi / M < Δ) (hΔhigh : Δ ≤ 2 * Real.pi / s)
    (Y : Fin s → ℝ) (hsep : AngularSeparated Δ Y)
    (hsample : 3 * (s : ℝ) * (M + 1) /
      (ρ ^ 2 * ((M : ℝ) - 2 * Real.pi / Δ)) * Real.log (2 * s / η) ≤ m) :
    1 - η ≤ probability (fun Ω : Sample (M + 1) m =>
      Real.sqrt ((1 - ρ) * ((M : ℝ) - 2 * Real.pi / Δ) / (M + 1)) ≤
        matrixSingularValue (sampledVandermonde m Y Ω.val) (s - 1) ∧
      matrixSingularValue (sampledVandermonde m Y Ω.val) (s - 1) ≤
        matrixSingularValue (sampledVandermonde m Y Ω.val) 0 ∧
      matrixSingularValue (sampledVandermonde m Y Ω.val) 0 ≤
        Real.sqrt ((1 + ρ) * ((M : ℝ) + 2 * Real.pi / Δ) / (M + 1))) := by
  have hsr : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hΔpi : Δ ≤ Real.pi := hΔhigh.trans
    ((div_le_iff₀ (by positivity : (0 : ℝ) < s)).2 (by nlinarith [Real.pi_pos]))
  have hrate : 3 * (s : ℝ) / (cubeSeparatedLower 1 M Δ * ρ ^ 2) *
      Real.log (2 * s / η) ≤ m := by
    rw [cubeSeparatedLower_one]
    convert hsample using 1
    unfold separatedLower
    congr 1
    field_simp
  have h := fixedSeparatedCube_singularValues (d := 1) (by decide) (by omega) hs
    hm (by simpa using hmM) hρ0 hρ1 hη0 hη1 (by norm_num; exact hΔlow) hΔpi
    (fun j (_ : Fin 1) => Y j) (by
      intro i j hij
      exact ⟨0, hsep i j hij⟩) hrate
  let P := CubeSingularValueEvent (fun j (_ : Fin 1) => Y j)
    (cubeSeparatedLower 1 M Δ) (cubeSeparatedUpper 1 M Δ) ρ (M := M) (m := m)
  change 1 - η ≤ probability P at h
  rw [← probability_comp_equiv
    (finiteSampleEquiv (Equiv.funUnique (Fin 1) (Fin (M + 1))).symm m) P] at h
  simpa only [P, CubeSingularValueEvent, cubeSampledVandermonde_one_singularValue,
    cubeSeparatedLower_one, cubeSeparatedUpper_one, separatedLower, separatedUpper,
    mul_div_assoc] using h

end

end LeanNumDetect.RandSamp
