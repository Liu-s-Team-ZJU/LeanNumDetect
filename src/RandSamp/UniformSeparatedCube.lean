import RandSamp.UniformKernel
import RandSamp.UniformCubeFullGram
import RandSamp.UniformSeparatedEvents

/-! Uniform random Fourier sampling over every separated node configuration in
arbitrary dimension, with the exact manuscript constants. -/

set_option autoImplicit false

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The lower singular-value endpoint in the uniform cube theorem is positive. -/
theorem uniformCube_lower_bound_pos {d M : ℕ} (hd : 1 ≤ d) (hM : 2 ≤ M)
    {Δ ρ : ℝ}
    (hΔlow : 2 * Real.pi * (2 * (d : ℝ) - 1) /
      ((M : ℝ) + (3 / 2 : ℝ) * d) < Δ) (hρ1 : ρ < 1) :
    0 < Real.sqrt ((1 - ρ) * uniformCubeLower d M Δ) := by
  exact Real.sqrt_pos.2 (mul_pos (sub_pos.mpr hρ1)
    (uniformCubeLower_pos hd (by omega) hΔlow))

/-- Manuscript `thm:uniform-separated-singular-values-higher-dimensional`.
The quantifier over all separated real lifts of torus nodes is inside one
event for the uniformly sampled frequency subset. -/
theorem uniformSeparatedCube_singularValues {d M s m : ℕ}
    (hd : 1 ≤ d) (hM : 2 ≤ M) (hs : 2 ≤ s)
    (hm : 1 ≤ m) (hmN : m ≤ (M + 1) ^ d)
    {Δ ρ η : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hη0 : 0 < η) (_hη1 : η < 1)
    (hΔlow : 2 * Real.pi * (2 * (d : ℝ) - 1) /
      ((M : ℝ) + (3 / 2 : ℝ) * d) < Δ)
    (hΔhigh : Δ ≤ Real.pi)
    (hsample : 16 * ((s : ℝ) - 1) ^ 2 /
      (ρ ^ 2 * (uniformCubeLower d M Δ) ^ 2) *
      Real.log (4 * (1 + 8 * Real.pi * d * M * ((s : ℝ) - 1) /
        (ρ * uniformCubeLower d M Δ)) ^ d / η) ≤ m) :
    1 - η ≤ probability (fun Ω : FiniteSample (CubeFrequency d M) m =>
      ∀ Y : Fin s → Fin d → ℝ, CubeAngularSeparated Δ Y →
        Real.sqrt ((1 - ρ) * uniformCubeLower d M Δ) ≤
          matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (s - 1) ∧
        matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (s - 1) ≤
          matrixSingularValue (cubeSampledVandermonde m Y Ω.val) 0 ∧
        matrixSingularValue (cubeSampledVandermonde m Y Ω.val) 0 ≤
          Real.sqrt (cubeSeparatedUpper d M Δ + ρ * uniformCubeLower d M Δ)) := by
  have ha : 0 < uniformCubeLower d M Δ :=
    uniformCubeLower_pos hd (by omega) hΔlow
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < 2 * (d : ℝ) - 1 := by linarith
  have hΔ0 : 0 < Δ := (by positivity :
    0 < 2 * Real.pi * (2 * (d : ℝ) - 1) /
      ((M : ℝ) + (3 / 2 : ℝ) * d)).trans hΔlow
  have hΔupper : Δ ≤ 2 * Real.pi := hΔhigh.trans (by linarith [Real.pi_pos])
  have hs1 : 0 < (s : ℝ) - 1 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  let ε := ρ * uniformCubeLower d M Δ / ((s : ℝ) - 1)
  have hε : 0 < ε := div_pos (mul_pos hρ0 ha) hs1
  have hcoef : 16 / ε ^ 2 =
      16 * ((s : ℝ) - 1) ^ 2 / (ρ ^ 2 * (uniformCubeLower d M Δ) ^ 2) := by
    dsimp [ε]
    field_simp
  have harg : 1 + 8 * Real.pi * d * M / ε =
      1 + 8 * Real.pi * d * M * ((s : ℝ) - 1) /
        (ρ * uniformCubeLower d M Δ) := by
    dsimp [ε]
    rw [div_div_eq_mul_div]
  have hrate : 16 / ε ^ 2 *
      Real.log (4 * (1 + 8 * Real.pi * d * M / ε) ^ d / η) ≤ m := by
    rwa [hcoef, harg]
  have hprob := uniformCubeKernel_probability hd (by omega) hm hmN hε hη0 hrate
  apply hprob.trans
  apply probability_mono
  intro Ω hΩ Y hsep
  have he : ((s : ℝ) - 1) * ε = ρ * uniformCubeLower d M Δ := by
    dsimp [ε]
    exact mul_div_cancel₀ _ (ne_of_gt hs1)
  have hlo : uniformCubeLower d M Δ - ((s : ℝ) - 1) * ε =
      (1 - ρ) * uniformCubeLower d M Δ := by rw [he]; ring
  have h := cube_singularValues_of_uniform_kernel (by omega) hm Y Ω hΩ
    (uniform_cube_full_gram_bounds hd (by omega) hΔ0 hΔupper Y hsep)
    (by rw [hlo]; exact (mul_pos (sub_pos.mpr hρ1) ha).le)
  rw [hlo, he] at h
  exact h

end

end LeanNumDetect.RandSamp
