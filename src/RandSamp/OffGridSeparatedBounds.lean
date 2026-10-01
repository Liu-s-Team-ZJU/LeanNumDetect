import RandSamp.OffGridSignal
import RandSamp.UniformSeparated

/-! Full-Gram bounds used by the separated specialization of the relative
off-grid theorem. The constants are exactly those of the earlier uniform
kernel theorem, including its improved lower endpoint. -/

set_option autoImplicit false

open WithLp
open scoped BigOperators

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

theorem quadratic_cubeFullGram_one {M s : ℕ} (Y : Fin s → ℝ)
    (z : EuclideanSpace ℂ (Fin s)) :
    FiniteMatrixSampling.quadratic (cubeFullGram M (fun j (_ : Fin 1) => Y j)) z =
      FiniteMatrixSampling.quadratic (fullGram M Y) z := by
  rw [cubeFullGram, quadratic_cubeFourier_mean, fullGram, quadratic_fourier_mean]
  simp only [pow_one, Nat.cast_add, Nat.cast_one]
  congr 1
  have he := (Equiv.funUnique (Fin 1) (Fin (M + 1))).sum_comp
    (fun k : Fin (M + 1) => fourierRowEnergy Y k.val (ofLp z))
  have hd : (default : Fin 1) = 0 := Subsingleton.elim _ _
  simpa only [cubeFourierRowEnergy, fourierRowEnergy, cubeFourierRow_one,
    Equiv.funUnique_apply, hd] using he

theorem uniformSeparated_fullGram_bounds {M s : ℕ} (hM : 1 ≤ M)
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔupper : Δ ≤ 2 * Real.pi)
    (Y : Fin s → ℝ) (hsep : AngularSeparated Δ Y)
    (z : EuclideanSpace ℂ (Fin s)) :
    uniformSeparatedLower M Δ * ‖z‖ ^ 2 ≤
      FiniteMatrixSampling.quadratic (fullGram M Y) z ∧
    FiniteMatrixSampling.quadratic (fullGram M Y) z ≤ separatedUpper M Δ * ‖z‖ ^ 2 := by
  have h := uniform_cube_full_gram_bounds (d := 1) (by decide) hM hΔ hΔupper
    (fun j (_ : Fin 1) => Y j) (by
      intro i j hij
      exact ⟨0, hsep i j hij⟩) z
  simpa only [quadratic_cubeFullGram_one, uniformCubeLower_one,
    uniformSeparatedLower, cubeSeparatedUpper_one] using h

theorem fullGram_lower_le_one {M s : ℕ} (hs : 0 < s)
    (Y : Fin s → ℝ) {a : ℝ}
    (hgram : ∀ z : EuclideanSpace ℂ (Fin s),
      a * ‖z‖ ^ 2 ≤ FiniteMatrixSampling.quadratic (fullGram M Y) z) : a ≤ 1 := by
  classical
  let i : Fin s := ⟨0, hs⟩
  let z : EuclideanSpace ℂ (Fin s) := toLp 2 (Pi.single i 1)
  have hn : ‖z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    rw [Finset.sum_eq_single i]
    · simp [z]
    · intro j _ hji
      simp [z, hji]
    · simp
  have hsum (k : ℕ) :
      (∑ j, fourierRow Y k j * ofLp z j) = fourierRow Y k i := by
    rw [Finset.sum_eq_single i]
    · simp [z]
    · intro j _ hji
      simp [z, hji]
    · simp
  have he : FiniteMatrixSampling.quadratic (fullGram M Y) z = 1 := by
    rw [fullGram, quadratic_fourier_mean]
    simp only [fourierRowEnergy, hsum, norm_fourierRow, one_pow,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by positivity)
  simpa only [hn, he, mul_one] using hgram z

end

end LeanNumDetect.RandSamp
