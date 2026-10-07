import RandSamp.MultidimensionalMultiClumpSampling

/-! Integral coordinate windings, common translations, and injective column
embeddings preserve the relevant cube Fourier energies. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect.RandSamp

noncomputable section

/-- The population normalization is exactly the Gram matrix of the full
cube Vandermonde matrix. -/
theorem cubeFullGram_eq_cubeFullVandermonde_gram {d M n : ℕ}
    (Y : Fin n → Fin d → ℝ) :
    cubeFullGram M Y = (cubeFullVandermonde M Y)ᴴ * cubeFullVandermonde M Y := by
  have hscalar : star (Real.sqrt (((M + 1) ^ d : ℕ) : ℝ) : ℂ)⁻¹ *
      (Real.sqrt (((M + 1) ^ d : ℕ) : ℝ) : ℂ)⁻¹ = (((M + 1) ^ d : ℕ) : ℂ)⁻¹ := by
    simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
    rw [← _root_.mul_inv_rev, ← pow_two, ← Complex.ofReal_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  ext i j
  simp only [cubeFullGram, FiniteMatrixSampling.finiteMean, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, cubeFourierPopulation, cubeFourierRowGram,
    Matrix.mul_apply, Matrix.conjTranspose_apply, cubeFullVandermonde,
    star_mul, card_cubeFrequency]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show star (cubeFourierRow Y k i) *
      star (Real.sqrt (((M + 1) ^ d : ℕ) : ℝ) : ℂ)⁻¹ *
      ((Real.sqrt (((M + 1) ^ d : ℕ) : ℝ) : ℂ)⁻¹ * cubeFourierRow Y k j) =
      (star (Real.sqrt (((M + 1) ^ d : ℕ) : ℝ) : ℂ)⁻¹ *
        (Real.sqrt (((M + 1) ^ d : ℕ) : ℝ) : ℂ)⁻¹) *
          (star (cubeFourierRow Y k i) * cubeFourierRow Y k j) by ring, hscalar]

/-- There is one scaled factor for each other node of the same clump. -/
theorem ClumpPartition.prod_local_scaling {n A : ℕ} (P : ClumpPartition n A)
    {R : Type*} [CommMonoid R] (i : Fin n) (scale : R) :
    (∏ j, if j = i then 1 else if P.label j = P.label i then scale else 1) =
      scale ^ (P.size (P.label i) - 1) := by
  classical
  let S := (P.members (P.label i)).erase i
  have hi : i ∈ P.members (P.label i) := (P.mem_members _ _).2 rfl
  have hcard : S.card = P.size (P.label i) - 1 := by
    dsimp [S, ClumpPartition.size]
    exact Finset.card_erase_of_mem hi
  calc
    (∏ j, if j = i then 1 else if P.label j = P.label i then scale else 1) =
        ∏ j, if j ∈ S then scale else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp [S]
      · simp [S, hj, P.mem_members]
    _ = scale ^ S.card := by simp
    _ = _ := by rw [hcard]

/-- Coordinatewise winding changes and translation have one common phase in
an integer cube Fourier row. -/
theorem cubeFourierRow_phase_of_lifts {d M q : ℕ}
    (Y offset : Fin q → Fin d → ℝ) (center : Fin d → ℝ)
    (p : Fin q → Fin d → ℤ)
    (hrep : ∀ j r, Y j r = offset j r + center r + 2 * Real.pi * p j r)
    (k : CubeFrequency d M) (j : Fin q) :
    cubeFourierRow Y k j =
      Complex.exp (Complex.I * ((∑ r, ((k r : ℕ) : ℝ) * center r : ℝ) : ℂ)) *
        cubeFourierRow offset k j := by
  unfold cubeFourierRow
  rw [← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨∑ r, (k r : ℤ) * p j r, ?_⟩
  simp_rw [hrep]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Integer coordinate turns and one common translation preserve the norm of
every full cube Fourier action. -/
theorem cubeFullVandermonde_norm_of_lifts {d M q : ℕ}
    (Y offset : Fin q → Fin d → ℝ) (center : Fin d → ℝ)
    (p : Fin q → Fin d → ℤ)
    (hrep : ∀ j r, Y j r = offset j r + center r + 2 * Real.pi * p j r)
    (u : EuclideanSpace ℂ (Fin q)) :
    ‖(cubeFullVandermonde M Y).toEuclideanLin u‖ =
      ‖(cubeFullVandermonde M offset).toEuclideanLin u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro k _
  change ‖∑ j, (Real.sqrt (((M + 1)^d : ℕ) : ℝ) : ℂ)⁻¹ *
    cubeFourierRow Y k j * ofLp u j‖^2 =
      ‖∑ j, (Real.sqrt (((M + 1)^d : ℕ) : ℝ) : ℂ)⁻¹ *
        cubeFourierRow offset k j * ofLp u j‖^2
  simp_rw [cubeFourierRow_phase_of_lifts Y offset center p hrep]
  let phase := Complex.exp (Complex.I * ((∑ r, ((k r : ℕ) : ℝ) * center r : ℝ) : ℂ))
  have he (j : Fin q) : (Real.sqrt (((M + 1)^d : ℕ) : ℝ) : ℂ)⁻¹ *
      (phase * cubeFourierRow offset k j) * ofLp u j =
        phase * ((Real.sqrt (((M + 1)^d : ℕ) : ℝ) : ℂ)⁻¹ *
          cubeFourierRow offset k j * ofLp u j) := by ring
  change ‖∑ j, (Real.sqrt (((M + 1)^d : ℕ) : ℝ) : ℂ)⁻¹ *
    (phase * cubeFourierRow offset k j) * ofLp u j‖^2 = _
  simp_rw [he]
  rw [← Finset.mul_sum, norm_mul]
  have hp : ‖phase‖ = 1 := by
    simpa [phase, mul_comm] using
      Complex.norm_exp_ofReal_mul_I (∑ r, ((k r : ℕ) : ℝ) * center r)
  rw [hp, one_mul]

/-- Extending a coefficient vector by zero along an injective column map
preserves its norm and its actual cube Fourier signal. -/
theorem exists_cube_column_embedding_vector {d M n q : ℕ}
    (Y : Fin n → Fin d → ℝ) (e : Fin q → Fin n) (he : Function.Injective e)
    (u : EuclideanSpace ℂ (Fin q)) :
    ∃ w : EuclideanSpace ℂ (Fin n), ‖w‖ = ‖u‖ ∧
      (cubeFullVandermonde M Y).toEuclideanLin w =
        (cubeFullVandermonde M (Y ∘ e)).toEuclideanLin u := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  let w := ∑ j, ofLp u j • b (e j)
  have hv : Orthonormal ℂ (b ∘ e) := b.orthonormal.comp e he
  have hinner : ⟪w, w⟫_ℂ = ∑ j, star (ofLp u j) * ofLp u j := by
    simpa [w, Function.comp_apply, Complex.star_def] using
      hv.inner_sum (ofLp u) (ofLp u) Finset.univ
  have hnorm : ‖w‖ = ‖u‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) w, hinner,
      ← inner_self_eq_norm_sq (𝕜 := ℂ) u,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  refine ⟨w, hnorm, ?_⟩
  ext k
  change ((cubeFullVandermonde M Y) *ᵥ ofLp w) k =
    ((cubeFullVandermonde M (Y ∘ e)) *ᵥ ofLp u) k
  dsimp [w]
  simp only [ofLp_sum, ofLp_smul, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [b, EuclideanSpace.basisFun_apply, EuclideanSpace.single,
    PiLp.ofLp_single, Matrix.mulVec_single_one, Matrix.col_apply]
  simp only [Matrix.mulVec, dotProduct, cubeFullVandermonde]
  apply Finset.sum_congr rfl
  intro j _
  simp [cubeFourierRow, Function.comp_apply, mul_comm]

/-- Any unit signal on an injectively indexed source subset bounds the least
singular value of the complete normalized cube Fourier matrix from above. -/
theorem cubeFullVandermonde_minimumSingularValue_le_subclump_signal {d M n q : ℕ}
    (hn : 0 < n) (Y : Fin n → Fin d → ℝ) (e : Fin q → Fin n)
    (he : Function.Injective e) (u : EuclideanSpace ℂ (Fin q)) (hu : ‖u‖ = 1) :
    matrixSingularValue (cubeFullVandermonde M Y) (n - 1) ≤
      ‖(cubeFullVandermonde M (Y ∘ e)).toEuclideanLin u‖ := by
  obtain ⟨w, hwnorm, hw⟩ := exists_cube_column_embedding_vector Y e he u
  have h := lastMatrixSingularValue_mul_norm_le (cubeFullVandermonde M Y)
    (by simpa using hn) w
  rw [hw] at h
  simpa only [Fintype.card_fin, hwnorm, hu, mul_one] using h

end
end LeanNumDetect.RandSamp
