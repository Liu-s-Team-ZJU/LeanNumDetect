import RandSamp.MultidimensionalClumpSharpness
import RandSamp.MultidimensionalMultiClumpSampling
import General.Fourier.MultidimensionalTaylorBounds
import General.Finite.PowerOrderSharpness

/-! An admissible arithmetic clump has minimum singular value at most a
constant times `(M*Δ)^(s-1)` in every dimension. The concrete collapsing
family rules out every smaller natural uniform lower exponent. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect.RandSamp
noncomputable section

def arithmeticClumpUpperConstant (s : ℕ) : ℝ :=
  (6 * Real.sqrt (s : ℝ) / ((s - 1).factorial : ℝ)) *
    (((s - 1 : ℕ) : ℝ) ^ (s - 1))

theorem arithmeticClumpUpperConstant_pos {s : ℕ} (hs : 2 ≤ s) :
    0 < arithmeticClumpUpperConstant s := by
  unfold arithmeticClumpUpperConstant
  have hsp : 0 < s - 1 := by omega
  positivity

theorem exists_unit_arithmeticClump_row_upper {d s M : ℕ} (hd : 1 ≤ d) (hs : 2 ≤ s)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hwidth : ((s - 1 : ℕ) : ℝ) * (M : ℝ) * Δ ≤ 1) :
    ∃ u : EuclideanSpace ℂ (Fin s), ‖u‖ = 1 ∧
      ∀ k : CubeFrequency d M,
        ‖∑ j, cubeFourierRow (arithmeticClumpNodes d s Δ) k j * ofLp u j‖ ≤
          arithmeticClumpUpperConstant s * ((M : ℝ) * Δ) ^ (s - 1) := by
  classical
  let r0 : Fin d := ⟨0, by omega⟩
  let t : Fin s → ℝ := fun j => (j.val : ℝ) * Δ
  let B := ((s - 1 : ℕ) : ℝ) * Δ
  have ht (j : Fin s) : |t j| ≤ B := by
    dsimp [t, B]
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show j.val ≤ s - 1 by omega)) hΔ
  have hshort (j : Fin s) : (M : ℝ) * |t j| ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (ht j) (Nat.cast_nonneg M)
    dsimp [B] at h
    nlinarith
  have hnodes : arithmeticClumpNodes d s Δ = MultidimensionalTaylorBounds.collinearNodes r0 t := by
    funext j r
    have he : r.val = 0 ↔ r = r0 := by
      constructor
      · intro h
        exact Fin.ext h
      · rintro rfl
        rfl
    simp [arithmeticClumpNodes, MultidimensionalTaylorBounds.collinearNodes, he, t]
  obtain ⟨u, hu, hrow⟩ := MultidimensionalTaylorBounds.exists_unit_collinear_fourier_row_upper
    hs r0 t (Nat.cast_nonneg M) (by dsimp [B]; positivity) ht hshort
  refine ⟨u, hu, ?_⟩
  intro k
  have hfreq (r : Fin d) : |((k r).val : ℝ)| ≤ (M : ℝ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.le_of_lt_succ (k r).isLt
  have h := hrow (fun r => ((k r).val : ℝ)) hfreq
  change ‖∑ j, cubeFourierRow (MultidimensionalTaylorBounds.collinearNodes r0 t) k j *
    ofLp u j‖ ≤ _ at h
  rw [← hnodes] at h
  convert h using 1
  unfold arithmeticClumpUpperConstant B
  simp only [mul_pow]
  ring

theorem arithmeticClump_full_minimumSingularValue_upper {d s M : ℕ}
    (hd : 1 ≤ d) (hs : 2 ≤ s) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hwidth : ((s - 1 : ℕ) : ℝ) * (M : ℝ) * Δ ≤ 1) :
    matrixSingularValue (cubeFullVandermonde M (arithmeticClumpNodes d s Δ)) (s - 1) ≤
      arithmeticClumpUpperConstant s * ((M : ℝ) * Δ) ^ (s - 1) := by
  obtain ⟨u, hu, hrow⟩ := exists_unit_arithmeticClump_row_upper hd hs hΔ hwidth
  let E := arithmeticClumpUpperConstant s * ((M : ℝ) * Δ) ^ (s - 1)
  have hE : 0 ≤ E := mul_nonneg (arithmeticClumpUpperConstant_pos hs).le (by positivity)
  have hnorm : ‖(cubeFullVandermonde M (arithmeticClumpNodes d s Δ)).toEuclideanLin u‖ ≤ E := by
    apply (sq_le_sq₀ (norm_nonneg _) hE).mp
    rw [norm_cubeFullVandermonde_sq, cubeFullGram, quadratic_cubeFourier_mean]
    have henergy (k : CubeFrequency d M) :
        cubeFourierRowEnergy (arithmeticClumpNodes d s Δ) k (ofLp u) ≤ E ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hE).mpr (hrow k)
    calc
      _ ≤ (((M : ℝ) + 1) ^ d)⁻¹ * ∑ _k : CubeFrequency d M, E ^ 2 := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => henergy k) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, card_cubeFrequency, nsmul_eq_mul,
          Nat.cast_pow, Nat.cast_add, Nat.cast_one]
        rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have h := lastMatrixSingularValue_mul_norm_le
    (cubeFullVandermonde M (arithmeticClumpNodes d s Δ)) (by simp; omega) u
  simpa only [Fintype.card_fin, hu, mul_one] using h.trans hnorm

/-- The same arithmetic upper bound holds for every nonempty selected row
set, with its sample normalization, without any probability condition. -/
theorem arithmeticClump_sampled_minimumSingularValue_upper {d s M m : ℕ}
    (hd : 1 ≤ d) (hs : 2 ≤ s) (hm : 1 ≤ m)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hwidth : ((s - 1 : ℕ) : ℝ) * (M : ℝ) * Δ ≤ 1)
    (Ω : FiniteMatrixSampling.FiniteSample (CubeFrequency d M) m) :
    matrixSingularValue (cubeSampledVandermonde m (arithmeticClumpNodes d s Δ) Ω.val) (s - 1) ≤
      arithmeticClumpUpperConstant s * ((M : ℝ) * Δ) ^ (s - 1) := by
  obtain ⟨u, hu, hrow⟩ := exists_unit_arithmeticClump_row_upper hd hs hΔ hwidth
  let E := arithmeticClumpUpperConstant s * ((M : ℝ) * Δ) ^ (s - 1)
  have hE : 0 ≤ E := mul_nonneg (arithmeticClumpUpperConstant_pos hs).le (by positivity)
  have hnorm : ‖(cubeSampledVandermonde m (arithmeticClumpNodes d s Δ) Ω.val).toEuclideanLin u‖ ≤ E := by
    apply (sq_le_sq₀ (norm_nonneg _) hE).mp
    rw [cubeSampledVandermonde_energy]
    have henergy (k : CubeFrequency d M) :
        cubeFourierRowEnergy (arithmeticClumpNodes d s Δ) k (ofLp u) ≤ E ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hE).mpr (hrow k)
    calc
      _ ≤ (m : ℝ)⁻¹ * ∑ _k ∈ Ω.val, E ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => henergy k) (by positivity)
      _ = E ^ 2 := by
        simp only [Finset.sum_const, Ω.property, nsmul_eq_mul]
        rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (show m ≠ 0 by omega)), one_mul]
  have h := lastMatrixSingularValue_mul_norm_le
    (cubeSampledVandermonde m (arithmeticClumpNodes d s Δ) Ω.val) (by simp; omega) u
  simpa only [Fintype.card_fin, hu, mul_one] using h.trans hnorm

/-- Every proposed smaller natural exponent is contradicted by a concrete
admissible arithmetic family at an arbitrarily small positive spacing. -/
theorem arithmeticClump_lower_exponent_sharp {d s M p : ℕ}
    (hd : 1 ≤ d) (hs : 2 ≤ s) (hM : 0 < M) (hp : p < s - 1)
    {c0 C0 c : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hc : 0 < c) :
    ∃ Δ : ℝ, 0 < Δ ∧
      MultidimensionalMultiClumpGeometry M c0 C0 (arithmeticClumpNodes d s Δ)
        (arithmeticClumpPartition s (by omega)) ∧
      matrixSingularValue (cubeFullVandermonde M (arithmeticClumpNodes d s Δ)) (s - 1) <
        c * ((M : ℝ) * Δ) ^ p := by
  have hsp : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < s - 1 by omega)
  obtain ⟨t, ht, htwidth, hstrict⟩ :=
    PowerOrderSharpness.exists_small_scale_strict_power_bound hp
      (arithmeticClumpUpperConstant_pos hs) hc (by positivity : 0 < c0 / ((s - 1 : ℕ) : ℝ))
  let Δ := t / (M : ℝ)
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hΔ : 0 < Δ := div_pos ht hMR
  have hscaled : (M : ℝ) * Δ = t := by dsimp [Δ]; field_simp
  have hwidth : ((s - 1 : ℕ) : ℝ) * (M : ℝ) * Δ ≤ c0 := by
    rw [mul_assoc, hscaled]
    simpa only [mul_comm] using (le_div_iff₀ hsp).mp htwidth
  refine ⟨Δ, hΔ, arithmeticClump_geometry_of_width hd (by omega) hΔ hM hc01 hwidth, ?_⟩
  have hu := arithmeticClump_full_minimumSingularValue_upper hd hs hΔ.le (hwidth.trans hc01)
  rw [hscaled] at hu ⊢
  exact hu.trans_lt hstrict

/-- Sharpness also excludes every smaller real exponent, including
fractional improvements of the integer exponent `s-1`. -/
theorem arithmeticClump_lower_real_exponent_sharp {d s M : ℕ}
    (hd : 1 ≤ d) (hs : 2 ≤ s) (hM : 0 < M) {p : ℝ}
    (hp : p < ((s - 1 : ℕ) : ℝ))
    {c0 C0 c : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hc : 0 < c) :
    ∃ Δ : ℝ, 0 < Δ ∧
      MultidimensionalMultiClumpGeometry M c0 C0 (arithmeticClumpNodes d s Δ)
        (arithmeticClumpPartition s (by omega)) ∧
      matrixSingularValue (cubeFullVandermonde M (arithmeticClumpNodes d s Δ)) (s - 1) <
        c * ((M : ℝ) * Δ) ^ p := by
  have hsp : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < s - 1 by omega)
  obtain ⟨t, ht, htwidth, hstrict⟩ :=
    PowerOrderSharpness.exists_small_scale_strict_rpow_bound hp
      (arithmeticClumpUpperConstant_pos hs) hc (by positivity : 0 < c0 / ((s - 1 : ℕ) : ℝ))
  let Δ := t / (M : ℝ)
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hΔ : 0 < Δ := div_pos ht hMR
  have hscaled : (M : ℝ) * Δ = t := by dsimp [Δ]; field_simp
  have hwidth : ((s - 1 : ℕ) : ℝ) * (M : ℝ) * Δ ≤ c0 := by
    rw [mul_assoc, hscaled]
    simpa only [mul_comm] using (le_div_iff₀ hsp).mp htwidth
  refine ⟨Δ, hΔ, arithmeticClump_geometry_of_width hd (by omega) hΔ hM hc01 hwidth, ?_⟩
  have hu := arithmeticClump_full_minimumSingularValue_upper hd hs hΔ.le (hwidth.trans hc01)
  rw [hscaled] at hu ⊢
  rw [Real.rpow_natCast] at hstrict
  exact hu.trans_lt hstrict

end
end LeanNumDetect.RandSamp
