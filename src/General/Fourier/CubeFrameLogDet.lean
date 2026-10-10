import General.Fourier.CubeFrameBasis
import General.MatrixAnalysis.FrameLogDetMean
import General.MatrixAnalysis.ShiftedLogDetSpectrum

/-! Direct logarithmic determinant estimates from a connected Fourier-cube basis.
The argument sums Hadamard's inequality over eligible shifts, without passing
through subspace thickness or spectral threshold counts. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.CubeFrameLogDet
open CubeFrameBasis CubeShiftBounds ConnectedBasisBounds
open FiniteMatrixSampling FrameMatrixBounds FrameLogDetMean
noncomputable section

/-- Averaging a conditioned translated basis yields the logarithmic determinant
mean estimate; only the number of eligible shifts and their multiplicities enter. -/
theorem translated_basis_logDetMean_lower {d L n : ℕ} (hn : 1 ≤ n)
    (f : CubePoint d L → EuclideanSpace ℂ (Fin n))
    (γ : Fin n → CubePoint d L) (g : Fin d → ℕ)
    (hγ : ∀ j l, (γ j l).val ≤ g l) (hg : ∀ l, g l ≤ L)
    (hwidth : 2 * n * (∑ l, g l) ≤ (n-1) * L)
    {θ R : ℝ} (hθ : 0 < θ) (hR : 0 < R)
    (hbase : ∀ t : CubeTranslations d L g,
      L1LowerBound (fun j => f (translatedPoint γ g hγ t j)) θ)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    (1 / (2 * (n : ℝ))) * Real.log (1 + (θ ^ 2 / R) • A).det.re ≤
      (Fintype.card (CubePoint d L) : ℝ)⁻¹ *
        ∑ k, Real.log (1 + FiniteMatrixSampling.quadratic A (f k) / R) := by
  classical
  let a : CubePoint d L → ℝ := fun k => Real.log (1 + FiniteMatrixSampling.quadratic A (f k) / R)
  let b := Real.log (1 + (θ ^ 2 / R) • A).det.re
  have ha (k : CubePoint d L) : 0 ≤ a k := by
    dsimp [a]
    apply Real.log_nonneg
    exact le_add_of_nonneg_right (div_nonneg (quadratic_nonneg hA.posSemidef (f k)) hR.le)
  have hb : 0 ≤ b := by
    have hH : (1 + (θ ^ 2 / R) • A).PosDef :=
      Matrix.PosDef.one.add_posSemidef (hA.posSemidef.smul (by positivity))
    have hh := log_det_mono Matrix.PosDef.one hH (fun x => by
      simp only [quadratic_matrix_add, quadratic_real_matrix_smul, quadratic_identity]
      exact le_add_of_nonneg_right (mul_nonneg (by positivity)
        (quadratic_nonneg hA.posSemidef x)))
    simpa only [Matrix.det_one, Complex.one_re, Real.log_one] using hh
  have hper (t : CubeTranslations d L g) :
      b ≤ ∑ j, a (translatedPoint γ g hγ t j) := by
    simpa only [a, b] using basis_sum_log_lower _ hθ hR (hbase t) A hA
  have hsum : (Fintype.card (CubeTranslations d L g) : ℝ) * b ≤
      ∑ t : CubeTranslations d L g, ∑ j, a (translatedPoint γ g hγ t j) := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (CubeTranslations d L g)))
      (fun t _ => hper t)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh
  have hinj (j : Fin n) :
      (∑ t : CubeTranslations d L g, a (translatedPoint γ g hγ t j)) ≤ ∑ k, a k := by
    have hh := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ((Finset.univ : Finset (CubeTranslations d L g)).image
        (fun t => translatedPoint γ g hγ t j))) (fun k _ _ => ha k)
    rw [Finset.sum_image] at hh
    · exact hh
    · exact (translatedPoint_injective γ g hγ j).injOn
  have hdouble : (∑ t : CubeTranslations d L g, ∑ j, a (translatedPoint γ g hγ t j)) ≤
      (n : ℝ) * ∑ k, a k := by
    rw [Finset.sum_comm]
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun j _ => hinj j)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  have hc := card_cubeTranslations_lower hn g hg hwidth
  have hcR : ((n : ℝ)+1) * (Fintype.card (CubePoint d L) : ℝ) ≤
      2 * (n : ℝ) * (Fintype.card (CubeTranslations d L g) : ℝ) := by
    exact_mod_cast hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : (0 : ℝ) < Fintype.card (CubePoint d L) := by
    rw [card_cubePoint]
    positivity
  have htR : (Fintype.card (CubePoint d L) : ℝ) ≤
      2 * (Fintype.card (CubeTranslations d L g) : ℝ) := by
    have hNnon : (0 : ℝ) ≤ Fintype.card (CubePoint d L) := hN.le
    nlinarith
  have hh := hsum.trans hdouble
  have hbT := mul_le_mul_of_nonneg_right htR hb
  apply (le_inv_mul_iff₀ hN).mpr
  change (Fintype.card (CubePoint d L) : ℝ) * (1 / (2*(n : ℝ)) * b) ≤ ∑ k, a k
  calc
    _ = ((Fintype.card (CubePoint d L) : ℝ) * b) / (2*(n : ℝ)) := by ring
    _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by nlinarith)

/-- Manuscript Lemma `lem:cube-logdet-mean`: the full general-radius cube
logarithmic determinant average, obtained directly from its connected basis. -/
theorem cubeFrameRow_logDetMean_lower {d n L : ℕ} [NeZero d]
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L+1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2*n ≤ L)
    {R : ℝ} (hR : 0 < R) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    (1 / (2 * (n : ℝ))) * Real.log
      (1 + (cubeFrameThreshold d n ^ 2 / R) • A).det.re ≤
      (Fintype.card (CubePoint d L) : ℝ)⁻¹ * ∑ k,
        Real.log (1 + FiniteMatrixSampling.quadratic A (cubeFrameRow z P L k) / R) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hθ := threshold_pos hd hn
  have hK := comparisonConstant_pos d n
  obtain ⟨basis⟩ := cubeFrameRow_connectedBasis z P hP hwhite hz hn hL
  have hbudget : 2*n*(L/(2*n)) ≤ L := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self L (2*n)
  have hw : 2*n*(∑ l, basis.width l) ≤ (n-1)*L := by
    calc
      _ ≤ 2*n*((n-1)*(L/(2*n))) := Nat.mul_le_mul_left _ basis.total_width
      _ = (n-1)*(2*n*(L/(2*n))) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hbudget
  have hg (l : Fin d) : basis.width l ≤ L := by
    have hs : basis.width l ≤ ∑ k, basis.width k :=
      Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ _)
    have hs' := basis.total_width
    have hh : (n-1)*(L/(2*n)) ≤ 2*n*(L/(2*n)) := by
      exact Nat.mul_le_mul_right _ (by omega)
    exact hs.trans (hs'.trans (hh.trans hbudget))
  have hnz : ∀ j r, z j r ≠ 0 := by
    intro j r hh
    have he := hz j r
    rw [hh, norm_zero] at he
    norm_num at he
  let T : CubeTranslations d L basis.width →
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    fun t => naturalCubeTranslation z P (fun r => (t r).val)
  have htrans (t : CubeTranslations d L basis.width) (j : Fin n) :
      cubeFrameRow z P L (translatedPoint basis.point basis.width basis.point_le_width t j) =
        T t (cubeFrameRow z P L (basis.point j)) := by
    have h := isotropicCubeRootRow_natural_translation z P hP hnz (L+1)
      (fun r => (basis.point j r).val) (fun r => (t r).val)
    have he : (fun r => (basis.point j r).val) + (fun r => (t r).val) =
        (fun r => (basis.point j r).val + (t r).val) := by funext r; rfl
    rw [he] at h
    simpa only [cubeFrameRow, translatedPoint, T] using h
  have hconorm (t : CubeTranslations d L basis.width) (v : EuclideanSpace ℂ (Fin n)) :
      ‖v‖ ≤ cubeShiftComparisonConstant d n * ‖T t v‖ := by
    apply naturalCubeTranslation_conorm_le z P hP hwhite hz hn hL
    intro r
    have hh := (t r).isLt
    omega
  have hbase (t : CubeTranslations d L basis.width) :
      L1LowerBound (fun j => cubeFrameRow z P L
        (translatedPoint basis.point basis.width basis.point_le_width t j))
        (cubeFrameThreshold d n) := by
    have hh := basis.lower.map_lower (T t) hK (hconorm t)
    have hθc : cubeFrameThreshold d n ≤ cubeFrameCoefficient d n / cubeShiftComparisonConstant d n := by
      unfold cubeFrameThreshold
      apply (div_le_div_iff₀ (by positivity) hK).mpr
      have hc := coefficient_pos hd hn
      nlinarith [mul_pos hc hK]
    intro a
    have ha : 0 ≤ ∑ j, ‖a j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
    calc
      _ ≤ (cubeFrameCoefficient d n / cubeShiftComparisonConstant d n) * ∑ j, ‖a j‖ :=
        mul_le_mul_of_nonneg_right hθc ha
      _ ≤ _ := by simpa only [htrans t] using hh a
  exact translated_basis_logDetMean_lower (by omega) (cubeFrameRow z P L)
    basis.point basis.width basis.point_le_width hg hw hθ hR hbase A hA

/-- The direct logarithmic determinant estimate at the radius used by the
smooth variational weights, with the unchanged spectral coefficient `6/5`. -/
theorem cubeFrameRow_entropyMean_spectral_six_fifths {d n L : ℕ} [NeZero d]
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L+1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2*n ≤ L)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    (6/5 : ℝ) * (∑ j, Real.log
      (1 + cubeFrameThreshold d n ^ 2 * hA.isHermitian.eigenvalues j /
        ((12/5 : ℝ) * n))) ≤
      (Fintype.card (CubePoint d L) : ℝ)⁻¹ * ∑ k,
        smoothEntropy ((12/5 : ℝ) * n) (FiniteMatrixSampling.quadratic A (cubeFrameRow z P L k)) := by
  let R := (12/5 : ℝ) * n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : 0 < R := by dsimp [R]; positivity
  have hh := cubeFrameRow_logDetMean_lower z P hP hwhite hz hn hL hR A hA
  rw [shifted_log_det_real_smul_eq_sum A hA (by positivity : 0 ≤ cubeFrameThreshold d n ^ 2 / R)] at hh
  have he (j : Fin n) :
      (cubeFrameThreshold d n ^ 2 / R) * hA.isHermitian.eigenvalues j =
        cubeFrameThreshold d n ^ 2 * hA.isHermitian.eigenvalues j / R := by ring
  simp_rw [he] at hh
  have hs := mul_le_mul_of_nonneg_left hh hR.le
  have hcoef : R * (1 / (2 * (n : ℝ))) = 6/5 := by
    dsimp [R]
    field_simp
    ring
  rw [← mul_assoc, hcoef] at hs
  change (6/5 : ℝ) * (∑ j, Real.log
    (1 + cubeFrameThreshold d n ^ 2 * hA.isHermitian.eigenvalues j / R)) ≤
    (Fintype.card (CubePoint d L) : ℝ)⁻¹ * ∑ k,
      smoothEntropy R (FiniteMatrixSampling.quadratic A (cubeFrameRow z P L k))
  simpa only [smoothEntropy, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hs

#print axioms cubeFrameRow_entropyMean_spectral_six_fifths

#print axioms cubeFrameRow_logDetMean_lower

end
end LeanNumDetect.CubeFrameLogDet
