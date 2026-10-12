import RandSamp.CubeWeakLowerSampling
import NumDetect.Preliminaries.Matrices

/-! Canonical normalized Fourier rows and their integer translations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.NumDetect

open RandSamp CubeShiftBounds CubeFrameBasis FiniteMatrixSampling ConnectedBasisBounds
noncomputable section

/-- The full Vandermonde matrix without a row-count normalization. -/
def cubeUnnormalizedVandermonde {d n : ℕ} (L : ℕ) (Y : Fin n → Fin d → ℝ) :
    Matrix (CubeFrequency d L) (Fin n) ℂ := cubeFourierRow (M := L) Y

/-- The manuscript's normalized Gram matrix of the full Fourier cube. -/
def cubeNormalizedFourierGram {d n : ℕ} (L : ℕ) (Y : Fin n → Fin d → ℝ) :
    Matrix (Fin n) (Fin n) ℂ := cubeFullGram L Y

/-- The canonical row obtained by applying the inverse positive Gram square root. -/
def cubeNormalizedFourierRow {d n : ℕ} (L : ℕ) (Y : Fin n → Fin d → ℝ)
    (k : Fin d → ℤ) : EuclideanSpace ℂ (Fin n) :=
  ((CFC.sqrt (cubeNormalizedFourierGram L Y))⁻¹).toEuclideanLin
    (integerRawCubeRootRow (cubeUnitRoots Y) k)

/-- The canonical translation matrix in the same coordinates as the normalized row. -/
def cubeNormalizedFourierTranslation {d n : ℕ} (L : ℕ) (Y : Fin n → Fin d → ℝ)
    (t : Fin d → ℤ) : Matrix (Fin n) (Fin n) ℂ :=
  (CFC.sqrt (cubeNormalizedFourierGram L Y))⁻¹ *
    (Matrix.diagonal (integerRootMultiplier (cubeUnitRoots Y) t))ᴴ *
    CFC.sqrt (cubeNormalizedFourierGram L Y)

/-- Canonical change of coordinates for the unnormalized full Gram matrix. -/
def cubeCanonicalWhitening {d n : ℕ} (L : ℕ) (Y : Fin n → Fin d → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Real.sqrt ((((L + 1) ^ d : ℕ) : ℝ)) : ℂ)⁻¹ •
    (CFC.sqrt (cubeNormalizedFourierGram L Y))⁻¹

theorem cubeNormalizedFourierGram_posDef {d n L : ℕ}
    (Y : Fin n → Fin d → ℝ)
    (hfull : HasFullColumnRank (cubeFourierRow (M := L) Y)) :
    (cubeNormalizedFourierGram L Y).PosDef := by
  have hraw : (cubeRootGram (cubeUnitRoots Y) (L + 1)).PosDef := by
    rw [cubeRootGram, cubeRootMatrix_cubeUnitRoots]
    exact Matrix.PosDef.conjTranspose_mul_self _ hfull
  have hN : 0 < ((((L + 1) ^ d : ℕ) : ℝ)) := by positivity
  have hG : cubeNormalizedFourierGram L Y =
      (((((L + 1) ^ d : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) •
        cubeRootGram (cubeUnitRoots Y) (L + 1) := by
    rw [cubeRootGram_eq_card_smul_cubeFullGram, smul_smul]
    have hc : (((L + 1) ^ d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀ hc, one_smul,
      cubeNormalizedFourierGram]
  rw [hG]
  exact hraw.smul (by exact_mod_cast (inv_pos.mpr hN))

/-- Full column rank supplies every property required by the general cube lemmas. -/
theorem cubeCanonicalWhitening_valid {d n L : ℕ}
    (Y : Fin n → Fin d → ℝ)
    (hfull : HasFullColumnRank (cubeFourierRow (M := L) Y)) :
    IsUnit (cubeCanonicalWhitening L Y) ∧
      (cubeCanonicalWhitening L Y)ᴴ * cubeRootGram (cubeUnitRoots Y) (L + 1) *
        cubeCanonicalWhitening L Y = 1 := by
  let G := cubeNormalizedFourierGram L Y
  let Q := CFC.sqrt G
  let c : ℂ := Real.sqrt ((((L + 1) ^ d : ℕ) : ℝ))
  have hG : G.PosDef := cubeNormalizedFourierGram_posDef Y hfull
  have hQ : IsUnit Q := (CFC.isUnit_sqrt_iff G hG.posSemidef.nonneg).mpr hG.isUnit
  letI := hQ.invertible
  have hQstar : Qᴴ = Q := (CFC.sqrt_nonneg G).posSemidef.isHermitian.eq
  have hQQ : Q * Q = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < ((((L + 1) ^ d : ℕ) : ℝ)))).ne'
  have hcstar : star c = c := by simp [c]
  have hcsq : c * c = (((L + 1) ^ d : ℕ) : ℂ) := by
    dsimp [c]
    rw [← sq, ← Complex.ofReal_pow]
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg ((L + 1) ^ d))
  have hP : IsUnit (cubeCanonicalWhitening L Y) := by
    apply (cubeCanonicalWhitening L Y).isUnit_iff_isUnit_det.mpr
    apply Matrix.isUnit_det_of_left_inverse (A := cubeCanonicalWhitening L Y) (B := c • Q)
    change (c • Q) * (c⁻¹ • Q⁻¹) = 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc,
      Matrix.mul_inv_of_invertible, one_smul]
  refine ⟨hP, ?_⟩
  change (c⁻¹ • Q⁻¹)ᴴ * cubeRootGram (cubeUnitRoots Y) (L + 1) * (c⁻¹ • Q⁻¹) = 1
  rw [cubeRootGram_eq_card_smul_cubeFullGram]
  change (c⁻¹ • Q⁻¹)ᴴ * ((((L + 1) ^ d : ℕ) : ℂ) • G) * (c⁻¹ • Q⁻¹) = 1
  rw [← hcsq, ← hQQ, Matrix.conjTranspose_smul, star_inv₀, hcstar,
    Matrix.conjTranspose_nonsing_inv, hQstar]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc,
    Matrix.inv_mul_of_invertible, Matrix.one_mul, Matrix.mul_inv_of_invertible]
  have hs : c⁻¹ * (c * c * c⁻¹) = 1 := by field_simp
  rw [hs, one_smul]

/-- The general isotropic row equals the manuscript's canonical normalized row. -/
theorem cubeNormalizedFourierRow_eq_integerIsotropic {d n L : ℕ}
    (Y : Fin n → Fin d → ℝ)
    (_hfull : HasFullColumnRank (cubeFourierRow (M := L) Y)) (k : Fin d → ℤ) :
    cubeNormalizedFourierRow L Y k =
      integerIsotropicCubeRootRow (cubeUnitRoots Y) (cubeCanonicalWhitening L Y) (L + 1) k := by
  let G := cubeNormalizedFourierGram L Y
  let Q := CFC.sqrt G
  let c : ℂ := Real.sqrt ((((L + 1) ^ d : ℕ) : ℝ))
  have hQstar : Qᴴ = Q := (CFC.sqrt_nonneg G).posSemidef.isHermitian.eq
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < ((((L + 1) ^ d : ℕ) : ℝ)))).ne'
  have hcstar : star c = c := by simp [c]
  change Q⁻¹.toEuclideanLin _ = c • ((c⁻¹ • Q⁻¹)ᴴ).toEuclideanLin _
  rw [Matrix.conjTranspose_smul, star_inv₀, hcstar, Matrix.conjTranspose_nonsing_inv, hQstar]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem cubeNormalizedFourierRow_nat_eq_cubeFrameRow {d n L : ℕ}
    (Y : Fin n → Fin d → ℝ)
    (hfull : HasFullColumnRank (cubeFourierRow (M := L) Y)) (k : CubeFrequency d L) :
    cubeNormalizedFourierRow L Y (fun r => ((k r).val : ℤ)) =
      cubeFrameRow (cubeUnitRoots Y) (cubeCanonicalWhitening L Y) L k := by
  rw [cubeNormalizedFourierRow_eq_integerIsotropic Y hfull,
    integerIsotropicCubeRootRow_nat]
  rfl


/-- The integer-root column is exactly the conjugate Fourier row, also for negative indices. -/
theorem integerRawCubeRootRow_cubeUnitRoots_exp {d n : ℕ}
    (Y : Fin n → Fin d → ℝ) (k : Fin d → ℤ) :
    integerRawCubeRootRow (cubeUnitRoots Y) k =
      WithLp.toLp 2 (fun j => Complex.exp
        (-Complex.I * ((∑ r, (k r : ℝ) * Y j r : ℝ) : ℂ))) := by
  ext j
  change star (∏ r, Complex.exp (Complex.I * (Y j r : ℂ)) ^ k r) = _
  simp_rw [← Complex.exp_int_mul]
  rw [← Complex.exp_sum, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_sum, map_mul, map_intCast, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The canonical definition is literally the displayed inverse-Gram-square-root formula. -/
theorem cubeNormalizedFourierRow_eq_exp {d n L : ℕ}
    (Y : Fin n → Fin d → ℝ) (k : Fin d → ℤ) :
    cubeNormalizedFourierRow L Y k =
      ((CFC.sqrt (cubeNormalizedFourierGram L Y))⁻¹).toEuclideanLin
        (WithLp.toLp 2 (fun j => Complex.exp
          (-Complex.I * ((∑ r, (k r : ℝ) * Y j r : ℝ) : ℂ)))) := by
  rw [cubeNormalizedFourierRow, integerRawCubeRootRow_cubeUnitRoots_exp]

theorem cubeNormalizedFourierTranslation_eq_cubeTranslation {d n L : ℕ}
    (Y : Fin n → Fin d → ℝ)
    (hfull : HasFullColumnRank (cubeFourierRow (M := L) Y)) (t : Fin d → ℤ) :
    cubeNormalizedFourierTranslation L Y t =
      cubeTranslation (cubeUnitRoots Y) (cubeCanonicalWhitening L Y) t := by
  let G := cubeNormalizedFourierGram L Y
  let Q := CFC.sqrt G
  let c : ℂ := Real.sqrt ((((L + 1) ^ d : ℕ) : ℝ))
  have hG : G.PosDef := cubeNormalizedFourierGram_posDef Y hfull
  have hQ : IsUnit Q := (CFC.isUnit_sqrt_iff G hG.posSemidef.nonneg).mpr hG.isUnit
  letI := hQ.invertible
  have hQstar : Qᴴ = Q := (CFC.sqrt_nonneg G).posSemidef.isHermitian.eq
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < ((((L + 1) ^ d : ℕ) : ℝ)))).ne'
  have hcstar : star c = c := by simp [c]
  have hP := (cubeCanonicalWhitening_valid Y hfull).1
  letI := hP.invertible
  have hright : cubeCanonicalWhitening L Y * (c • Q) = 1 := by
    change (c⁻¹ • Q⁻¹) * (c • Q) = 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc,
      Matrix.inv_mul_of_invertible, one_smul]
  have hPi : (cubeCanonicalWhitening L Y)⁻¹ = c • Q := by
    calc
      _ = (cubeCanonicalWhitening L Y)⁻¹ * (cubeCanonicalWhitening L Y * (c • Q)) := by
        rw [hright, Matrix.mul_one]
      _ = c • Q := by
        rw [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.one_mul]
  unfold cubeTranslation coefficientTranslation
  rw [hPi]
  change Q⁻¹ * (Matrix.diagonal (integerRootMultiplier (cubeUnitRoots Y) t))ᴴ * Q =
    ((c • Q) * Matrix.diagonal (integerRootMultiplier (cubeUnitRoots Y) t) *
      (c⁻¹ • Q⁻¹))ᴴ
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hQstar, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  exact Matrix.mul_assoc _ _ _

/-- Lemma `lem:cube-vandermonde-translations`, with only its node and full-rank hypotheses. -/
theorem cubeNormalizedFourier_translations {d n L : ℕ}
    (_hd : 0 < d) (hn : 0 < n) (hL : 2 * n ≤ L)
    (Y : Fin n → Fin d → ℝ) (_hY : ∀ j, InAngularCube (Y j))
    (hfull : HasFullColumnRank (cubeFourierRow (M := L) Y)) :
    (∀ k t : Fin d → ℤ, cubeNormalizedFourierRow L Y (k + t) =
      (cubeNormalizedFourierTranslation L Y t).toEuclideanLin
        (cubeNormalizedFourierRow L Y k)) ∧
    (∀ t : Fin d → ℤ, (cubeNormalizedFourierTranslation L Y t)⁻¹ =
      cubeNormalizedFourierTranslation L Y (-t)) ∧
    (∀ t : Fin d → ℤ, (∀ r, |t r| ≤ (L : ℤ)) →
      ‖(cubeNormalizedFourierTranslation L Y t).toEuclideanLin.toContinuousLinearMap‖ ≤
        (2 : ℝ) ^ (4 * d * n ^ 2)) := by
  have hp := cubeCanonicalWhitening_valid Y hfull
  have hz : ∀ j r, cubeUnitRoots Y j r ≠ 0 := by
    intro j r
    exact Complex.exp_ne_zero _
  refine ⟨?_, ?_, ?_⟩
  · intro k t
    simp_rw [cubeNormalizedFourierRow_eq_integerIsotropic Y hfull,
      cubeNormalizedFourierTranslation_eq_cubeTranslation Y hfull]
    exact integerIsotropicCubeRootRow_translation _ _ hp.1 hz (L + 1) k t
  · intro t
    simp_rw [cubeNormalizedFourierTranslation_eq_cubeTranslation Y hfull]
    let A := cubeTranslation (cubeUnitRoots Y) (cubeCanonicalWhitening L Y) t
    let B := cubeTranslation (cubeUnitRoots Y) (cubeCanonicalWhitening L Y) (-t)
    have hBA : B * A = 1 := cubeTranslation_neg_mul _ _ hp.1 hz t
    have hA : IsUnit A := A.isUnit_iff_isUnit_det.mpr (Matrix.isUnit_det_of_left_inverse hBA)
    letI := hA.invertible
    change A⁻¹ = B
    calc
      _ = (B * A) * A⁻¹ := by rw [hBA, Matrix.one_mul]
      _ = B := by rw [Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]
  · intro t ht
    rw [cubeNormalizedFourierTranslation_eq_cubeTranslation Y hfull]
    have hh := cubeTranslation_norm_le (cubeUnitRoots Y) (cubeCanonicalWhitening L Y)
      hp.1 hp.2 (norm_cubeUnitRoots Y) hn hL t ht
    have hK : cubeShiftComparisonConstant d n = (2 : ℝ) ^ (4 * d * n ^ 2) := by
      unfold cubeShiftComparisonConstant
      rw [← pow_mul]
      congr 1
      ring
    simpa only [hK] using hh

/-- Lemma `lem:cube-row-selection`, stated for the canonical normalized Vandermonde rows. -/
theorem cubeNormalizedFourierRow_connectedBasis {d n L : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hL : 2 * n ≤ L)
    (Y : Fin n → Fin d → ℝ) (_hY : ∀ j, InAngularCube (Y j))
    (hfull : HasFullColumnRank (cubeFourierRow (M := L) Y)) :
    ∃ γ : Fin n → CubeFrequency d L,
      (∑ r, Finset.univ.sup (fun j => (γ j r).val)) ≤ (n - 1) * (L / (2 * n)) ∧
      ∀ a : Fin n → ℂ,
        cubeFrameCoefficient d n * ∑ j, ‖a j‖ ≤
          ‖∑ j, a j • cubeNormalizedFourierRow L Y (fun r => ((γ j r).val : ℤ))‖ := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hp := cubeCanonicalWhitening_valid Y hfull
  obtain ⟨basis⟩ := cubeFrameRow_connectedBasis (cubeUnitRoots Y) (cubeCanonicalWhitening L Y)
    hp.1 hp.2 (norm_cubeUnitRoots Y) hn hL
  refine ⟨basis.point, ?_, ?_⟩
  · apply le_trans _ basis.total_width
    apply Finset.sum_le_sum
    intro r _
    exact Finset.sup_le (fun j _ => basis.point_le_width j r)
  · intro a
    simp_rw [cubeNormalizedFourierRow_nat_eq_cubeFrameRow Y hfull]
    exact basis.lower a


/-- The normalized Gram definition is exactly the manuscript's full-matrix formula. -/
theorem cubeNormalizedFourierGram_eq_full_gram {d n L : ℕ}
    (Y : Fin n → Fin d → ℝ) :
    cubeNormalizedFourierGram L Y =
      ((((L + 1) ^ d : ℕ) : ℂ))⁻¹ •
        ((cubeUnnormalizedVandermonde L Y)ᴴ * cubeUnnormalizedVandermonde L Y) := by
  have hN : (((L + 1) ^ d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero d (Nat.succ_ne_zero L))
  calc
    _ = ((((L + 1) ^ d : ℕ) : ℂ))⁻¹ •
        (((((L + 1) ^ d : ℕ) : ℂ)) • cubeFullGram L Y) := by
      simp only [smul_smul, inv_mul_cancel₀ hN, one_smul, cubeNormalizedFourierGram]
    _ = ((((L + 1) ^ d : ℕ) : ℂ))⁻¹ • cubeRootGram (cubeUnitRoots Y) (L + 1) := by
      rw [cubeRootGram_eq_card_smul_cubeFullGram]
    _ = _ := by rw [cubeRootGram, cubeRootMatrix_cubeUnitRoots]; rfl

/-- The canonical translation definition uses precisely the manuscript's diagonal phases. -/
theorem cubeNormalizedFourierTranslation_eq_exp {d n L : ℕ}
    (Y : Fin n → Fin d → ℝ) (t : Fin d → ℤ) :
    cubeNormalizedFourierTranslation L Y t =
      (CFC.sqrt (cubeNormalizedFourierGram L Y))⁻¹ *
        Matrix.diagonal (fun j => Complex.exp
          (-Complex.I * ((∑ r, (t r : ℝ) * Y j r : ℝ) : ℂ))) *
        CFC.sqrt (cubeNormalizedFourierGram L Y) := by
  unfold cubeNormalizedFourierTranslation
  rw [Matrix.diagonal_conjTranspose]
  have he : (star (integerRootMultiplier (cubeUnitRoots Y) t)) =
      (fun j => Complex.exp (-Complex.I * ((∑ r, (t r : ℝ) * Y j r : ℝ) : ℂ))) := by
    funext j
    have hh := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v.ofLp j)
      (integerRawCubeRootRow_cubeUnitRoots_exp Y t)
    simpa only [integerRawCubeRootRow, PiLp.toLp_apply, Pi.star_apply] using hh
  rw [he]

#print axioms cubeNormalizedFourier_translations
#print axioms cubeNormalizedFourierRow_connectedBasis

end
end LeanNumDetect.NumDetect
