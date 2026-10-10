import General.Probability.ThickFrameSampling
import General.Fourier.CubeShiftBounds
import General.Fourier.CubeFrameThickness
import RandSamp.MultidimensionalMultiClumpSampling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling CubeShiftBounds CappedWeightIteration
noncomputable section
attribute [local instance] Classical.propDecidable

def cubeUnitRoots {d n : ℕ} (Y : Fin n → Fin d → ℝ) : Fin n → Fin d → ℂ :=
  fun j r => Complex.exp (Complex.I*(Y j r : ℂ))

@[simp] theorem norm_cubeUnitRoots {d n : ℕ} (Y : Fin n → Fin d → ℝ) (j : Fin n) (r : Fin d) :
    ‖cubeUnitRoots Y j r‖ = 1 := by
  simpa only [cubeUnitRoots, mul_comm] using Complex.norm_exp_ofReal_mul_I (Y j r)

theorem cubeRootMatrix_cubeUnitRoots {d M n : ℕ} (Y : Fin n → Fin d → ℝ) :
    cubeRootMatrix (cubeUnitRoots Y) (M+1) = cubeFourierRow (M := M) Y := by
  ext k j
  simp only [cubeRootMatrix, cubeUnitRoots, cubeFourierRow,
    ← Complex.exp_nat_mul, ← Complex.exp_sum,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem cubeRootGram_eq_sum_cubeFourierPopulation {d M n : ℕ}
    (Y : Fin n → Fin d → ℝ) :
    cubeRootGram (cubeUnitRoots Y) (M+1) = ∑ k, cubeFourierPopulation (M := M) Y k := by
  rw [cubeRootGram, cubeRootMatrix_cubeUnitRoots]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    cubeFourierPopulation, cubeFourierRowGram]

theorem cubeRootGram_eq_card_smul_cubeFullGram {d M n : ℕ}
    (Y : Fin n → Fin d → ℝ) :
    cubeRootGram (cubeUnitRoots Y) (M+1) = (((M+1)^d : ℕ) : ℂ) • cubeFullGram M Y := by
  rw [cubeRootGram_eq_sum_cubeFourierPopulation, cubeFullGram, finiteMean,
    smul_smul, card_cubeFrequency]
  have hN : ((((M+1)^d : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero d (Nat.succ_ne_zero M))
  rw [mul_inv_cancel₀ hN, one_smul]

theorem framePopulation_linear {N n : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin n)) (A : Matrix (Fin n) (Fin n) ℂ) (k : Fin N) :
    framePopulation (fun i => A.toEuclideanLin (f i)) k = A * framePopulation f k * Aᴴ := by
  ext i j
  simp only [framePopulation, Matrix.toLpLin_apply, PiLp.toLp_apply,
    Matrix.mulVec, dotProduct, star_sum, star_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem framePopulation_real_smul {N n : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin n)) (a : ℝ) (k : Fin N) :
    framePopulation (fun i => (a : ℂ) • f i) k = ((a^2 : ℝ) : ℂ) • framePopulation f k := by
  ext i j
  simp only [framePopulation, PiLp.smul_apply, smul_eq_mul, Matrix.smul_apply,
    star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
  ring


def cubeWhitenedFrame {d M n : ℕ} (Y : Fin n → Fin d → ℝ)
    (P : Matrix (Fin n) (Fin n) ℂ) : CubeFrequency d M → EuclideanSpace ℂ (Fin n) :=
  fun k => isotropicCubeRootRow (cubeUnitRoots Y) P (M+1) (fun r => (k r).val)

theorem cubeWhitenedFrame_population {d M n : ℕ} (Y : Fin n → Fin d → ℝ)
    (P : Matrix (Fin n) (Fin n) ℂ)
    (e : Fin (Fintype.card (CubeFrequency d M)) ≃ CubeFrequency d M)
    (k : Fin (Fintype.card (CubeFrequency d M))) :
    framePopulation (fun i => cubeWhitenedFrame Y P (e i)) k =
      ((((M+1)^d : ℕ) : ℂ)) • (Pᴴ * cubeFourierPopulation Y (e k) * P) := by
  let raw := fun i => rawCubeRootRow (cubeUnitRoots Y) (fun r => (e i r).val)
  have hr : framePopulation raw k = cubeFourierPopulation Y (e k) := by
    ext i j
    have he := congrFun (congrFun (cubeRootMatrix_cubeUnitRoots (M := M) Y) (e k))
    simp only [framePopulation, raw, rawCubeRootRow, PiLp.toLp_apply, star_star,
      cubeFourierPopulation, cubeFourierRowGram]
    simp only [cubeRootMatrix] at he
    rw [he i, he j]
  have hs := framePopulation_real_smul
    (fun i => Pᴴ.toEuclideanLin (raw i))
    (Real.sqrt ((((M+1)^d : ℕ) : ℝ))) k
  rw [framePopulation_linear, Matrix.conjTranspose_conjTranspose, hr] at hs
  simpa only [cubeWhitenedFrame, isotropicCubeRootRow, whitenedCubeRootRow,
    raw, Fintype.card_fin, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast] using hs

theorem mean_real_smul {N n : ℕ} (X : Fin N → Matrix (Fin n) (Fin n) ℂ) (a : ℝ) :
    mean (fun k => (a : ℂ) • X k) = (a : ℂ) • mean X := by
  simp only [mean, Finset.smul_sum, smul_smul, mul_comm]

theorem sampleMean_real_smul {N n m : ℕ}
    (X : Fin N → Matrix (Fin n) (Fin n) ℂ) (a : ℝ) (Ω : Sample N m) :
    sampleMean (fun k => (a : ℂ) • X k) Ω = (a : ℂ) • sampleMean X Ω := by
  simp only [sampleMean, sampleSum, Finset.smul_sum, smul_smul, mul_comm]

/-- Relative lower energy of the original sampled Fourier rows. -/
def CubeWeakLowerGramEvent {d M n m : ℕ} (Y : Fin n → Fin d → ℝ) (θ ρ : ℝ)
    (Ω : FiniteSample (CubeFrequency d M) m) : Prop :=
  ∀ z : EuclideanSpace ℂ (Fin n),
    ((1-ρ)/2)*thickFrameDetFloor n θ*FiniteMatrixSampling.quadratic (cubeFullGram M Y) z ≤
      FiniteMatrixSampling.quadratic (finiteSampleMean (cubeFourierPopulation Y) Ω) z


/-- Relative lower energy transfers to every ordered singular value. -/
theorem cubeWeakLowerGramEvent_singularValue {d M n m : ℕ}
    (Y : Fin n → Fin d → ℝ) {θ ρ : ℝ} (hρ1 : ρ ≤ 1)
    (Ω : FiniteSample (CubeFrequency d M) m) (hrelative : CubeWeakLowerGramEvent Y θ ρ Ω)
    {i : ℕ} (hi : i < n) :
    Real.sqrt (((1-ρ)/2)*thickFrameDetFloor n θ) *
      matrixSingularValue (cubeFullVandermonde M Y) i ≤
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) i := by
  let a := ((1-ρ)/2)*thickFrameDetFloor n θ
  have ha : 0 ≤ a := mul_nonneg
    (div_nonneg (sub_nonneg.mpr hρ1) (by norm_num))
    (thickFrameDetFloor_pos n θ).le
  have he : 1-(1-a) = a := by ring
  have hh : CubeLowerGramEvent Y (1-a) Ω := by
    intro z
    rw [he]
    exact hrelative z
  have h := cubeLowerGramEvent_singularValue Y (ρ := 1-a) (by linarith) Ω hh hi
  rw [he] at h
  exact h

theorem cubeRootGram_posDef_of_cubeFullGram {d M n : ℕ}
    (Y : Fin n → Fin d → ℝ) (hG : (cubeFullGram M Y).PosDef) :
    (cubeRootGram (cubeUnitRoots Y) (M+1)).PosDef := by
  rw [cubeRootGram_eq_card_smul_cubeFullGram]
  apply hG.smul
  exact_mod_cast (show (0 : ℝ) < (((M+1)^d : ℕ) : ℝ) by
    exact_mod_cast pow_pos (Nat.succ_pos M) d)

/-- The finite-frame result transferred through the actual cube whitening. -/
theorem cubeFixedSupport_lowerGram_of_whitened_thickness {d M n m : ℕ}
    (hn : 0 < n) (hm : 1 ≤ m) (hmN : m ≤ (M+1)^d)
    (Y : Fin n → Fin d → ℝ) (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : IsUnit P) (hwhite : Pᴴ * cubeRootGram (cubeUnitRoots Y) (M+1) * P = 1)
    {θ ρ ε : ℝ} (hθ : 0 < θ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (n+1)*(n-Module.finrank ℂ U)*Fintype.card (CubeFrequency d M) ≤
      2*n^2*(Finset.univ.filter (fun k : CubeFrequency d M =>
        ∀ u : U, θ < ‖cubeWhitenedFrame Y P k-(u : EuclideanSpace ℂ (Fin n))‖)).card)
    (hsample : 3*(n : ℝ)/ρ^2*Real.log ((n : ℝ)/ε) ≤ (m : ℝ)) :
    1-ε ≤ probability (fun Ω : FiniteSample (CubeFrequency d M) m =>
      CubeWeakLowerGramEvent Y θ ρ Ω) := by
  letI := hP.invertible
  let N := Fintype.card (CubeFrequency d M)
  let e := (Fintype.equivFin (CubeFrequency d M)).symm
  let f := fun k => cubeWhitenedFrame Y P (e k)
  have hN : 0 < N := by
    dsimp [N]
    rw [card_cubeFrequency]
    exact pow_pos (Nat.succ_pos M) d
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmcard : m ≤ N := by simpa [N] using hmN
  have hMean : mean (fun k => cubeFourierPopulation Y (e k)) = cubeFullGram M Y := by
    rw [← finiteMean_fin, finiteMean_comp_equiv e, cubeFullGram]
  have hFrame : framePopulation f = fun k => (N : ℂ) •
      (Pᴴ * cubeFourierPopulation Y (e k) * P) := by
    funext k
    simpa only [f, N, card_cubeFrequency] using cubeWhitenedFrame_population Y P e k
  have hfull : mean (framePopulation f) = 1 := by
    rw [hFrame]
    change mean (fun k => ((N : ℝ) : ℂ) •
      (Pᴴ * cubeFourierPopulation Y (e k) * P)) = 1
    rw [mean_real_smul, mean_congruence, hMean]
    rw [cubeRootGram_eq_card_smul_cubeFullGram] at hwhite
    simpa only [Matrix.mul_smul, Matrix.smul_mul, N, card_cubeFrequency, Complex.ofReal_natCast] using hwhite
  have hthick' : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (n+1)*(n-Module.finrank ℂ U)*N ≤
      2*n^2*(Finset.univ.filter (fun k =>
        ∀ u : U, θ < ‖f k-(u : EuclideanSpace ℂ (Fin n))‖)).card := by
    intro U
    have hc := Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl) :
      {i : Fin N // ∀ u : U, θ < ‖f i-(u : EuclideanSpace ℂ (Fin n))‖} ≃
      {k : CubeFrequency d M // ∀ u : U, θ < ‖cubeWhitenedFrame Y P k-(u : EuclideanSpace ℂ (Fin n))‖})
    simp only [Fintype.card_subtype] at hc
    have hh := hthick U
    rw [← hc] at hh
    exact hh
  have hprob := sampleMean_thick_frame_lower_bound_probability hN hn hm hmcard f hfull
    hθ hρ0 hρ1 hε hthick' hsample
  rw [← probability_comp_equiv (finiteSampleEquiv e m) (CubeWeakLowerGramEvent Y θ ρ)]
  apply hprob.trans
  apply probability_mono
  intro Ω hΩ x
  let y := P⁻¹.toEuclideanLin x
  have hxy : P.toEuclideanLin y = x := by
    change (P.toEuclideanLin ∘ₗ P⁻¹.toEuclideanLin) x = x
    rw [← Matrix.toLpLin_mul_same, Matrix.mul_inv_of_invertible]
    simp
  have hmetric : ‖y‖^2 = (N : ℝ)*FiniteMatrixSampling.quadratic (cubeFullGram M Y) x := by
    have he := congrArg (fun A => FiniteMatrixSampling.quadratic A y) hwhite
    rw [quadratic_identity, quadratic_congruence] at he
    rw [cubeRootGram_eq_card_smul_cubeFullGram, hxy] at he
    simpa only [← Complex.ofReal_natCast, quadratic_smul_matrix, N, card_cubeFrequency] using he.symm
  have hSample : sampleMean (framePopulation f) Ω =
      (N : ℂ) • (Pᴴ * finiteSampleMean (cubeFourierPopulation Y)
        (finiteSampleEquiv e m Ω) * P) := by
    rw [hFrame]
    change sampleMean (fun k => ((N : ℝ) : ℂ) •
      (Pᴴ*cubeFourierPopulation Y (e k)*P)) Ω = _
    rw [sampleMean_real_smul, sampleMean_congruence]
    rw [← finiteSampleMean_fin, finiteSampleMean_comp_equiv]
    simp only [Complex.ofReal_natCast]
  have hy := hΩ y
  rw [hSample, hmetric] at hy
  simp only [← Complex.ofReal_natCast] at hy
  rw [quadratic_smul_matrix, quadratic_congruence, hxy] at hy
  change ((1-ρ)/2)*thickFrameDetFloor n θ*FiniteMatrixSampling.quadratic (cubeFullGram M Y) x ≤ _
  apply (mul_le_mul_iff_right₀ hNR).mp
  convert hy using 1 <;> first | rfl | ring


/-- The uniform sampling coefficient depends only on dimension and node count. -/
def cubeWeakSamplingCoefficient (d n : ℕ) : ℝ :=
  Real.sqrt (thickFrameDetFloor n (CubeFrameThickness.cubeFrameThreshold d n)/2)

theorem cubeWeakSamplingCoefficient_pos (d n : ℕ) :
    0 < cubeWeakSamplingCoefficient d n := by
  exact Real.sqrt_pos.mpr (div_pos (thickFrameDetFloor_pos n _) (by norm_num))

/-- The actual Fourier cube has sufficient uniform subspace thickness. -/
theorem cubeFixedSupport_weak_lowerGram_probability {d L n m : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hL : 2*n ≤ L)
    (hm : 1 ≤ m) (hmN : m ≤ (L+1)^d) (Y : Fin n → Fin d → ℝ)
    (hG : (cubeFullGram L Y).PosDef)
    {ρ ε : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (hsample : 3*(n : ℝ)/ρ^2*Real.log ((n : ℝ)/ε) ≤ (m : ℝ)) :
    1-ε ≤ probability (fun Ω : FiniteSample (CubeFrequency d L) m =>
      CubeWeakLowerGramEvent Y (CubeFrameThickness.cubeFrameThreshold d n) ρ Ω) := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨P, hP, hwhite⟩ := exists_whitening_matrix
    (cubeRootGram (cubeUnitRoots Y) (L+1)) (cubeRootGram_posDef_of_cubeFullGram Y hG)
  apply cubeFixedSupport_lowerGram_of_whitened_thickness hn hm hmN Y P hP hwhite
    (CubeFrameThickness.threshold_pos hd hn) hρ0 hρ1 hε _ hsample
  intro U
  have hc := CubeFrameThickness.cubeFrameRow_thickCard (cubeUnitRoots Y) P hP hwhite
    (norm_cubeUnitRoots Y) hn hL U
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, card_cubeFrequency,
    cubeWhitenedFrame, CubeFrameThickness.cubeFrameRow,
    TranslatedBasisThickness.FarFromSubspace] using hc

/-- Minimum singular value under uniform sampling with a rate proportional to n. -/
theorem cubeFixedSupport_weak_minSingularValue_probability {d L n m : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hL : 8*n ≤ L)
    (hm : 1 ≤ m) (hmN : m ≤ (L+1)^d) (Y : Fin n → Fin d → ℝ)
    (hG : (cubeFullGram L Y).PosDef)
    {ρ ε : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (hsample : 3*(n : ℝ)/ρ^2*Real.log ((n : ℝ)/ε) ≤ (m : ℝ)) :
    1-ε ≤ probability (fun Ω : FiniteSample (CubeFrequency d L) m =>
      Real.sqrt (1-ρ)*cubeWeakSamplingCoefficient d n *
        matrixSingularValue (cubeFullVandermonde L Y) (n-1) ≤
        matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (n-1)) := by
  have hp := cubeFixedSupport_weak_lowerGram_probability hd hn (by omega : 2*n ≤ L)
    hm hmN Y hG hρ0 hρ1 hε hsample
  apply hp.trans
  apply probability_mono
  intro Ω hΩ
  have hmin := cubeWeakLowerGramEvent_singularValue Y hρ1.le Ω hΩ (by omega : n-1 < n)
  have he : ((1-ρ)/2)*thickFrameDetFloor n (CubeFrameThickness.cubeFrameThreshold d n) =
      (1-ρ)*(thickFrameDetFloor n (CubeFrameThickness.cubeFrameThreshold d n)/2) := by ring
  rw [he, Real.sqrt_mul (sub_nonneg.mpr hρ1.le)] at hmin
  exact hmin

end
end LeanNumDetect.RandSamp
