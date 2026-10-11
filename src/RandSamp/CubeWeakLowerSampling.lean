import General.Probability.LogarithmicFrameSampling
import RandSamp.CubeFrameNormalization
import General.Fourier.CubeFrameLogDet
import RandSamp.MultidimensionalMultiClumpSampling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling CubeShiftBounds FrameMatrixBounds
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Relative lower energy of the original sampled Fourier rows. -/
def CubeWeakLowerGramEvent {d M n m : ℕ} (Y : Fin n → Fin d → ℝ) (θ ρ : ℝ)
    (Ω : FiniteSample (CubeFrequency d M) m) : Prop :=
  ∀ z : EuclideanSpace ℂ (Fin n),
    ((1-ρ)/2)*logarithmicFrameFloor n θ*FiniteMatrixSampling.quadratic (cubeFullGram M Y) z ≤
      FiniteMatrixSampling.quadratic (finiteSampleMean (cubeFourierPopulation Y) Ω) z


/-- Relative lower energy transfers to every ordered singular value. -/
theorem cubeWeakLowerGramEvent_singularValue {d M n m : ℕ}
    (Y : Fin n → Fin d → ℝ) {θ ρ : ℝ} (hρ1 : ρ ≤ 1)
    (Ω : FiniteSample (CubeFrequency d M) m) (hrelative : CubeWeakLowerGramEvent Y θ ρ Ω)
    {i : ℕ} (hi : i < n) :
    Real.sqrt (((1-ρ)/2)*logarithmicFrameFloor n θ) *
      matrixSingularValue (cubeFullVandermonde M Y) i ≤
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) i := by
  let a := ((1-ρ)/2)*logarithmicFrameFloor n θ
  have ha : 0 ≤ a := mul_nonneg
    (div_nonneg (sub_nonneg.mpr hρ1) (by norm_num))
    (logarithmicFrameFloor_pos n θ).le
  have he : 1-(1-a) = a := by ring
  have hh : CubeLowerGramEvent Y (1-a) Ω := by
    intro z
    rw [he]
    exact hrelative z
  have h := cubeLowerGramEvent_singularValue Y (ρ := 1-a) (by linarith) Ω hh hi
  rw [he] at h
  exact h

/-- The finite-frame result transferred through the actual cube whitening. -/
theorem cubeFixedSupport_lowerGram_of_whitened_entropy {d M n m : ℕ}
    (hn : 0 < n) (hm : 1 ≤ m) (hmN : m ≤ (M+1)^d)
    (Y : Fin n → Fin d → ℝ) (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : IsUnit P) (hwhite : Pᴴ * cubeRootGram (cubeUnitRoots Y) (M+1) * P = 1)
    {θ ρ ε : ℝ} (hθ : 0 < θ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (hentropy : ∀ (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef),
      (6 / 5 : ℝ) * (∑ j,
        Real.log (1 + θ ^ 2 * hH.isHermitian.eigenvalues j / ((12 / 5 : ℝ) * n))) ≤
        (Fintype.card (CubeFrequency d M) : ℝ)⁻¹ *
          ∑ k, smoothEntropy ((12 / 5 : ℝ) * n) (FiniteMatrixSampling.quadratic H (cubeWhitenedFrame (M := M) Y P k)))
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
  have hentropy' : ∀ (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef),
      (6 / 5 : ℝ) * (∑ j,
        Real.log (1 + θ ^ 2 * hH.isHermitian.eigenvalues j / ((12 / 5 : ℝ) * n))) ≤
        (N : ℝ)⁻¹ * ∑ k, smoothEntropy ((12 / 5 : ℝ) * n) (FiniteMatrixSampling.quadratic H (f k)) := by
    intro H hH
    have hs := Equiv.sum_comp e (fun k =>
      smoothEntropy ((12 / 5 : ℝ) * n) (FiniteMatrixSampling.quadratic H (cubeWhitenedFrame (M := M) Y P k)))
    have hh := hentropy H hH
    rw [← hs] at hh
    exact hh
  have hprob := sampleMean_logarithmic_frame_lower_bound_probability hN hn hm hmcard f hfull
    hθ hρ0 hρ1 hε hentropy' hsample
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
  change ((1-ρ)/2)*logarithmicFrameFloor n θ*FiniteMatrixSampling.quadratic (cubeFullGram M Y) x ≤ _
  apply (mul_le_mul_iff_right₀ hNR).mp
  convert hy using 1 <;> first | rfl | ring


/-- The uniform sampling coefficient depends only on dimension and node count. -/
def cubeWeakSamplingCoefficient (d n : ℕ) : ℝ :=
  Real.sqrt (logarithmicFrameFloor n (CubeFrameBasis.cubeFrameThreshold d n)/2)

theorem cubeWeakSamplingCoefficient_pos (d n : ℕ) :
    0 < cubeWeakSamplingCoefficient d n := by
  exact Real.sqrt_pos.mpr (div_pos (logarithmicFrameFloor_pos n _) (by norm_num))

/-- The actual Fourier cube has the logarithmic entropy estimate supplied by
its translated row bases. -/
theorem cubeFixedSupport_weak_lowerGram_probability {d L n m : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hL : 2*n ≤ L)
    (hm : 1 ≤ m) (hmN : m ≤ (L+1)^d) (Y : Fin n → Fin d → ℝ)
    (hG : (cubeFullGram L Y).PosDef)
    {ρ ε : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (hsample : 3*(n : ℝ)/ρ^2*Real.log ((n : ℝ)/ε) ≤ (m : ℝ)) :
    1-ε ≤ probability (fun Ω : FiniteSample (CubeFrequency d L) m =>
      CubeWeakLowerGramEvent Y (CubeFrameBasis.cubeFrameThreshold d n) ρ Ω) := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨P, hP, hwhite⟩ := exists_whitening_matrix
    (cubeRootGram (cubeUnitRoots Y) (L+1)) (cubeRootGram_posDef_of_cubeFullGram Y hG)
  apply cubeFixedSupport_lowerGram_of_whitened_entropy hn hm hmN Y P hP hwhite
    (CubeFrameBasis.threshold_pos hd hn) hρ0 hρ1 hε _ hsample
  intro A hA
  have hc := CubeFrameLogDet.cubeFrameRow_entropyMean_spectral_six_fifths
    (cubeUnitRoots Y) P hP hwhite (norm_cubeUnitRoots Y) hn hL A hA
  simpa only [card_cubeFrequency, cubeWhitenedFrame, CubeFrameBasis.cubeFrameRow] using hc

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
  have he : ((1-ρ)/2)*logarithmicFrameFloor n (CubeFrameBasis.cubeFrameThreshold d n) =
      (1-ρ)*(logarithmicFrameFloor n (CubeFrameBasis.cubeFrameThreshold d n)/2) := by ring
  rw [he, Real.sqrt_mul (sub_nonneg.mpr hρ1.le)] at hmin
  exact hmin

end
end LeanNumDetect.RandSamp
