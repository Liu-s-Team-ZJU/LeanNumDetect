import RandSamp.CubeWeakLowerSampling
import General.Probability.ThickFrameSampling
import General.Fourier.CubeFrameThickness

/-! Retained subspace-thickness sampling applications. The manuscript-facing
public sampling theorem remains in `CubeWeakLowerSampling` and uses the
logarithmic determinant average and stationary-weight construction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling CubeShiftBounds FrameMatrixBounds
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The retained subspace-thickness transfer through the actual cube whitening. -/
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


/-- The actual Fourier cube has sufficient uniform subspace thickness. -/
theorem cubeFixedSupport_thickness_lowerGram_probability {d L n m : ℕ}
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

end
end LeanNumDetect.RandSamp
