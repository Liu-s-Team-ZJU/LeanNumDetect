import General.Fourier.CubeGreedyFrameBounds
import General.Probability.GreedyThickFrameSampling
import RandSamp.CubeFrameNormalization

/-! Uniform Fourier-cube sampling through greedy accepted bases. The constants
and the dimension-only sample budget are those of the manuscript's Appendix C. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling CubeShiftBounds FrameMatrixBounds CubeGreedyFrameBounds
open CubeFrameBasis TranslatedBasisThickness

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The retained fraction of normalized full-cube Gram energy. -/
def cubeGreedySamplingThreshold (d n : ℕ) : ℝ :=
  greedySamplingThreshold n (cubeGreedyEnergy d n)

/-- The singular-value coefficient of the greedy cube sampler. -/
def cubeGreedySamplingCoefficient (d n : ℕ) : ℝ :=
  Real.sqrt (cubeGreedySamplingThreshold d n)

theorem cubeGreedySamplingThreshold_pos {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    0 < cubeGreedySamplingThreshold d n :=
  greedySamplingThreshold_pos hn (cubeGreedyEnergy_pos hd hn)

theorem cubeGreedySamplingCoefficient_pos {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    0 < cubeGreedySamplingCoefficient d n :=
  Real.sqrt_pos.mpr (cubeGreedySamplingThreshold_pos hd hn)

/-- Relative lower energy of the original sampled Fourier rows. -/
def CubeGreedyLowerGramEvent {d L n m : ℕ} (Y : Fin n → Fin d → ℝ)
    (Ω : FiniteSample (CubeFrequency d L) m) : Prop :=
  ∀ x : EuclideanSpace ℂ (Fin n),
    cubeGreedySamplingThreshold d n * FiniteMatrixSampling.quadratic (cubeFullGram L Y) x ≤
      FiniteMatrixSampling.quadratic (finiteSampleMean (cubeFourierPopulation Y) Ω) x

/-- Lower Gram order transfers to every ordered singular value. -/
theorem cubeGreedyLowerGramEvent_singularValue {d L n m : ℕ}
    (hd : 0 < d) (hn : 0 < n) (Y : Fin n → Fin d → ℝ)
    (Ω : FiniteSample (CubeFrequency d L) m) (hrelative : CubeGreedyLowerGramEvent Y Ω)
    {i : ℕ} (hi : i < n) :
    cubeGreedySamplingCoefficient d n * matrixSingularValue (cubeFullVandermonde L Y) i ≤
      matrixSingularValue (cubeSampledVandermonde m Y Ω.val) i := by
  let κ := cubeGreedySamplingThreshold d n
  have hκ : 0 ≤ κ := (cubeGreedySamplingThreshold_pos hd hn).le
  have he : 1 - (1 - κ) = κ := by ring
  have hh : CubeLowerGramEvent Y (1 - κ) Ω := by
    intro x
    rw [he]
    exact hrelative x
  have h := cubeLowerGramEvent_singularValue Y (ρ := 1 - κ) (by linarith) Ω hh hi
  rw [he] at h
  exact h

/-- The finite thick-frame theorem transferred through the actual cube whitening. -/
theorem cubeFixedSupport_greedy_lowerGram_probability {d L n m : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hL : 2 * n ≤ L)
    (hm : 1 ≤ m) (hmN : m ≤ (L + 1) ^ d) (Y : Fin n → Fin d → ℝ)
    (hG : (cubeFullGram L Y).PosDef) {ε : ℝ} (hε : 0 < ε)
    (hsample : 3 * (n : ℝ) * Real.log ((n : ℝ) / ε) ≤ (m : ℝ)) :
    1 - ε ≤ probability (fun Ω : FiniteSample (CubeFrequency d L) m =>
      CubeGreedyLowerGramEvent Y Ω) := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨P, hP, hwhite⟩ := exists_whitening_matrix
    (cubeRootGram (cubeUnitRoots Y) (L + 1)) (cubeRootGram_posDef_of_cubeFullGram Y hG)
  letI := hP.invertible
  let N := Fintype.card (CubeFrequency d L)
  let e := (Fintype.equivFin (CubeFrequency d L)).symm
  let f := fun k => cubeWhitenedFrame Y P (e k)
  have hN : 0 < N := by
    dsimp [N]
    rw [card_cubeFrequency]
    exact pow_pos (Nat.succ_pos L) d
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmcard : m ≤ N := by simpa [N] using hmN
  have hnorm : ∀ k, ‖f k‖ ≤ cubeFrameUpperConstant d n := by
    intro k
    exact cubeFrameRow_norm_le (cubeUnitRoots Y) P hP hwhite (norm_cubeUnitRoots Y) hn hL (e k)
  have hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      ((n : ℝ) - Module.finrank ℂ U) / (2 * n) ≤
        probability (fun k => FarFromSubspace (f k) U (cubeFrameThreshold d n)) := by
    intro U
    have hh := cubeFrameRow_probability_far_real (cubeUnitRoots Y) P hP hwhite
      (norm_cubeUnitRoots Y) hn hL U
    rw [← probability_comp_equiv e] at hh
    exact hh
  have hprob := sampleMean_greedy_thick_frame_probability hN hn
    (threshold_pos hd hn) (threshold_le_upperConstant hn) f hnorm hthick
    hm hmcard hε hsample
  have hFrame : framePopulation f = fun k => (N : ℂ) •
      (Pᴴ * cubeFourierPopulation Y (e k) * P) := by
    funext k
    simpa only [f, N, card_cubeFrequency] using cubeWhitenedFrame_population Y P e k
  rw [← probability_comp_equiv (finiteSampleEquiv e m) (CubeGreedyLowerGramEvent Y)]
  apply hprob.trans
  apply probability_mono
  intro Ω hΩ x
  let y := P⁻¹.toEuclideanLin x
  have hxy : P.toEuclideanLin y = x := by
    change (P.toEuclideanLin ∘ₗ P⁻¹.toEuclideanLin) x = x
    rw [← Matrix.toLpLin_mul_same, Matrix.mul_inv_of_invertible]
    simp
  have hmetric : ‖y‖ ^ 2 = (N : ℝ) * FiniteMatrixSampling.quadratic (cubeFullGram L Y) x := by
    have he := congrArg (fun A => FiniteMatrixSampling.quadratic A y) hwhite
    rw [quadratic_identity, quadratic_congruence] at he
    rw [cubeRootGram_eq_card_smul_cubeFullGram, hxy] at he
    simpa only [← Complex.ofReal_natCast, quadratic_smul_matrix, N, card_cubeFrequency]
      using he.symm
  have hSample : sampleMean (framePopulation f) Ω =
      (N : ℂ) • (Pᴴ * finiteSampleMean (cubeFourierPopulation Y)
        (finiteSampleEquiv e m Ω) * P) := by
    rw [hFrame]
    change sampleMean (fun k => ((N : ℝ) : ℂ) •
      (Pᴴ * cubeFourierPopulation Y (e k) * P)) Ω = _
    rw [sampleMean_real_smul, sampleMean_congruence]
    rw [← finiteSampleMean_fin, finiteSampleMean_comp_equiv]
    simp only [Complex.ofReal_natCast]
  have hy := hΩ y
  rw [hSample, hmetric] at hy
  simp only [← Complex.ofReal_natCast] at hy
  rw [quadratic_smul_matrix, quadratic_congruence, hxy] at hy
  change cubeGreedySamplingThreshold d n * FiniteMatrixSampling.quadratic (cubeFullGram L Y) x ≤ _
  apply (mul_le_mul_iff_right₀ hNR).mp
  convert hy using 1 <;> first | rfl | (dsimp [cubeGreedySamplingThreshold, cubeGreedyEnergy]; ring)

/-- The logarithmic sample budget gives the explicit minimum singular-value bound. -/
theorem cubeFixedSupport_greedy_minSingularValue_probability {d L n m : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hL : 8 * n ≤ L)
    (hm : 1 ≤ m) (hmN : m ≤ (L + 1) ^ d) (Y : Fin n → Fin d → ℝ)
    (hG : (cubeFullGram L Y).PosDef) {ε : ℝ} (hε : 0 < ε)
    (hsample : 3 * (n : ℝ) * Real.log ((n : ℝ) / ε) ≤ (m : ℝ)) :
    1 - ε ≤ probability (fun Ω : FiniteSample (CubeFrequency d L) m =>
      cubeGreedySamplingCoefficient d n * matrixSingularValue (cubeFullVandermonde L Y) (n - 1) ≤
        matrixSingularValue (cubeSampledVandermonde m Y Ω.val) (n - 1)) := by
  have hp := cubeFixedSupport_greedy_lowerGram_probability hd hn (by omega : 2 * n ≤ L)
    hm hmN Y hG hε hsample
  apply hp.trans
  apply probability_mono
  intro Ω hΩ
  exact cubeGreedyLowerGramEvent_singularValue hd hn Y Ω hΩ (by omega : n - 1 < n)

end
end LeanNumDetect.RandSamp
