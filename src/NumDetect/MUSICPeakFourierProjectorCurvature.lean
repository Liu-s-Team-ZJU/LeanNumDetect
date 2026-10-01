import NumDetect.MUSICPeakFourierLineVector
import NumDetect.MUSICPeakProjectorCurvatureLoss
import NumDetect.MUSICPeakFourierDerivativeNorm
import NumDetect.MUSICPeakStrictConvex

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open WithLp
namespace LeanNumDetect
namespace NumDetect
noncomputable section

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Nonempty ι]
  [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private def fourierMultiplier (frequency : ι → Point d) (u : Point d) (i : ι) : ℂ :=
  Complex.I * (dot (frequency i) u : ℂ)

private def fourierLineVector (frequency : ι → Point d) (y u : Point d)
    (k : ℕ) (t : ℝ) : EuclideanSpace ℂ ι :=
  toLp 2 (fun i => (fourierMultiplier frequency u i) ^ k *
    normalizedSteering frequency (y + t • u) i)

private theorem fourierLineVector_hasDerivAt
    (frequency : ι → Point d) (y u : Point d) (k : ℕ) (t : ℝ) :
    HasDerivAt (fourierLineVector frequency y u k)
      (fourierLineVector frequency y u (k + 1) t) t := by
  have h := normalizedSteeringVector_mul_hasDerivAt_line frequency y u
    (fun i => (fourierMultiplier frequency u i) ^ k) t
  convert h using 1 <;> ext i <;>
    simp [fourierLineVector, fourierMultiplier, pow_succ, mul_assoc]


private theorem FourierLine_squaredMUSIC_contDiffAt_two
    (frequency : ι → Point d) (A : Matrix ι κ ℂ) (n : ℕ)
    (y u : Point d) (t : ℝ) :
    ContDiffAt ℝ 2 (fun s : ℝ =>
      rankNoiseSpaceCorrelation frequency A n (y + s • u) ^ 2) t := by
  have hline : ContDiff ℝ 2 (fun s : ℝ => y + s • u) := by fun_prop
  exact ((rankNoiseSpaceCorrelation_sq_contDiff_two frequency A n).comp hline).contDiffAt

/-- Projector distance controls the directional Hessian difference of finite-Fourier squared MUSIC. -/
theorem finiteFourier_squaredMUSIC_lineCurvature_perturb_abs_le
    (frequency : ι → Point d) (Aσ A₀ : Matrix ι κ ℂ) (n : ℕ)
    (y u : Point d) (p Ω : ℝ) (hp : 0 ≤ p) (hΩ : 0 ≤ Ω)
    (hproj : ∀ z : EuclideanSpace ℂ ι,
      ‖(trailingLeftSingularSubspace Aσ n).starProjection z -
        (trailingLeftSingularSubspace A₀ n).starProjection z‖ ≤ p * ‖z‖)
    (hphase : ∀ i, |dot (frequency i) u| ≤ Ω) :
    |iteratedDeriv 2 (fun s : ℝ =>
      rankNoiseSpaceCorrelation frequency Aσ n (y + s • u) ^ 2) 0 -
      iteratedDeriv 2 (fun s : ℝ =>
        rankNoiseSpaceCorrelation frequency A₀ n (y + s • u) ^ 2) 0| ≤
      4 * p * Ω ^ 2 := by
  let Sσ := trailingLeftSingularSubspace Aσ n
  let S₀ := trailingLeftSingularSubspace A₀ n
  let a := fourierLineVector frequency y u 0
  let au := fourierLineVector frequency y u 1
  let auu := fourierLineVector frequency y u 2
  have ha : ∀ s, HasDerivAt a (au s) s := by
    intro s
    exact fourierLineVector_hasDerivAt frequency y u 0 s
  have hau : ∀ s, HasDerivAt au (auu s) s := by
    intro s
    exact fourierLineVector_hasDerivAt frequency y u 1 s
  have heq (A : Matrix ι κ ℂ) :
      (fun s : ℝ => ‖(trailingLeftSingularSubspace A n).starProjection (a s)‖ ^ 2) =
      (fun s : ℝ => rankNoiseSpaceCorrelation frequency A n (y + s • u) ^ 2) := by
    funext s
    simp [a, fourierLineVector, rankNoiseSpaceCorrelation]
  have hσ : ContDiffAt ℝ 2 (fun s : ℝ => ‖Sσ.starProjection (a s)‖ ^ 2) 0 := by
    rw [heq]
    exact FourierLine_squaredMUSIC_contDiffAt_two frequency Aσ n y u 0
  have h₀ : ContDiffAt ℝ 2 (fun s : ℝ => ‖S₀.starProjection (a s)‖ ^ 2) 0 := by
    rw [heq]
    exact FourierLine_squaredMUSIC_contDiffAt_two frequency A₀ n y u 0
  have haNorm : ‖a 0‖ ≤ 1 := by
    simp [a, fourierLineVector, norm_normalizedSteering]
  have hauNorm : ‖au 0‖ ≤ Ω := by
    simpa [au, fourierLineVector, fourierMultiplier] using
      (norm_fourier_directional_derivative_vector_le
        (k := 1) frequency y u Ω hΩ hphase)
  have hauuNorm : ‖auu 0‖ ≤ Ω ^ 2 := by
    simpa [auu, fourierLineVector, fourierMultiplier] using
      (norm_fourier_directional_derivative_vector_le
        (k := 2) frequency y u Ω hΩ hphase)
  have h := starProjection_squaredCurvature_perturb_abs_le
    Sσ S₀ a au auu ha hau 0 p Ω hp hΩ hσ h₀ hproj
    haNorm hauNorm hauuNorm
  change |iteratedDeriv 2 (fun s =>
      ‖(trailingLeftSingularSubspace Aσ n).starProjection (a s)‖ ^ 2) 0 -
      iteratedDeriv 2 (fun s =>
        ‖(trailingLeftSingularSubspace A₀ n).starProjection (a s)‖ ^ 2) 0| ≤
      4 * p * Ω ^ 2 at h
  rw [heq Aσ, heq A₀] at h
  exact h


theorem finiteFourier_lineCurvature_eq_pointLine
    (frequency : ι → Point d) (A : Matrix ι κ ℂ) (n : ℕ)
    (z w : EuclideanSpace ℝ (Fin d)) :
    lineCurvature (finiteFourierSquaredMUSIC frequency A n) z w =
      iteratedDeriv 2 (fun s : ℝ =>
        rankNoiseSpaceCorrelation frequency A n (ofLp z + s • ofLp w) ^ 2) 0 := by
  simp only [lineCurvature, finiteFourierSquaredMUSIC, ofLp_add, ofLp_smul]

/-- Euclidean directional curvature version of finite-Fourier projector perturbation. -/
theorem finiteFourier_squaredMUSIC_lineCurvature_perturb_abs_le_euclidean
    (frequency : ι → Point d) (Aσ A₀ : Matrix ι κ ℂ) (n : ℕ)
    (z w : EuclideanSpace ℝ (Fin d)) (p Ω : ℝ)
    (hp : 0 ≤ p) (hΩ : 0 ≤ Ω)
    (hproj : ∀ a : EuclideanSpace ℂ ι,
      ‖(trailingLeftSingularSubspace Aσ n).starProjection a -
        (trailingLeftSingularSubspace A₀ n).starProjection a‖ ≤ p * ‖a‖)
    (hphase : ∀ i, |dot (frequency i) (ofLp w)| ≤ Ω) :
    |lineCurvature (finiteFourierSquaredMUSIC frequency Aσ n) z w -
      lineCurvature (finiteFourierSquaredMUSIC frequency A₀ n) z w| ≤
      4 * p * Ω ^ 2 := by
  rw [finiteFourier_lineCurvature_eq_pointLine,
    finiteFourier_lineCurvature_eq_pointLine]
  exact finiteFourier_squaredMUSIC_lineCurvature_perturb_abs_le
    frequency Aσ A₀ n (ofLp z) (ofLp w) p Ω hp hΩ hproj hphase


/-- A Fourier phase bound and projector gap imply the quantitative noisy curvature lower bound. -/
theorem finiteFourier_squaredMUSIC_lineCurvature_lower_of_projectorBound
    (frequency : ι → Point d) (Aσ A₀ : Matrix ι κ ℂ) (n : ℕ)
    (z w : EuclideanSpace ℝ (Fin d)) (p Ω : ℝ)
    (hp : 0 ≤ p) (hΩ : 0 ≤ Ω)
    (hproj : ∀ a : EuclideanSpace ℂ ι,
      ‖(trailingLeftSingularSubspace Aσ n).starProjection a -
        (trailingLeftSingularSubspace A₀ n).starProjection a‖ ≤ p * ‖a‖)
    (hphase : ∀ i, |dot (frequency i) (ofLp w)| ≤ Ω * ‖w‖) :
    lineCurvature (finiteFourierSquaredMUSIC frequency A₀ n) z w -
      4 * Ω ^ 2 * p * ‖w‖ ^ 2 ≤
    lineCurvature (finiteFourierSquaredMUSIC frequency Aσ n) z w := by
  have habs := finiteFourier_squaredMUSIC_lineCurvature_perturb_abs_le_euclidean
    frequency Aσ A₀ n z w p (Ω * ‖w‖) hp
    (mul_nonneg hΩ (norm_nonneg w)) hproj hphase
  have hle := (abs_le.mp habs).1
  nlinarith [show 4 * p * (Ω * ‖w‖) ^ 2 =
    4 * Ω ^ 2 * p * ‖w‖ ^ 2 by ring]


/-- Singular-subspace stability gives a Fourier directional-curvature loss with any valid singular-value lower bound. -/
theorem finiteFourier_squaredMUSIC_lineCurvature_lower_of_matrixPerturb
    (frequency : ι → Point d) (A E : Matrix ι κ ℂ) (n : ℕ)
    (hn : 0 < n) (hrows : n < Fintype.card ι)
    (hcols : n ≤ Fintype.card κ) (hrank : A.rank = n)
    (z w : EuclideanSpace ℝ (Fin d)) (G Ω : ℝ)
    (hG : 0 < G)
    (hGle : G ≤ matrixSingularValue A (n - 1))
    (hsmall : 2 * matrixSpectralNorm E < G)
    (hΩ : 0 ≤ Ω)
    (hphase : ∀ i, |dot (frequency i) (ofLp w)| ≤ Ω * ‖w‖) :
    lineCurvature (finiteFourierSquaredMUSIC frequency A n) z w -
      4 * Ω ^ 2 *
        (2 * matrixSpectralNorm E / G) * ‖w‖ ^ 2 ≤
    lineCurvature (finiteFourierSquaredMUSIC frequency (A + E) n) z w := by
  have hsmallσ : 2 * matrixSpectralNorm E <
      matrixSingularValue A (n - 1) := hsmall.trans_le hGle
  have hnonneg : 0 ≤ 2 * matrixSpectralNorm E :=
    mul_nonneg (by norm_num) (norm_nonneg _)
  have hp : 0 ≤ 2 * matrixSpectralNorm E / G :=
    div_nonneg hnonneg hG.le
  have hratio : 2 * matrixSpectralNorm E /
      matrixSingularValue A (n - 1) ≤
        2 * matrixSpectralNorm E / G :=
    div_le_div_of_nonneg_left hnonneg hG hGle
  have hproj (a : EuclideanSpace ℂ ι) :
      ‖(trailingLeftSingularSubspace (A + E) n).starProjection a -
        (trailingLeftSingularSubspace A n).starProjection a‖ ≤
      (2 * matrixSpectralNorm E / G) * ‖a‖ := by
    calc
      _ ≤ (2 * matrixSpectralNorm E /
          matrixSingularValue A (n - 1)) * ‖a‖ :=
        fixedRankTrailingLeftSingularSubspaceProjectionPerturbation
          A E n hn hrows hcols hrank hsmallσ a
      _ ≤ (2 * matrixSpectralNorm E / G) * ‖a‖ :=
        mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
  exact finiteFourier_squaredMUSIC_lineCurvature_lower_of_projectorBound
    frequency (A + E) A n z w (2 * matrixSpectralNorm E / G) Ω
    hp hΩ hproj hphase

end
end NumDetect
end LeanNumDetect
