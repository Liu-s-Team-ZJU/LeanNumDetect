import MultiTuran.FullAperture
import MultiTuran.ProductRestriction
import MultiTuran.ScaledRestrictionConstants

/-! # The explicit multi-clump coefficient and the spectral transfer

The constants follow the order used by the manuscript: norming, product
Nikolskii, measured-set density, full aperture, and within-clump separation.
The transfer lemma keeps the actual norming, cube, and restriction statements
visible; it does not assert any of those inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Matrix WithLp Set MeasureTheory

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

def multiClumpBlockConstant (d : ℕ) (C_B : ℝ) : ℝ :=
  2^(d+2)*(d : ℝ)*C_B*(Real.sqrt 108+1)*(Real.pi/2)^(2*d)

def multiClumpNormingConstant (d n nStar : ℕ) (C_T : ℝ) : ℝ :=
  (1/(2*(n : ℝ)^2)) * (2/(Real.pi^2*(nStar : ℝ)^2))^d *
    (1/(2^d*C_T*(d : ℝ)))^(2*(nStar-1)) *
    (1+(1+(2-Real.exp (1/2 : ℝ))^(-(nStar : ℝ)/2))^nStar)^(-2 : ℤ)

def multiClumpCubeLowerBound {d : ℕ} (G : SegmentedGrid d)
    (n nStar : ℕ) (θ : ℝ) : ℝ :=
  (1/Real.sqrt ((n : ℝ)*8^nStar)) *
    ((G.minAperture : ℝ)/(6*nStar))^((d : ℝ)/2) *
    min 1 ((G.minAperture : ℝ)*θ/(8*Real.pi*nStar))^(nStar-1)

def multiClumpArrayLowerBound {d n : ℕ} (C_T : ℝ) (G : SegmentedGrid d)
    (Y : Fin n → Point d) (nStar : ℕ) : ℝ :=
  Real.sqrt (multiClumpNormingConstant d n nStar C_T / ((n : ℝ)*8^nStar)) *
    (2/(Real.pi*n))^d * G.rhoL * (G.fillingRatio/(C_T*d))^(n-1) *
    ((G.minAperture : ℝ)/(6*nStar))^((d : ℝ)/2) *
    min 1 ((G.minAperture : ℝ)*nodeSeparation Y/(8*Real.pi*nStar))^(nStar-1)

theorem multiClumpNormingConstant_nonneg (d n nStar : ℕ) (C_T : ℝ)
    (hC_T : 0 ≤ C_T) : 0 ≤ multiClumpNormingConstant d n nStar C_T := by
  unfold multiClumpNormingConstant
  positivity

theorem multiClumpCubeLowerBound_nonneg {d : ℕ} (G : SegmentedGrid d)
    (n nStar : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    0 ≤ multiClumpCubeLowerBound G n nStar θ := by
  unfold multiClumpCubeLowerBound
  positivity

/-- An arbitrary norming coefficient and any actual full-cube bound transfer
through the original product restriction chain. -/
theorem singularValue_lower_of_norming_cube_and_restriction {d n s : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d) (hn : 0 < n)
    {C_T η b : ℝ} (hC_T : 0 < C_T) (hη : 0 ≤ η) (hb : 0 ≤ b)
    (hnorming : ContinuousNorming G Y η) (hfull : s+1 ≤ G.minAperture)
    (hcube : b ≤ matrixSingularValue (fullCubeVandermonde 1 s Y) (n-1))
    (hTuran : ∀ c : Fin n → ℂ,
      setSupNorm (exponentialSum Y c) G.apertureBox ≤
        (C_T*d/G.fillingRatio)^(n-1) *
          setSupNorm (exponentialSum Y c) G.thickening) :
    Real.sqrt η * (2/(Real.pi*n))^d * G.rhoL *
      (G.fillingRatio/(C_T*d))^(n-1) * b ≤
        matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast G.dimension_pos
  let A : ℝ := (2/(Real.pi*n))^d * G.rhoL *
    (G.fillingRatio/(C_T*d))^(n-1)
  let τ : ℝ := (C_T*d/G.fillingRatio)^(n-1)
  let T : ℝ := Real.sqrt G.boxVolume * τ *
    (∏ q, Real.pi*n/(2*Real.sqrt (G.coordinateMinLength q : ℝ)))
  have hA : 0 ≤ A := by
    dsimp [A]
    have hρ := G.fillingRatio_pos.le
    have hL := G.rhoL_pos.le
    positivity
  have hτ : 0 ≤ τ := by
    dsimp [τ]
    have hρ := G.fillingRatio_pos.le
    positivity
  have hTA : T*A = 1 := by
    calc
      _ = (Real.sqrt G.boxVolume *
          (∏ q, Real.pi*n/(2*Real.sqrt (G.coordinateMinLength q : ℝ))) *
          ((2/(Real.pi*n))^d*G.rhoL)) *
        ((C_T*d/G.fillingRatio)^(n-1)*(G.fillingRatio/(C_T*d))^(n-1)) := by
          dsimp [T,A,τ]
          ring
      _ = 1 := by
        rw [G.scaledRestriction_normalization hn,
          G.fillingRatio_pow_mul_inverse C_T hC_T (n-1)]
        norm_num
  have hcontinuous : ∀ c : Fin n → ℂ,
      (A*b)*Real.sqrt (∑ j, ‖c j‖^2) ≤ continuousL2Norm G Y c := by
    intro c
    have hap := fullAperture_L2_lower_full_residue G Y c hn
      (by norm_num : 0 < (1 : ℕ)) (by simpa only [Nat.mul_one] using hfull)
    simp only [Nat.cast_one, Real.one_rpow, one_mul] at hap
    have hlower : b*Real.sqrt (∑ j, ‖c j‖^2) ≤
        Real.sqrt (setEnergy Y c G.apertureBox) :=
      (mul_le_mul_of_nonneg_right hcube (Real.sqrt_nonneg _)).trans hap
    have hupper := apertureL2_le_of_supNorm_restriction G Y c hn hτ (hTuran c)
    change Real.sqrt (setEnergy Y c G.apertureBox) ≤ T*continuousL2Norm G Y c at hupper
    calc
      _ = A*(b*Real.sqrt (∑ j, ‖c j‖^2)) := by ring
      _ ≤ A*(T*continuousL2Norm G Y c) :=
        mul_le_mul_of_nonneg_left (hlower.trans hupper) hA
      _ = (T*A)*continuousL2Norm G Y c := by ring
      _ = _ := by rw [hTA,one_mul]
  have h := minimumSingularValue_ge_of_continuousNorming G Y hn hη
    (mul_nonneg hA hb) hnorming
    (continuousEnergy_lower_of_L2_lower G Y (mul_nonneg hA hb) hcontinuous)
  convert h using 1 <;> dsimp [A] <;> ring

/-- The literal factored manuscript formula follows from its norming
constant, its full-cube estimate, and the original restriction comparison. -/
theorem multiClumpArrayLowerBound_le_of_norming_cube_and_restriction
    {d n s nStar : ℕ} (G : SegmentedGrid d) (Y : Fin n → Point d)
    (hn : 0 < n) {C_T : ℝ} (hC_T : 0 < C_T)
    (hnorming : ContinuousNorming G Y (multiClumpNormingConstant d n nStar C_T))
    (hfull : s+1 ≤ G.minAperture)
    (hcube : multiClumpCubeLowerBound G n nStar (nodeSeparation Y) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n-1))
    (hTuran : ∀ c : Fin n → ℂ,
      setSupNorm (exponentialSum Y c) G.apertureBox ≤
        (C_T*d/G.fillingRatio)^(n-1) *
          setSupNorm (exponentialSum Y c) G.thickening) :
    multiClumpArrayLowerBound C_T G Y nStar ≤
      matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  have hη := multiClumpNormingConstant_nonneg d n nStar C_T hC_T.le
  have h := singularValue_lower_of_norming_cube_and_restriction G Y hn hC_T hη
    (multiClumpCubeLowerBound_nonneg G n nStar (nodeSeparation_nonneg Y))
    hnorming hfull hcube hTuran
  have hsqrt : Real.sqrt (multiClumpNormingConstant d n nStar C_T / ((n : ℝ)*8^nStar)) =
      Real.sqrt (multiClumpNormingConstant d n nStar C_T) /
        Real.sqrt ((n : ℝ)*8^nStar) := Real.sqrt_div hη _
  unfold multiClumpArrayLowerBound
  rw [hsqrt]
  convert h using 1 <;> unfold multiClumpCubeLowerBound <;> ring

end
end LeanNumDetect.MultiTuran.MultiClump
