import MultiTuran.Preliminaries.BoundFormula
import MultiTuran.FullAperture.FullAperture
import MultiTuran.SingleClump.Scaling
import MultiTuran.Norming.ProductNorming
import MultiTuran.Norming.ProductRestriction
import MultiTuran.SingleClump.ScaledRestrictionConstants

/-! # Explicit segmented-array transfer after a supremum comparison

All integration, norming, aperture scaling and singular-value steps are proved
here. The supremum comparison is an explicit premise of this reusable
assembly. `SegmentedArray` supplies it from the proved Turán theorem and
exports manuscript `lem:sv-md-array` without an extra comparison premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The literal coefficient of the manuscript follows from the stated actual
supremum comparison. That comparison is the only analytic transfer premise. -/
theorem segmentedArrayLowerBound_le_of_supNorm_comparison {d n : ℕ}
    {C_T : ℝ} (hC_T : 0 < C_T) (G : SegmentedGrid d)
    (Y : Fin n → Point d) (center : Point d) (hn : 4 ≤ n)
    (hN : 2*n ≤ G.minAperture)
    (hY : ∀ j, InOpenCube (2*Real.pi/(G.omega : ℝ)) center (Y j))
    (hblock : SegmentedBlockCondition (discretizationConstant d) G n)
    (hTuran : ∀ c : Fin n → ℂ,
      setSupNorm (exponentialSum Y c) G.apertureBox ≤
        (C_T*d/G.fillingRatio)^(n-1) *
          setSupNorm (exponentialSum Y c) G.thickening) :
    segmentedArrayLowerBound C_T G Y ≤
      matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hdR : (0 : ℝ) < d := by exact_mod_cast G.dimension_pos
  have hρ : 0 < G.fillingRatio := G.fillingRatio_pos
  have hθ : 0 ≤ nodeSeparation Y := nodeSeparation_nonneg Y
  let M : ℕ := G.minAperture/n
  let s : ℕ := n-1
  have hM : 0 < M := Nat.div_pos (by omega) hn0
  have hfull : (s+1)*M ≤ G.minAperture := by
    have hs : s+1=n := by dsimp [s]; omega
    rw [hs]
    exact Nat.mul_div_le G.minAperture n
  have hadm : FullApertureAdmissible G M s := by
    constructor
    · exact hM
    · nlinarith
    · nlinarith
  have hshort : (M : ℝ)*nodeDiameter Y ≤ Real.pi :=
    G.noWrap_of_nodes_in_open_cube Y center hn hY
  let A : ℝ := (2/(Real.pi*n))^d * G.rhoL *
    (G.fillingRatio/(C_T*d))^(n-1)
  let B : ℝ := ((G.minAperture : ℝ)/(2*n))^((d : ℝ)/2) *
    ((G.minAperture : ℝ)*nodeSeparation Y/(2*Real.pi*n))^(n-1)
  let b : ℝ := (1/Real.sqrt (n : ℝ))*A*B
  let τ : ℝ := (C_T*d/G.fillingRatio)^(n-1)
  let T : ℝ := Real.sqrt G.boxVolume * τ *
    (∏ q, Real.pi*n/(2*Real.sqrt (G.coordinateMinLength q : ℝ)))
  have hA : 0 ≤ A := by
    dsimp [A]
    have hL := G.rhoL_pos.le
    positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hTA : T*A=1 := by
    calc
      _ = (Real.sqrt G.boxVolume *
          (∏ q, Real.pi*n/(2*Real.sqrt (G.coordinateMinLength q : ℝ))) *
          ((2/(Real.pi*n))^d*G.rhoL)) *
        ((C_T*d/G.fillingRatio)^(n-1)*(G.fillingRatio/(C_T*d))^(n-1)) := by
          dsimp [T,A,τ]
          ring
      _ = 1 := by
        rw [G.scaledRestriction_normalization hn0,
          G.fillingRatio_pow_mul_inverse C_T hC_T (n-1)]
        norm_num
  have hcontinuous : ∀ c : Fin n → ℂ,
      b*Real.sqrt (∑ j, ‖c j‖^2) ≤ continuousL2Norm G Y c := by
    intro c
    have hap := fullAperture_elementary_no_wrap_L2_lower G Y c hn0 hadm
      (show n-1≤s by rfl) hshort
    rw [fullApertureWidth_eq_dilation G hfull] at hap
    have hscaled := aperture_scaled_factors_lower d G.minAperture n hn0 (by omega) hθ
    have hlower : ((1/Real.sqrt (n : ℝ))*B)*Real.sqrt (∑ j, ‖c j‖^2) ≤
        Real.sqrt (setEnergy Y c G.apertureBox) := by
      calc
        _ = (B/Real.sqrt (n : ℝ))*Real.sqrt (∑ j, ‖c j‖^2) := by ring
        _ ≤ (((M : ℝ)^((d : ℝ)/2)*
            ((M : ℝ)*nodeSeparation Y/Real.pi)^(n-1))/Real.sqrt (n : ℝ))*
            Real.sqrt (∑ j, ‖c j‖^2) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hscaled (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
        _ = (M : ℝ)^((d : ℝ)/2)/Real.sqrt (n : ℝ)*
            ((M : ℝ)*nodeSeparation Y/Real.pi)^(n-1)*Real.sqrt (∑ j, ‖c j‖^2) := by ring
        _ ≤ _ := hap
    have hupper := apertureL2_le_of_supNorm_restriction G Y c hn0 hτ (hTuran c)
    change Real.sqrt (setEnergy Y c G.apertureBox) ≤ T*continuousL2Norm G Y c at hupper
    calc
      _ = A*(((1/Real.sqrt (n : ℝ))*B)*Real.sqrt (∑ j, ‖c j‖^2)) := by dsimp [b]; ring
      _ ≤ A*(T*continuousL2Norm G Y c) :=
        mul_le_mul_of_nonneg_left (hlower.trans hupper) hA
      _ = (T*A)*continuousL2Norm G Y c := by ring
      _ = _ := by rw [hTA,one_mul]
  have hspectral := minimumSingularValue_ge_of_continuousNorming G Y hn0
    (by norm_num : (0 : ℝ) ≤ 1/2) hb
    (continuousNorming_half_of_localized_blockCondition G Y center hn0 hY hblock)
    (continuousEnergy_lower_of_L2_lower G Y hb hcontinuous)
  have hformula : Real.sqrt (1/2 : ℝ)*b = segmentedArrayLowerBound C_T G Y := by
    calc
      _ = (Real.sqrt (1/2 : ℝ)/Real.sqrt (n : ℝ))*A*B := by dsimp [b]; ring
      _ = (1/Real.sqrt (2*(n : ℝ)))*A*B := by rw [half_norming_sqrt_normalization]
      _ = _ := by dsimp [A,B,segmentedArrayLowerBound]; ring
  rwa [hformula] at hspectral

end
end LeanNumDetect.MultiTuran
