import MultiTuran.MultiClump.ClumpSums
import MultiTuran.MultiClump.BlockRestoration
import MultiTuran.MultiClump.BlockParameters
import MultiTuran.MultiClump.BlockFeasibility
import MultiTuran.MultiClump.NormingConstants
import MultiTuran.MultiClump.Selectors
import MultiTuran.MultiClump.Convolution

/-! # Uniform multi-clump norming from the literal block and clump geometry

The local sums are reindexed by their actual cardinalities. Restoration,
Riemann norming, and the explicitly constructed finite selectors give the
same energy loss as in the manuscript. No selector, restoration, or norming
conclusion is assumed as an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

private theorem one_le_turanConstant : 1 ≤ multidimensionalTuranConstant := by
  have he := Real.add_one_le_exp (1000000 : ℝ)
  have hp : 0 ≤ 2*Real.exp 1*oneDimensionalPruningWeakConstant := by
    exact mul_nonneg (by positivity) oneDimensionalPruningWeakConstant_pos.le
  unfold multidimensionalTuranConstant oneDimensionalTuranConstant
  linarith

/-- The restoration coefficient is increasing in the number of terms. -/
theorem clumpRestorationFactor_mono {d v nStar : ℕ} (hd : 0 < d)
    (hv : v ≤ nStar) :
    clumpRestorationFactor d v multidimensionalTuranConstant ≤
      clumpRestorationFactor d nStar multidimensionalTuranConstant := by
  have hvR : (v : ℝ) ≤ nStar := by exact_mod_cast hv
  have hbase : (1 : ℝ) ≤ 2^d*multidimensionalTuranConstant*(d : ℝ) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) one_le_turanConstant)
      (by exact_mod_cast hd)
  have hfirst : (Real.pi*v/2)^(2*d) ≤ (Real.pi*nStar/2)^(2*d) := by
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvR Real.pi_pos.le)
      (by norm_num)
  have hexponent : 2*(v-1) ≤ 2*(nStar-1) := by omega
  have hsecond := pow_le_pow_right₀ hbase hexponent
  unfold clumpRestorationFactor
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hfirst (by positivity)) hsecond
    (by positivity) (by positivity)

/-- Restore the actual filtered clump from all shortened blocks, using its
true cardinality and then the uniform largest-clump coefficient. -/
theorem filtered_clump_energy_le_shortenedGrid {d n A nStar : ℕ}
    (G : SegmentedGrid d) (W : ℕ) (hW : 2*W < G.minThickLength)
    (Y : Fin n → Point d) (C : NumDetect.ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 0 < d) (hsurj : Function.Surjective C.label) (a : Fin A) (c : Fin n → ℂ) :
    continuousEnergy G Y (fun j => if C.label j = a then c j else 0) ≤
      clumpRestorationFactor d nStar multidimensionalTuranConstant *
        continuousEnergy (shortenedGrid G W) Y (fun j => if C.label j = a then c j else 0) := by
  have hv := clumpSize_pos_of_surjective C.label hsurj a
  have hE (H : SegmentedGrid d) :
      continuousEnergy H Y (fun j => if C.label j = a then c j else 0) =
        continuousEnergy H (clumpNodes Y C.label a) (clumpCoefficients c C.label a) := by
    unfold continuousEnergy setEnergy
    simp_rw [exponentialSum_filtered_eq_clump]
  rw [hE G, hE (shortenedGrid G W)]
  have hr := continuousEnergy_le_shortenedGrid G W hW hv
    (clumpNodes Y C.label a) (clumpCoefficients c C.label a)
  change continuousEnergy G (clumpNodes Y C.label a) (clumpCoefficients c C.label a) ≤
    clumpRestorationFactor d (clumpSize C.label a) multidimensionalTuranConstant *
      continuousEnergy (shortenedGrid G W) (clumpNodes Y C.label a)
        (clumpCoefficients c C.label a) at hr
  exact hr.trans (mul_le_mul_of_nonneg_right
    (clumpRestorationFactor_mono hd (clumpSize_le C a)) (continuousEnergy_nonneg _ _ _))

/-- All input hypotheses are geometric or the displayed `B_d` sampling
condition. This version uses ordinary short-clump representatives; integer
lifts are handled by the final theorem's separate geometry step. The
cross-clump hypothesis states both separation above the clump diameter
`τ` and separation at the block-resolution threshold, without introducing
an independent separation parameter. -/
theorem continuousNorming_of_multiclump_blocks {d n A nStar : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d)
    (C : NumDetect.ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 2 ≤ d) (hn : 0 < n) (hnStar : 0 < nStar)
    (hsurj : Function.Surjective C.label) {τ C_B : ℝ}
    (hC_B : 24 ≤ C_B) (hτ : 0 ≤ τ)
    (hsame : ∀ i j, C.label i = C.label j → ∀ q, |Y i q-Y j q| ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j →
      max τ (16*Real.pi*d*(nStar : ℝ)^2/G.minThickLength) <
        torusLInfDistance (Y i) (Y j))
    (hcondition : multiClumpBlockConstant d C_B * G.rowCount *
      clumpRiemannExpression d nStar G.minThickLength τ ≤ 1) :
    ContinuousNorming G Y
      (multiClumpNormingConstant d n nStar multidimensionalTuranConstant) := by
  classical
  have hd0 : 0 < d := by omega
  have hL : (0 : ℝ) < G.minThickLength := by exact_mod_cast minThickLength_pos G
  let separation := 16*Real.pi*d*(nStar : ℝ)^2/G.minThickLength
  have hseparation : 0 < separation := by dsimp [separation]; positivity
  have hseparationπ : separation ≤ Real.pi :=
    blockCondition_separationThreshold_le_pi G hnStar hτ hC_B hcondition
  have hgap : 16*Real.pi*d*(nStar : ℝ)^2 ≤ separation*G.minThickLength := by
    dsimp [separation]
    rw [div_mul_cancel₀ _ hL.ne']
  have hcrossSeparation (i j : Fin n) (hij : C.label i ≠ C.label j) :
      separation < torusLInfDistance (Y i) (Y j) :=
    (le_max_right τ separation).trans_lt (hcross i j hij)
  let K := selectorWidthParameter d separation
  let W := nStar*(nStar*K)
  have hW : 2*W < G.minThickLength := by
    simpa only [W, K, pow_two, Nat.mul_assoc] using
      selector_width_fits_blocks G hd hnStar hseparation hseparationπ hgap
  have hK : 4*Real.pi*d/((K : ℝ)+1) ≤ separation :=
    selectorWidthParameter_separation hd0 hseparation
  have hsel (a : Fin A) :
      ∃ P : NumDetect.SegmentedPolynomial d W 0 (W+1),
        (∀ j, P.angularValue (Y j) = if C.label j = a then 1 else 0) ∧
          P.mass ≤ clumpSelectorBound nStar := by
    exact clump_selector_of_torus_separated_clumps C (by omega) (by omega)
      hcrossSeparation hK (by change W < W+1; omega) a
  choose P hP hmass using hsel
  have hthreshold := shortenedGrid_riemann_threshold G W hW hτ hC_B hcondition
  have hhalf (a : Fin A) (c : Fin n → ℂ) :
      continuousEnergy (shortenedGrid G W) Y (fun j => if C.label j = a then c j else 0) ≤
        2*discreteEnergy (shortenedGrid G W) Y (fun j => if C.label j = a then c j else 0) := by
    have h := filtered_clump_norming_half (shortenedGrid G W) Y C hd hsurj hτ hsame
      hthreshold a c
    linarith
  have hdiscrete (a : Fin A) (c : Fin n → ℂ) :
      discreteEnergy (shortenedGrid G W) Y (fun j => if C.label j = a then c j else 0) ≤
        (clumpSelectorBound nStar)^2*discreteEnergy G Y c := by
    have h := clump_discreteEnergy_le_of_selector G hW (P a) Y C.label a (hP a) c
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (NumDetect.SegmentedPolynomial.mass_nonneg _) (hmass a) 2)
      (by unfold discreteEnergy; positivity))
  let R := clumpRestorationFactor d nStar multidimensionalTuranConstant
  let S := clumpSelectorBound nStar
  have hR : 0 ≤ R := clumpRestorationFactor_nonneg _ _ _ multidimensionalTuranConstant_pos.le
  have hclump (a : Fin A) (c : Fin n → ℂ) :
      continuousEnergy G Y (fun j => if C.label j = a then c j else 0) ≤
        (2*R*S^2)*discreteEnergy G Y c := by
    calc
      _ ≤ R*continuousEnergy (shortenedGrid G W) Y
          (fun j => if C.label j = a then c j else 0) :=
        filtered_clump_energy_le_shortenedGrid G W hW Y C hd0 hsurj a c
      _ ≤ R*(2*discreteEnergy (shortenedGrid G W) Y
          (fun j => if C.label j = a then c j else 0)) :=
        mul_le_mul_of_nonneg_left (hhalf a c) hR
      _ ≤ R*(2*(S^2*discreteEnergy G Y c)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hdiscrete a c) (by norm_num)) hR
      _ = _ := by ring
  have hAn : (A : ℝ) ≤ n := by exact_mod_cast clumpCount_le_nodeCount C.label hsurj
  have hAsq : (A : ℝ)^2 ≤ (n : ℝ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hAn 2
  intro c
  have henergy : continuousEnergy G Y c ≤
      (2*(n : ℝ)^2*R*S^2)*discreteEnergy G Y c := by
    calc
      _ ≤ (A : ℝ)*∑ a : Fin A, continuousEnergy G Y
          (fun j => if C.label j = a then c j else 0) := continuousEnergy_le_clump_sum G Y C.label c
      _ ≤ (A : ℝ)*∑ _a : Fin A, (2*R*S^2)*discreteEnergy G Y c :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hclump a c)) (Nat.cast_nonneg _)
      _ = (2*(A : ℝ)^2*R*S^2)*discreteEnergy G Y c := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ _ := by
        have hD : 0 ≤ discreteEnergy G Y c := by unfold discreteEnergy; positivity
        calc
          _ = (A : ℝ)^2*(2*R*S^2*discreteEnergy G Y c) := by ring
          _ ≤ (n : ℝ)^2*(2*R*S^2*discreteEnergy G Y c) :=
            mul_le_mul_of_nonneg_right hAsq (by positivity)
          _ = _ := by ring
  have hη : 0 ≤ multiClumpNormingConstant d n nStar multidimensionalTuranConstant :=
    multiClumpNormingConstant_nonneg _ _ _ _ multidimensionalTuranConstant_pos.le
  calc
    _ ≤ multiClumpNormingConstant d n nStar multidimensionalTuranConstant *
        ((2*(n : ℝ)^2*R*S^2)*discreteEnergy G Y c) :=
      mul_le_mul_of_nonneg_left henergy hη
    _ = (multiClumpNormingConstant d n nStar multidimensionalTuranConstant *
        (2*(n : ℝ)^2*R*S^2))*discreteEnergy G Y c := by ring
    _ = discreteEnergy G Y c := by
      rw [multiClumpNormingConstant_mul_energy_loss hd0 hn hnStar multidimensionalTuranConstant_pos,
        one_mul]

end
end LeanNumDetect.MultiTuran.MultiClump
