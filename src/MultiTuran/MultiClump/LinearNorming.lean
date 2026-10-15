import MultiTuran.MultiClump.Norming
import MultiTuran.MultiClump.LinearGapParameters
import MultiTuran.MultiClump.TranslatedBlockRestoration
import MultiTuran.MultiClump.AnchorReconstruction
import MultiTuran.MultiClump.ContinuousCombinations

/-! # Uniform block norming under linear clump separation

Low-bandwidth anchor extraction is followed by continuous prefix reconstruction.
Only the initial anchor shifts consume measured rows; the longer shifts are
controlled by the convex sweep and the original coefficient budget.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

private theorem sampledEnergy_nonneg {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (c : Fin n → ℂ) : 0 ≤ discreteEnergy G Y c := by
  unfold discreteEnergy
  positivity

/-- The original norming coefficient with a linear largest-clump gap. -/
theorem continuousNorming_of_linear_multiclump_blocks {d n A nStar : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d)
    (C : NumDetect.ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 2 ≤ d) (hn : 0 < n) (hnStar : 0 < nStar)
    (hsurj : Function.Surjective C.label) {τ C_B : ℝ}
    (hC_B : 24 ≤ C_B) (hτ : 0 ≤ τ)
    (hsame : ∀ i j, C.label i = C.label j → ∀ q, |Y i q-Y j q| ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j →
      max τ (16*Real.pi*d*(nStar : ℝ)/G.minThickLength) <
        torusLInfDistance (Y i) (Y j))
    (hcondition : multiClumpBlockConstant d C_B * G.rowCount *
      clumpRiemannExpression d nStar G.minThickLength τ ≤ 1) :
    ContinuousNorming G Y
      (multiClumpNormingConstant d n nStar multidimensionalTuranConstant) := by
  classical
  by_cases hsingle : nStar = 1
  · apply continuousNorming_of_multiclump_blocks G Y C hd hn hnStar hsurj hC_B hτ hsame
    · simpa only [hsingle, Nat.cast_one, one_pow] using hcross
    · exact hcondition
  have hns : 2 ≤ nStar := by omega
  let K := linearGapSelectorWidthParameter G nStar
  let W := nStar*K
  let D := nStar*W+1
  have hW : 2*W < G.minThickLength := linearGapSelectorWidthParameter_fits_blocks G nStar
  have hwidth : 8*W ≤ 3*G.minThickLength := linearGapSelectorWidthParameter_eight_mul_le G nStar
  have hL : 80*(nStar : ℝ) ≤ G.minThickLength :=
    linearGap_blockCondition_minimumLength_lower G hd hns hτ hC_B hcondition
  have hK : 4*Real.pi*(7/5 : ℝ)*d/((K : ℝ)+1) ≤
      16*Real.pi*d*nStar/G.minThickLength :=
    linearGapSelectorWidthParameter_separation G hnStar hL
  have hD : nStar*W < D := by dsimp [D]; omega
  have hWD : W < D := by
    have hmul : W ≤ nStar*W := by simpa using Nat.mul_le_mul_right W hnStar
    exact hmul.trans_lt hD
  let b := (1/Real.sqrt (2-Real.exp (5/14 : ℝ)))^nStar
  let R := clumpRestorationFactor d nStar multidimensionalTuranConstant
  let T := (2*(nStar : ℝ)/3)^(nStar-1)
  let S := clumpSelectorBound nStar
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hR : 0 ≤ R := clumpRestorationFactor_nonneg _ _ _ multidimensionalTuranConstant_pos.le
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hS : 0 ≤ S := (clumpSelectorBound_pos nStar).le
  have hsel (j : Fin n) :
      ∃ P : NumDetect.SegmentedPolynomial d W 0 D,
        P.angularValue (Y j) = 1 ∧
        (∀ k, C.label k ≠ C.label j → P.angularValue (Y k) = 0) ∧ P.mass ≤ b := by
    simpa only [b, show (1/(2*(7/5 : ℝ))) = 5/14 by norm_num] using
      anchor_selector_of_torus_separated_clumps_beta C (by omega) (by omega)
        linearGapFrameParameter_admissible
        (fun i j hij => (le_max_right τ _).trans_lt (hcross i j hij)) hK hWD j
  choose g hgone hgzero hgmass using hsel
  have hthreshold := shortenedGrid_riemann_threshold G W hW hτ hC_B hcondition
  have hE (H : SegmentedGrid d) (a : Fin A) (c : Fin n → ℂ) :
      continuousEnergy H Y (fun j => if C.label j = a then c j else 0) =
        continuousEnergy H (clumpNodes Y C.label a) (clumpCoefficients c C.label a) := by
    unfold continuousEnergy setEnergy
    simp_rw [exponentialSum_filtered_eq_clump]
  have hdisc (j : Fin n) (c : Fin n → ℂ) :
      discreteEnergy (shortenedGrid G W) Y (fun k => c k*(g j).angularValue (Y k)) ≤
        b^2*discreteEnergy G Y c := by
    have h := selectorAction_energy_le G hW (g j)
      (fun r => exponentialSum Y c (G.rowPoint r))
    simp_rw [selectorAction_exponentialSum] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (NumDetect.SegmentedPolynomial.mass_nonneg _) (hgmass j) 2)
      (sampledEnergy_nonneg G Y c))
  have hclump (a : Fin A) (c : Fin n → ℂ) :
      continuousEnergy G Y (fun j => if C.label j = a then c j else 0) ≤
        (2*R*S^2)*discreteEnergy G Y c := by
    let v := clumpSize C.label a
    let e := clumpEnumeration C.label a
    let Z := clumpNodes Y C.label a
    let c₀ := clumpCoefficients c C.label a
    let p : Fin v → NumDetect.SegmentedPolynomial d W 0 D := fun j => g (e j).val
    let H := anchorRemainder (clumpSize_le C a) hD p
    let q (j : Fin v) : Fin v → ℂ :=
      fun k => c₀ k*(p j).angularValue (Z k)
    let u (i : NumDetect.SegmentedIndex d ((nStar-1)*W) 0) : Point d :=
      fun r => ((i r).2 : ℝ)
    have hv : 0 < v := clumpSize_pos_of_surjective C.label hsurj a
    have hvle : v ≤ nStar := clumpSize_le C a
    have hone (j : Fin v) : (p j).angularValue (Z j)=1 := hgone (e j).val
    have hpmass (j : Fin v) : (p j).mass ≤ b := hgmass (e j).val
    have hqlocal (j : Fin v) :
        continuousEnergy (shortenedGrid G W) Z (q j) ≤
          2*b^2*discreteEnergy G Y c := by
      let cg : Fin n → ℂ := fun k => c k*(g (e j).val).angularValue (Y k)
      have hf : (fun k => if C.label k=a then cg k else 0)=cg := by
        funext k
        by_cases hk : C.label k=a
        · simp [hk]
        · have hz := hgzero (e j).val k (by
            simpa only [e,clumpEnumeration_label C.label a j] using hk)
          simp [hk,cg,hz]
      have hq : clumpCoefficients cg C.label a=q j := rfl
      have hh := filtered_clump_norming_half (shortenedGrid G W) Y C hd hsurj hτ hsame
        hthreshold a cg
      rw [hf] at hh
      have he : continuousEnergy (shortenedGrid G W) Y cg=
          continuousEnergy (shortenedGrid G W) Z (q j) := by
        rw [← hf,hE]
        rw [hq]
      rw [he] at hh
      have hdj := hdisc (e j).val c
      change discreteEnergy (shortenedGrid G W) Y cg ≤ _ at hdj
      nlinarith only [hh,hdj]
    have hshift (i : NumDetect.SegmentedIndex d ((nStar-1)*W) 0) :
        ∀ r, u i r ≤ ((nStar : ℝ)-1)*W := by
      intro r
      have hi : (i r).2.val ≤ (nStar-1)*W := Nat.le_of_lt_succ (i r).2.isLt
      have hc : ((i r).2.val : ℝ) ≤ ((nStar-1)*W : ℕ) := by exact_mod_cast hi
      simpa only [u,Nat.cast_mul,Nat.cast_sub hnStar,Nat.cast_one] using hc
    have htranslated (j : Fin v) (i : NumDetect.SegmentedIndex d ((nStar-1)*W) 0) :
        continuousEnergy G Z (phaseCoefficients Z (q j) (u i)) ≤
          R*T^2*(2*b^2*discreteEnergy G Y c) := by
      have hr := continuousEnergy_translated_le_shortenedGrid_of_cardinality_le G hd hv hns hvle
        W hwidth Z (q j) (u i) (fun r => Nat.cast_nonneg _) (hshift i)
      have hpow : (2*(nStar : ℝ)/3)^(2*(nStar-1))=T^2 := by
        dsimp [T]
        rw [← pow_mul]
        congr 1
        omega
      rw [hpow] at hr
      exact hr.trans (mul_le_mul_of_nonneg_left (hqlocal j) (mul_nonneg hR (sq_nonneg T)))
    let σ := Fin v × NumDetect.SegmentedIndex d ((nStar-1)*W) 0
    let coeff (s : σ) : ℂ := (H s.1).coeff s.2
    let vectors (s : σ) : Fin v → ℂ := phaseCoefficients Z (q s.1) (u s.2)
    let M : ℝ := ∑ j : Fin v, (H j).mass
    have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => NumDetect.SegmentedPolynomial.mass_nonneg _
    have hmass : M ≤ ∑ j : Fin v, (1+b)^j.val := by
      exact Finset.sum_le_sum fun j _ => anchorRemainder_mass_le hvle hD p hb hpmass j
    have hbudget : T*(b*M) ≤ S := by
      have hvpow : (1+b)^v ≤ (1+b)^nStar :=
        pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1+b) hvle
      have hgeom := anchor_geometric_sum v b
      have hmass' := mul_le_mul_of_nonneg_left hmass hb
      have hbudget := linearGap_mass_budget hns
      change T*((1+b)^nStar-1) ≤ S at hbudget
      apply le_trans _ hbudget
      apply mul_le_mul_of_nonneg_left _ hT
      linarith
    have hbudgetSq : (T*(b*M))^2 ≤ S^2 :=
      pow_le_pow_left₀ (mul_nonneg hT (mul_nonneg hb hM)) hbudget 2
    have hsumcoeff : (∑ s : σ, ‖coeff s‖)=M := by
      simp only [σ,coeff,Fintype.sum_prod_type,M,NumDetect.SegmentedPolynomial.mass]
    have hreconstruct : (fun k => ∑ s : σ, coeff s*vectors s k)=c₀ := by
      funext k
      change (∑ s : Fin v × NumDetect.SegmentedIndex d ((nStar-1)*W) 0,
        (H s.1).coeff s.2 * phaseCoefficients Z (q s.1) (u s.2) k)=c₀ k
      rw [Fintype.sum_prod_type]
      have hmult (j : Fin v) :
          (∑ i : NumDetect.SegmentedIndex d ((nStar-1)*W) 0,
            (H j).coeff i*phaseCoefficients Z (q j) (u i) k) =
            (q j k)*(H j).angularValue (Z k) := by
        simpa only [u] using (multiplier_coefficients_eq_sum (H j) Z (q j) k).symm
      simp_rw [hmult]
      have hrec := anchorRemainder_reconstruction hvle hD p Z hone k
      calc
        _ = c₀ k * ∑ j : Fin v, (H j).angularValue (Z k)*(p j).angularValue (Z k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          dsimp [q]
          ring
        _ = c₀ k := by rw [hrec,mul_one]
    have hcomb := continuousEnergy_weighted_sum_le G Z coeff vectors
    rw [hreconstruct,hsumcoeff] at hcomb
    have henergy : continuousEnergy G Z c₀ ≤
        M^2*(R*T^2*(2*b^2*discreteEnergy G Y c)) := by
      apply hcomb.trans
      calc
        M*(∑ s : σ, ‖coeff s‖*continuousEnergy G Z (vectors s)) ≤
            M*(∑ s : σ, ‖coeff s‖*(R*T^2*(2*b^2*discreteEnergy G Y c))) := by
          apply mul_le_mul_of_nonneg_left _ hM
          exact Finset.sum_le_sum fun s _ =>
            mul_le_mul_of_nonneg_left (htranslated s.1 s.2) (norm_nonneg _)
        _ = _ := by rw [← Finset.sum_mul,hsumcoeff]; ring
    rw [hE G a c]
    calc
      _ ≤ M^2*(R*T^2*(2*b^2*discreteEnergy G Y c)) := henergy
      _ = (2*R*(T*(b*M))^2)*discreteEnergy G Y c := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbudgetSq (by positivity)) (sampledEnergy_nonneg G Y c)
  have hAn : (A : ℝ) ≤ n := by exact_mod_cast clumpCount_le_nodeCount C.label hsurj
  have hAsq : (A : ℝ)^2 ≤ (n : ℝ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hAn 2
  intro c
  have hde : 0 ≤ discreteEnergy G Y c := sampledEnergy_nonneg G Y c
  have henergy : continuousEnergy G Y c ≤
      (2*(n : ℝ)^2*R*S^2)*discreteEnergy G Y c := by
    calc
      _ ≤ (A : ℝ)*∑ a : Fin A, continuousEnergy G Y
          (fun j => if C.label j=a then c j else 0) := continuousEnergy_le_clump_sum G Y C.label c
      _ ≤ (A : ℝ)*∑ _a : Fin A, (2*R*S^2)*discreteEnergy G Y c :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hclump a c)) (Nat.cast_nonneg _)
      _ = (2*(A : ℝ)^2*R*S^2)*discreteEnergy G Y c := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
      _ ≤ _ := by
        calc
          _ = (A : ℝ)^2*(2*R*S^2*discreteEnergy G Y c) := by ring
          _ ≤ (n : ℝ)^2*(2*R*S^2*discreteEnergy G Y c) :=
            mul_le_mul_of_nonneg_right hAsq (by positivity)
          _ = _ := by ring
  have hη := multiClumpNormingConstant_nonneg d n nStar multidimensionalTuranConstant
    multidimensionalTuranConstant_pos.le
  calc
    _ ≤ multiClumpNormingConstant d n nStar multidimensionalTuranConstant *
        ((2*(n : ℝ)^2*R*S^2)*discreteEnergy G Y c) := mul_le_mul_of_nonneg_left henergy hη
    _ = (multiClumpNormingConstant d n nStar multidimensionalTuranConstant *
        (2*(n : ℝ)^2*R*S^2))*discreteEnergy G Y c := by ring
    _ = discreteEnergy G Y c := by
      rw [multiClumpNormingConstant_mul_energy_loss (by omega) hn hnStar
        multidimensionalTuranConstant_pos,one_mul]

end
end LeanNumDetect.MultiTuran.MultiClump
