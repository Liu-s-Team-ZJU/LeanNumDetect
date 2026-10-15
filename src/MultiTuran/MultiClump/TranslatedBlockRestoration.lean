import MultiTuran.MultiClump.ConvexSweep
import MultiTuran.MultiClump.RowShift
import MultiTuran.MultiClump.NormingConstants

/-! # Restoring finitely translated blocks with one Turán estimate

The segment-swept convex body controls a translated block without expanding
every coordinate independently.  The extra factor grows only linearly in
the number of accumulated translations, before the original Turán power.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

private theorem dimension_mul_four_fifths_pow_le (d : ℕ) :
    (d : ℝ)*(4/5 : ℝ)^d ≤ 5/3 := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    by_cases hd : d < 4
    · interval_cases d <;> norm_num
    · have hdR : (4 : ℝ) ≤ d := by exact_mod_cast (show 4 ≤ d by omega)
      calc
        ((d+1 : ℕ) : ℝ)*(4/5 : ℝ)^(d+1) =
            ((d : ℝ)+1)*(4/5)*(4/5 : ℝ)^d := by push_cast; rw [pow_succ]; ring
        _ ≤ (d : ℝ)*(4/5 : ℝ)^d := by
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ 5/3 := ih

/-- The dimension-dependent sweep loss fits in the original `2^d` factor,
leaving only `2*m/3` for the accumulated translations. -/
theorem sweep_ratio_le_original_factor {d m : ℕ} (hd : 2 ≤ d) (hm : 0 < m) :
    (8/5 : ℝ)^d * (1+3*(d : ℝ)*((m : ℝ)-1)/8) ≤ (2 : ℝ)^d*(2*m/3) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (4/5 : ℝ)^d ≤ 2/3 := by
    have h := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 4/5 by norm_num)
      (show (4/5 : ℝ) ≤ 1 by norm_num) hd
    norm_num at h ⊢
    linarith
  have hdp : 3*(d : ℝ)*(4/5 : ℝ)^d/8 ≤ 2/3 := by
    have h := dimension_mul_four_fifths_pow_le d
    nlinarith
  have hbound : (4/5 : ℝ)^d*(1+3*(d : ℝ)*((m : ℝ)-1)/8) ≤ 2*m/3 := by
    have h := mul_le_mul_of_nonneg_right hdp (sub_nonneg.mpr hmR)
    nlinarith
  have he : (8/5 : ℝ)^d = (2 : ℝ)^d*(4/5 : ℝ)^d := by
    rw [← mul_pow]
    norm_num
  rw [he, mul_assoc]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- A single rectangular restoration estimate with an arbitrary proved
upper bound for the volume of the segment sweep. -/
theorem coordinateBox_translated_energy_restoration {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) (Y : Fin n → Point d) (c : Fin n → ℂ)
    (a b b' u : Point d) (hshort : ∀ q, a q < b' q)
    (hsub : ∀ q, b' q ≤ b q) (hhalf : ∀ q, b q-a q ≤ 2*(b' q-a q))
    (hu : ∀ q, 0 ≤ u q) {F : ℝ} (hF : 0 ≤ F)
    (hratio : ((∏ q, (b q-a q))/(∏ q, (b' q-a q))) *
      (1+∑ q, u q/(b q-a q)) ≤ (2 : ℝ)^d*F) :
    setEnergy Y (phaseCoefficients Y c u) (coordinateBox a b) ≤
      (2 : ℝ)^d*(Real.pi*n/2)^(2*d)*
        ((2 : ℝ)^d*multidimensionalTuranConstant*(d : ℝ))^(2*(n-1))*
          F^(2*(n-1))*setEnergy Y c (coordinateBox a b') := by
  let V : ℝ := ∏ q, (b q-a q)
  let V' : ℝ := ∏ q, (b' q-a q)
  let T : ℝ := (2 : ℝ)^d*multidimensionalTuranConstant*(d : ℝ)*F
  let B := coordinateBoxSweep a b u
  have hfull (q : Fin d) : a q < b q := (hshort q).trans_le (hsub q)
  have hV : 0 < V := Finset.prod_pos fun q _ => sub_pos.mpr (hfull q)
  have hV' : 0 < V' := Finset.prod_pos fun q _ => sub_pos.mpr (hshort q)
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      multidimensionalTuranConstant_pos.le) (Nat.cast_nonneg d)) hF
  have hvol : V ≤ (2 : ℝ)^d*V' := by
    calc
      V ≤ ∏ q, 2*(b' q-a q) :=
        Finset.prod_le_prod (fun q _ => (sub_pos.mpr (hfull q)).le) (fun q _ => hhalf q)
      _ = (2 : ℝ)^d*V' := by rw [Finset.prod_mul_distrib]; simp [V']
  have hratioSmall : V/V' ≤ (2 : ℝ)^d := (div_le_iff₀ hV').mpr hvol
  have hBvol : (volume B).toReal ≤ V*(1+∑ q, u q/(b q-a q)) := by
    have h := coordinateBoxSweep_volume_le hd a b u hfull hu
    have hnonneg : 0 ≤ V*(1+∑ q, u q/(b q-a q)) := by
      apply mul_nonneg hV.le
      have hsum : 0 ≤ ∑ q, u q/(b q-a q) :=
        Finset.sum_nonneg fun q _ => div_nonneg (hu q) (sub_pos.mpr (hfull q)).le
      linarith
    exact (ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h).trans_eq
      (ENNReal.toReal_ofReal hnonneg)
  have hbase : multidimensionalTuranConstant*(d : ℝ)*(volume B).toReal/V' ≤ T := by
    calc
      _ ≤ multidimensionalTuranConstant*(d : ℝ)*
          (V*(1+∑ q, u q/(b q-a q)))/V' :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hBvol
          (mul_nonneg multidimensionalTuranConstant_pos.le (Nat.cast_nonneg d))) hV'.le
      _ = (multidimensionalTuranConstant*(d : ℝ))*
          ((V/V')*(1+∑ q, u q/(b q-a q))) := by ring
      _ ≤ (multidimensionalTuranConstant*(d : ℝ))*((2 : ℝ)^d*F) :=
        mul_le_mul_of_nonneg_left hratio
          (mul_nonneg multidimensionalTuranConstant_pos.le (Nat.cast_nonneg d))
      _ = T := by dsimp [T]; ring
  have hsubset : coordinateBox a b' ⊆ B := by
    apply Set.Subset.trans _ (coordinateBox_subset_sweep a b u)
    intro x hx q hq
    exact ⟨(hx q hq).1,(hx q hq).2.trans (hsub q)⟩
  have hpos : 0 < volume (coordinateBox a b') := by
    rw [coordinateBox_volume a b' (fun q => (hshort q).le)]
    exact ENNReal.ofReal_pos.mpr hV'
  have hrestr := exponentialSum_convexBody_supNorm_le hd hn
    (coordinateBoxSweep_isCompact a b u) (coordinateBoxSweep_convex a b u)
    (show MeasurableSet (coordinateBox a b') from MeasurableSet.univ_pi fun _ => measurableSet_Icc)
    hsubset hpos Y c
  rw [coordinateBox_volume_toReal a b' (fun q => (hshort q).le)] at hrestr
  have hrestr' : setSupNorm (exponentialSum Y c) B ≤
      T^(n-1)*setSupNorm (exponentialSum Y c) (coordinateBox a b') := by
    apply hrestr.trans
    apply mul_le_mul_of_nonneg_right _ (setSupNorm_nonneg _ _)
    exact pow_le_pow_left₀
      (div_nonneg (mul_nonneg (mul_nonneg multidimensionalTuranConstant_pos.le
        (Nat.cast_nonneg d)) (ENNReal.toReal_nonneg)) hV'.le) hbase (n-1)
  have hshiftSup : setSupNorm (exponentialSum Y (phaseCoefficients Y c u)) (coordinateBox a b) ≤
      setSupNorm (exponentialSum Y c) B := by
    apply Real.sSup_le
    · rintro z ⟨t,ht,rfl⟩
      change ‖exponentialSum Y (phaseCoefficients Y c u) t‖ ≤ _
      rw [exponentialSum_phaseCoefficients]
      exact norm_le_setSupNorm_on_compact _ (continuous_exponentialSum Y c)
        (coordinateBoxSweep_isCompact a b u)
        (coordinateBox_add_subset_sweep a b u ⟨t,ht,rfl⟩)
    · exact setSupNorm_nonneg _ _
  have hfullSup := hshiftSup.trans hrestr'
  have hN := coordinateBox_supNorm_sq_le hn Y c a b' hshort
  have hE := coordinateBox_energy_le_volume_mul_supNorm_sq Y (phaseCoefficients Y c u)
    a b (fun q => (hfull q).le)
  have hpow : (T^(n-1))^2 = T^(2*(n-1)) := by rw [← pow_mul]; congr 1; omega
  calc
    _ ≤ V*(T^(n-1)*setSupNorm (exponentialSum Y c) (coordinateBox a b'))^2 :=
      hE.trans (mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (setSupNorm_nonneg _ _)
          (mul_nonneg (pow_nonneg hT _) (setSupNorm_nonneg _ _))).mpr hfullSup) hV.le)
    _ = V*T^(2*(n-1))*setSupNorm (exponentialSum Y c) (coordinateBox a b')^2 := by
      rw [mul_pow,hpow]; ring
    _ ≤ V*T^(2*(n-1))*((Real.pi*n/2)^(2*d)/V'*setEnergy Y c (coordinateBox a b')) :=
      mul_le_mul_of_nonneg_left hN (mul_nonneg hV.le (pow_nonneg hT _))
    _ = (V/V')*((Real.pi*n/2)^(2*d)*T^(2*(n-1))*setEnergy Y c (coordinateBox a b')) := by ring
    _ ≤ (2 : ℝ)^d*((Real.pi*n/2)^(2*d)*T^(2*(n-1))*setEnergy Y c (coordinateBox a b')) :=
      mul_le_mul_of_nonneg_right hratioSmall
        (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hT _)) (setEnergy_nonneg Y c _))
    _ = _ := by dsimp [T]; rw [mul_pow]; ring

/-- The sweep ratio for a rectangle shortened by a common width at most
three eighths of every coordinate length. -/
theorem coordinateBox_sweep_ratio_of_width {d m : ℕ} (hd : 2 ≤ d) (hm : 0 < m)
    (a b b' u : Point d) {W : ℝ} (hW : 0 ≤ W)
    (hfull : ∀ q, a q < b q) (hshort : ∀ q, b' q=b q-W)
    (hwidth : ∀ q, 8*W ≤ 3*(b q-a q))
    (hu : ∀ q, 0 ≤ u q) (hshift : ∀ q, u q ≤ ((m : ℝ)-1)*W) :
    ((∏ q, (b q-a q))/(∏ q, (b' q-a q)))*(1+∑ q, u q/(b q-a q)) ≤
      (2 : ℝ)^d*(2*m/3) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hshortpos (q : Fin d) : 0 < b' q-a q := by rw [hshort]; linarith [hwidth q,hfull q]
  have hV : 0 < ∏ q, (b' q-a q) := Finset.prod_pos fun q _ => hshortpos q
  have hratio : (∏ q, (b q-a q))/(∏ q, (b' q-a q)) ≤ (8/5 : ℝ)^d := by
    apply (div_le_iff₀ hV).mpr
    calc
      _ ≤ ∏ q, (8/5 : ℝ)*(b' q-a q) := by
        apply Finset.prod_le_prod (fun q _ => (sub_pos.mpr (hfull q)).le)
        intro q _
        rw [hshort]
        linarith [hwidth q]
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hsum : (∑ q, u q/(b q-a q)) ≤ 3*(d : ℝ)*((m : ℝ)-1)/8 := by
    calc
      _ ≤ ∑ _q : Fin d, 3*((m : ℝ)-1)/8 := by
        apply Finset.sum_le_sum
        intro q _
        apply (div_le_iff₀ (sub_pos.mpr (hfull q))).mpr
        have h := mul_le_mul_of_nonneg_left (hwidth q) (sub_nonneg.mpr hmR)
        nlinarith [hshift q]
      _ = _ := by simp; ring
  have hnonneg : 0 ≤ 1+∑ q, u q/(b q-a q) := by
    have h := Finset.sum_nonneg fun q (_ : q ∈ Finset.univ) =>
      div_nonneg (hu q) (sub_pos.mpr (hfull q)).le
    linarith
  exact (mul_le_mul hratio (add_le_add_right hsum 1) hnonneg (by positivity)).trans
    (sweep_ratio_le_original_factor hd hm)

/-- All measured product blocks, with finitely accumulated nonnegative
translations. Only one original restoration coefficient is used. -/
theorem continuousEnergy_translated_le_shortenedGrid {d n m : ℕ}
    (G : SegmentedGrid d) (hd : 2 ≤ d) (hn : 0 < n) (hm : 0 < m)
    (W : ℕ) (hwidth : 8*W ≤ 3*G.minThickLength)
    (Y : Fin n → Point d) (c : Fin n → ℂ) (u : Point d)
    (hu : ∀ q, 0 ≤ u q) (hshift : ∀ q, u q ≤ ((m : ℝ)-1)*W) :
    continuousEnergy G Y (phaseCoefficients Y c u) ≤
      (2 : ℝ)^d*(Real.pi*n/2)^(2*d)*
        ((2 : ℝ)^d*multidimensionalTuranConstant*(d : ℝ))^(2*(n-1))*
          (2*(m : ℝ)/3)^(2*(n-1))*continuousEnergy (shortenedGrid G W) Y c := by
  have hL := minThickLength_pos G
  have hW : 2*W < G.minThickLength := by omega
  have hblock (b : ProductBlock G) :
      setEnergy Y (phaseCoefficients Y c u) (productBlockBox G b) ≤
      (2 : ℝ)^d*(Real.pi*n/2)^(2*d)*
        ((2 : ℝ)^d*multidimensionalTuranConstant*(d : ℝ))^(2*(n-1))*
          (2*(m : ℝ)/3)^(2*(n-1))*setEnergy Y c (productBlockBox (shortenedGrid G W) b) := by
    let a : Point d := fun q => (G.start q (b q) : ℝ)
    let z : Point d := fun q => ((G.start q (b q)+G.thickLength q (b q) : ℕ) : ℝ)
    let z' : Point d := fun q => ((G.start q (b q)+(shortenedGrid G W).thickLength q (b q) : ℕ) : ℝ)
    have hfull (q : Fin d) : a q < z q := by
      dsimp [a,z]
      push_cast
      have hp : 0 < G.thickLength q (b q) := by unfold SegmentedGrid.thickLength; omega
      exact lt_add_of_pos_right _ (by exact_mod_cast hp)
    have hshort (q : Fin d) : a q < z' q := by
      dsimp [a,z']
      push_cast
      have hp : 0 < (shortenedGrid G W).thickLength q (b q) := by unfold SegmentedGrid.thickLength; omega
      exact lt_add_of_pos_right _ (by exact_mod_cast hp)
    have hlen (q : Fin d) : z' q=z q-(W : ℝ) := by
      have h := shortenedGrid_thickLength_add G W hW q (b q)
      dsimp [z,z']
      push_cast
      have hR : ((shortenedGrid G W).thickLength q (b q) : ℝ)+(W : ℝ) = G.thickLength q (b q) := by exact_mod_cast h
      linarith
    have hwidthR (q : Fin d) : 8*(W : ℝ) ≤ 3*(z q-a q) := by
      have hmin := (minThickLength_le_coordinateMinLength G q).trans (G.coordinateMinLength_le q (b q))
      dsimp [z,a]
      push_cast
      simp only [add_sub_cancel_left]
      exact_mod_cast (show 8*W ≤ 3*G.thickLength q (b q) by omega)
    change setEnergy Y (phaseCoefficients Y c u) (coordinateBox a z) ≤
      (2 : ℝ)^d*(Real.pi*n/2)^(2*d)*
        ((2 : ℝ)^d*multidimensionalTuranConstant*(d : ℝ))^(2*(n-1))*
          (2*(m : ℝ)/3)^(2*(n-1))*setEnergy Y c (coordinateBox a z')
    apply coordinateBox_translated_energy_restoration G.dimension_pos hn Y c a z z' u hshort
      (fun q => by rw [hlen]; linarith [show (0 : ℝ) ≤ W from Nat.cast_nonneg W])
      (fun q => by rw [hlen]; linarith [hwidthR q]) hu (by positivity)
    exact coordinateBox_sweep_ratio_of_width hd hm a z z' u (Nat.cast_nonneg W)
      hfull hlen hwidthR hu hshift
  rw [continuousEnergy_eq_sum_productBlockBox G,
    continuousEnergy_eq_sum_productBlockBox (shortenedGrid G W), Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => hblock b

private theorem restorationFactor_mono {d n m : ℕ} (hd : 0 < d) (hnm : n ≤ m) :
    clumpRestorationFactor d n multidimensionalTuranConstant ≤
      clumpRestorationFactor d m multidimensionalTuranConstant := by
  have hCT : 1 ≤ multidimensionalTuranConstant := by
    have he := Real.add_one_le_exp (1000000 : ℝ)
    have hp : 0 ≤ 2*Real.exp 1*oneDimensionalPruningWeakConstant :=
      mul_nonneg (by positivity) oneDimensionalPruningWeakConstant_pos.le
    unfold multidimensionalTuranConstant oneDimensionalTuranConstant
    linarith
  have hbase : (1 : ℝ) ≤ 2^d*multidimensionalTuranConstant*(d : ℝ) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hCT)
      (by exact_mod_cast hd)
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hfirst : (Real.pi*n/2)^(2*d) ≤ (Real.pi*m/2)^(2*d) := by
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnmR Real.pi_pos.le) (by norm_num)
  have hsecond := pow_le_pow_right₀ hbase (show 2*(n-1) ≤ 2*(m-1) by omega)
  unfold clumpRestorationFactor
  exact mul_le_mul (mul_le_mul_of_nonneg_left hfirst (by positivity)) hsecond
    (by positivity) (by positivity)

/-- Uniform cardinality version, including singleton clumps. The upper
cardinality `m` controls both the shifts and the final restoration factor. -/
theorem continuousEnergy_translated_le_shortenedGrid_of_cardinality_le {d n m : ℕ}
    (G : SegmentedGrid d) (hd : 2 ≤ d) (hn : 0 < n) (hm : 2 ≤ m) (hnm : n ≤ m)
    (W : ℕ) (hwidth : 8*W ≤ 3*G.minThickLength)
    (Y : Fin n → Point d) (c : Fin n → ℂ) (u : Point d)
    (hu : ∀ q, 0 ≤ u q) (hshift : ∀ q, u q ≤ ((m : ℝ)-1)*W) :
    continuousEnergy G Y (phaseCoefficients Y c u) ≤
      clumpRestorationFactor d m multidimensionalTuranConstant *
        (2*(m : ℝ)/3)^(2*(m-1))*continuousEnergy (shortenedGrid G W) Y c := by
  have h := continuousEnergy_translated_le_shortenedGrid G hd hn (by omega) W hwidth Y c u hu hshift
  change continuousEnergy G Y (phaseCoefficients Y c u) ≤
    clumpRestorationFactor d n multidimensionalTuranConstant *
      (2*(m : ℝ)/3)^(2*(n-1))*continuousEnergy (shortenedGrid G W) Y c at h
  have hbase : (1 : ℝ) ≤ 2*(m : ℝ)/3 := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hexp := pow_le_pow_right₀ hbase (show 2*(n-1) ≤ 2*(m-1) by omega)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (restorationFactor_mono (by omega : 0 < d) hnm) hexp
      (by positivity) (clumpRestorationFactor_nonneg _ _ _ multidimensionalTuranConstant_pos.le))
    (continuousEnergy_nonneg _ _ _))

end
end LeanNumDetect.MultiTuran.MultiClump
