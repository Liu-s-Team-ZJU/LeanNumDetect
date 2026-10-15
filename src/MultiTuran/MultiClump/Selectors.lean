import General.Fourier.BartonCubeFrame
import NumDetect.Segmented.ClumpBounds
import MultiTuran.MultiClump.ClumpGeometry

/-!
Clump selectors constructed from separated-color cardinal interpolants. The
coefficient mass, not only the supremum norm, is bounded by the selector
constant. This stronger conclusion gives the finite shift operator estimate
without any loss depending on the number of frequencies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

open NumDetect

private theorem mass_sub_le {d m r D : ℕ}
    (P Q : SegmentedPolynomial d m r D) :
    (P - Q).mass ≤ P.mass + Q.mass := by
  unfold SegmentedPolynomial.mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change ‖P.coeff i - Q.coeff i‖ ≤ ‖P.coeff i‖ + ‖Q.coeff i‖
  exact norm_sub_le _ _

private theorem angularValue_sub {d m r D : ℕ}
    (P Q : SegmentedPolynomial d m r D) (y : Point d) :
    (P - Q).angularValue y = P.angularValue y - Q.angularValue y := by
  change (P + -Q).angularValue y = _
  simp [SegmentedPolynomial.angularValue, sub_eq_add_neg]

private theorem frame_constant_pos : 0 < 2 - Real.exp (1 / 2 : ℝ) := by
  have hlog : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  linarith

/-- A cardinal localizer for an anchor: one at the anchor and zero outside its
clump. Both the construction and its bound follow from the actual geometric
separation through the proved cube frame theorem. -/
theorem anchor_selector_of_separated_clumps
    {d n A nStar K D : ℕ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 1 ≤ d) (hnStar : 1 ≤ nStar)
    (hcube : ∀ j, InAngularCube (Y j)) {separation : ℝ}
    (hgap : ∀ i j, C.label i ≠ C.label j →
      separation < periodicLInfDistance (Y i) (Y j))
    (hK : 4 * Real.pi * d / (K + 1) ≤ separation)
    (hD : nStar * K < D) (anchor : Fin n) :
    ∃ P : SegmentedPolynomial d (nStar * K) 0 D,
      P.angularValue (Y anchor) = 1 ∧
      (∀ j, C.label j ≠ C.label anchor → P.angularValue (Y j) = 0) ∧
      P.mass ≤ (1 / Real.sqrt (2 - Real.exp (1 / 2 : ℝ))) ^ nStar := by
  have hβ : 1 / (2 * Real.log 2) < (1 : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
    linarith [Real.log_two_gt_d9]
  have hframe := BartonCubeFrame.hasFineCubeFrame_of_translatedCube hd hβ
    (by simpa using hK)
  have hKD : K < D := by
    have hle : K ≤ nStar * K := by
      calc K = 1 * K := by omega
           _ ≤ nStar * K := Nat.mul_le_mul_right K hnStar
    exact hle.trans_lt hD
  apply localizationPolynomial_of_colorFrames C anchor hKD hD
    frame_constant_pos
  intro color v
  simpa only [mul_one] using @hframe (↥(clumpColorClass C anchor color))
    inferInstance inferInstance (fun j : ↥(clumpColorClass C anchor color) => Y j)
    (fun j => hcube j)
    (fun i j hij => hgap i j (clumpColorClass_labels_ne C anchor color i j hij)) v

/-- Turn anchor localizers into a selector equal to one on every node of the
chosen clump. The degree uses the size of that clump, bounded by `nStar`. -/
theorem clump_selector_of_anchor_selectors
    {d n A nStar m D : ℕ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hnStar : 1 ≤ nStar) (hD : nStar * m < D)
    (g : Fin n → SegmentedPolynomial d m 0 D)
    (hgone : ∀ j, (g j).angularValue (Y j) = 1)
    (hgzero : ∀ i j, C.label j ≠ C.label i → (g i).angularValue (Y j) = 0)
    {B : ℝ} (hB : 0 ≤ B) (hgmass : ∀ j, (g j).mass ≤ B)
    (a : Fin A) :
    ∃ G : SegmentedPolynomial d (nStar * m) 0 D,
      (∀ j, G.angularValue (Y j) = if C.label j = a then 1 else 0) ∧
      G.mass ≤ 1 + (1 + B) ^ nStar := by
  classical
  let S := {j : Fin n // C.label j = a}
  let q := Fintype.card S
  let e : Fin q ≃ S := (Fintype.equivFin S).symm
  have hq : q ≤ nStar := by
    simpa only [q, Fintype.card_fin] using
      Fintype.card_le_of_injective (fun j : S => C.slot j) (by
        intro i j hij
        apply Subtype.ext
        apply C.injective
        exact Prod.ext (i.property.trans j.property.symm) hij)
  have hmD : m < D := by
    have hle : m ≤ nStar * m := by
      calc m = 1 * m := by omega
           _ ≤ nStar * m := Nat.mul_le_mul_right m hnStar
    exact hle.trans_lt hD
  have hDpos : 0 < D := by omega
  let one_m : SegmentedPolynomial d m 0 D :=
    (SegmentedPolynomial.one d D hDpos).widen (Nat.zero_le m) le_rfl hmD
  let F (i : Fin q) : SegmentedPolynomial d m 0 D := one_m - g (e i)
  have hprodle : m * q ≤ nStar * m := by
    calc m * q ≤ m * nStar := Nat.mul_le_mul_left m hq
         _ = nStar * m := Nat.mul_comm _ _
  have hprod : m * q < D := hprodle.trans_lt hD
  let Q := SegmentedPolynomial.prod q F hprod
  let Q' : SegmentedPolynomial d (nStar * m) 0 D :=
    Q.widen hprodle (by simp) hD
  let one_W : SegmentedPolynomial d (nStar * m) 0 D :=
    (SegmentedPolynomial.one d D hDpos).widen (Nat.zero_le _) le_rfl hD
  let G := one_W - Q'
  have hone_m (y : Point d) : one_m.angularValue y = 1 := by
    simp [one_m, SegmentedPolynomial.angularValue]
  have hone_W (y : Point d) : one_W.angularValue y = 1 := by
    simp [one_W, SegmentedPolynomial.angularValue]
  have hmass_one_m : one_m.mass = 1 := by
    simp [one_m, SegmentedPolynomial.mass_widen]
  have hmass_one_W : one_W.mass = 1 := by
    simp [one_W, SegmentedPolynomial.mass_widen]
  refine ⟨G, ?_, ?_⟩
  · intro j
    simp only [G, angularValue_sub, hone_W,
      Q', SegmentedPolynomial.angularValue_widen, Q, SegmentedPolynomial.angularValue_prod]
    by_cases hj : C.label j = a
    · rw [if_pos hj]
      have hz : ∏ i, (F i).angularValue (Y j) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (e.symm ⟨j, hj⟩))
        simp only [F, angularValue_sub, hone_m]
        have he : ((e (e.symm ⟨j, hj⟩) : S) : Fin n) = j := by simp
        rw [he, hgone, sub_self]
      rw [hz]
      ring
    · rw [if_neg hj]
      have hone : ∀ i, (F i).angularValue (Y j) = 1 := by
        intro i
        simp only [F, angularValue_sub, hone_m]
        rw [hgzero (e i) j (by
          intro h
          exact hj (h.trans (e i).property)), sub_zero]
      simp [hone]
  · calc
      G.mass ≤ one_W.mass + Q'.mass := mass_sub_le _ _
      _ = 1 + Q.mass := by rw [hmass_one_W]; simp [Q', SegmentedPolynomial.mass_widen]
      _ ≤ 1 + ∏ i, (F i).mass :=
        add_le_add (le_refl 1) (SegmentedPolynomial.mass_prod_le F hprod)
      _ ≤ 1 + ∏ _i : Fin q, (1 + B) := by
        apply add_le_add (le_refl 1)
        apply Finset.prod_le_prod
        · intro i _
          exact SegmentedPolynomial.mass_nonneg _
        · intro i _
          calc
            (F i).mass ≤ one_m.mass + (g (e i)).mass := mass_sub_le _ _
            _ = 1 + (g (e i)).mass := by rw [hmass_one_m]
            _ ≤ 1 + B := add_le_add (le_refl 1) (hgmass _)
      _ = 1 + (1 + B) ^ q := by simp
      _ ≤ 1 + (1 + B) ^ nStar := by
        have hbase : (1 : ℝ) ≤ 1 + B := by linarith
        exact add_le_add (le_refl 1) (pow_le_pow_right₀ hbase hq)


/-- Uniform clump selector with the degree and constant used in the Riemann
multi-clump proof. No selector or operator estimate is assumed. -/
theorem clump_selector_of_separated_clumps
    {d n A nStar K D : ℕ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 1 ≤ d) (hnStar : 1 ≤ nStar)
    (hcube : ∀ j, InAngularCube (Y j)) {separation : ℝ}
    (hgap : ∀ i j, C.label i ≠ C.label j →
      separation < periodicLInfDistance (Y i) (Y j))
    (hK : 4 * Real.pi * d / (K + 1) ≤ separation)
    (hD : nStar * (nStar * K) < D) (a : Fin A) :
    ∃ G : SegmentedPolynomial d (nStar * (nStar * K)) 0 D,
      (∀ j, G.angularValue (Y j) = if C.label j = a then 1 else 0) ∧
      G.mass ≤ 1 + (1 + (1 / Real.sqrt (2 - Real.exp (1 / 2 : ℝ))) ^ nStar) ^ nStar := by
  have hgD : nStar * K < D := by
    have hle : nStar * K ≤ nStar * (nStar * K) := by
      calc nStar * K = 1 * (nStar * K) := by omega
           _ ≤ nStar * (nStar * K) := Nat.mul_le_mul_right _ hnStar
    exact hle.trans_lt hD
  choose g hgone hgzero hgmass using
    anchor_selector_of_separated_clumps C hd hnStar hcube hgap hK hgD
  exact clump_selector_of_anchor_selectors C hnStar hD g hgone hgzero
    (by positivity) hgmass a


/-- The geometric selector theorem for arbitrary real node representatives.
Principal-chart normalization is internal and preserves every integer phase. -/
theorem clump_selector_of_torus_separated_clumps
    {d n A nStar K D : ℕ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 1 ≤ d) (hnStar : 1 ≤ nStar) {separation : ℝ}
    (hgap : ∀ i j, C.label i ≠ C.label j →
      separation < torusLInfDistance (Y i) (Y j))
    (hK : 4 * Real.pi * d / (K + 1) ≤ separation)
    (hD : nStar * (nStar * K) < D) (a : Fin A) :
    ∃ G : SegmentedPolynomial d (nStar * (nStar * K)) 0 D,
      (∀ j, G.angularValue (Y j) = if C.label j = a then 1 else 0) ∧
      G.mass ≤ 1 + (1 + (1 / Real.sqrt (2 - Real.exp (1 / 2 : ℝ))) ^ nStar) ^ nStar := by
  let Y' := fun j => principalAngularPoint (Y j)
  let C' : ClumpSlots (A := A) (nStar := nStar) Y' :=
    { label := C.label, slot := C.slot, injective := C.injective }
  have hcube : ∀ j, InAngularCube (Y' j) := fun j => principalAngularPoint_mem (Y j)
  have hgap' : ∀ i j, C'.label i ≠ C'.label j →
      separation < periodicLInfDistance (Y' i) (Y' j) := by
    intro i j hij
    rw [← torusLInfDistance_eq_periodicLInfDistance (hcube i) (hcube j)]
    simpa only [Y', torusLInfDistance_principalAngularPoint] using hgap i j hij
  obtain ⟨G, hG, hmass⟩ :=
    clump_selector_of_separated_clumps C' hd hnStar hcube hgap' hK hD a
  refine ⟨G, ?_, hmass⟩
  intro j
  simpa only [Y', segmentedPolynomial_angularValue_principalAngularPoint, C'] using hG j

end
end LeanNumDetect.MultiTuran.MultiClump
