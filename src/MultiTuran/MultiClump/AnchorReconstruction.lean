import NumDetect.Segmented.Polynomial
import MultiTuran.Preliminaries.Geometry

/-!
Finite polynomial remainders for the continuous clump reconstruction.
The anchor localizers retain their linear bandwidth. Their higher-degree
prefix products are applied only to already localized continuous sums.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

open NumDetect

/-- Include an index preceding an anchor into the original anchor family. -/
def prefixAnchorIndex {v : ℕ} (j : Fin v) (i : Fin j.val) : Fin v :=
  ⟨i.val, lt_trans i.isLt j.isLt⟩

private theorem polynomial_mass_sub_le {d m r D : ℕ}
    (P Q : SegmentedPolynomial d m r D) :
    (P - Q).mass ≤ P.mass + Q.mass := by
  unfold SegmentedPolynomial.mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change ‖P.coeff i - Q.coeff i‖ ≤ ‖P.coeff i‖ + ‖Q.coeff i‖
  exact norm_sub_le _ _

private theorem polynomial_angularValue_sub {d m r D : ℕ}
    (P Q : SegmentedPolynomial d m r D) (y : Point d) :
    (P - Q).angularValue y = P.angularValue y - Q.angularValue y := by
  change (P + -Q).angularValue y = _
  simp [SegmentedPolynomial.angularValue, sub_eq_add_neg]

/-- The prefix remainder `∏ i < j, (1 - g i)`, with a common support budget. -/
def anchorRemainder {d v nStar W D : ℕ}
    (hv : v ≤ nStar) (hD : nStar * W < D)
    (g : Fin v → SegmentedPolynomial d W 0 D) (j : Fin v) :
    SegmentedPolynomial d ((nStar - 1) * W) 0 D := by
  have hDpos : 0 < D := by omega
  have hWD : W < D := by
    have hns : 1 ≤ nStar := by have := j.isLt; omega
    have hle : W ≤ nStar * W := by simpa using Nat.mul_le_mul_right W hns
    exact hle.trans_lt hD
  let oneW : SegmentedPolynomial d W 0 D :=
    (SegmentedPolynomial.one d D hDpos).widen (Nat.zero_le W) le_rfl hWD
  let F (i : Fin j.val) : SegmentedPolynomial d W 0 D :=
    oneW - g (prefixAnchorIndex j i)
  have hj : j.val ≤ nStar - 1 := by omega
  have hwidth : W * j.val ≤ (nStar - 1) * W := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left W hj
  have htotal : (nStar - 1) * W < D :=
    (Nat.mul_le_mul_right W (Nat.sub_le nStar 1)).trans_lt hD
  let Q := SegmentedPolynomial.prod j.val F (hwidth.trans_lt htotal)
  exact Q.widen hwidth (by simp) htotal

/-- Values of the common-budget prefix remainder. -/
theorem anchorRemainder_angularValue {d v nStar W D : ℕ}
    (hv : v ≤ nStar) (hD : nStar * W < D)
    (g : Fin v → SegmentedPolynomial d W 0 D) (j : Fin v) (y : Point d) :
    (anchorRemainder hv hD g j).angularValue y =
      ∏ i : Fin j.val, (1 - (g (prefixAnchorIndex j i)).angularValue y) := by
  classical
  simp only [anchorRemainder, SegmentedPolynomial.angularValue_widen,
    SegmentedPolynomial.angularValue_prod, polynomial_angularValue_sub]
  apply Finset.prod_congr rfl
  intro i _
  simp [SegmentedPolynomial.angularValue]

/-- Prefix coefficient mass grows by at most one factor `1+B` per anchor. -/
theorem anchorRemainder_mass_le {d v nStar W D : ℕ}
    (hv : v ≤ nStar) (hD : nStar * W < D)
    (g : Fin v → SegmentedPolynomial d W 0 D)
    {B : ℝ} (_hB : 0 ≤ B) (hgmass : ∀ j, (g j).mass ≤ B) (j : Fin v) :
    (anchorRemainder hv hD g j).mass ≤ (1 + B) ^ j.val := by
  classical
  dsimp [anchorRemainder]
  rw [SegmentedPolynomial.mass_widen]
  refine (SegmentedPolynomial.mass_prod_le _ _).trans ?_
  calc
    (∏ i : Fin j.val,
        (((SegmentedPolynomial.one d D _).widen (Nat.zero_le W) le_rfl _) -
          g (prefixAnchorIndex j i)).mass) ≤ ∏ _i : Fin j.val, (1 + B) := by
      apply Finset.prod_le_prod
      · intro i _
        exact SegmentedPolynomial.mass_nonneg _
      · intro i _
        calc
          _ ≤ ((SegmentedPolynomial.one d D _).widen (Nat.zero_le W) le_rfl _).mass +
              (g (prefixAnchorIndex j i)).mass := polynomial_mass_sub_le _ _
          _ = 1 + (g (prefixAnchorIndex j i)).mass := by
            simp only [SegmentedPolynomial.mass_widen, SegmentedPolynomial.mass_one]
          _ ≤ 1 + B := add_le_add (le_refl 1) (hgmass _)
    _ = (1 + B) ^ j.val := by simp

/-- Scalar telescoping identity for successively multiplying by `1-g`. -/
theorem scalar_prefix_telescoping (v : ℕ) (g : Fin v → ℂ) :
    (∑ j : Fin v, (∏ i : Fin j.val, (1 - g (prefixAnchorIndex j i))) * g j) =
      1 - ∏ j : Fin v, (1 - g j) := by
  classical
  induction v with
  | zero => simp
  | succ v ih =>
    rw [Fin.sum_univ_castSucc, Fin.prod_univ_castSucc]
    have hprefix (j : Fin v) :
        (∏ i : Fin j.castSucc.val, (1 - g (prefixAnchorIndex j.castSucc i))) =
          ∏ i : Fin j.val, (1 - g (prefixAnchorIndex j i).castSucc) := by
      apply Finset.prod_congr rfl
      intro i _
      rfl
    have hlast :
        (∏ i : Fin (Fin.last v).val, (1 - g (prefixAnchorIndex (Fin.last v) i))) =
          ∏ i : Fin v, (1 - g i.castSucc) := by
      apply Finset.prod_congr rfl
      intro i _
      rfl
    simp only [hprefix, hlast]
    rw [ih (fun i => g i.castSucc)]
    ring

/-- At an anchor point, the full remainder product vanishes. -/
theorem scalar_prefix_reconstruction {v : ℕ} (g : Fin v → ℂ) (k : Fin v)
    (hk : g k = 1) :
    (∑ j : Fin v, (∏ i : Fin j.val, (1 - g (prefixAnchorIndex j i))) * g j) = 1 := by
  classical
  rw [scalar_prefix_telescoping]
  have hz : ∏ j : Fin v, (1 - g j) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rw [hk, sub_self]
  rw [hz, sub_zero]

/-- Reconstruction of the constant data on an anchor family by prefix products. -/
theorem anchorRemainder_reconstruction {d v nStar W D : ℕ}
    (hv : v ≤ nStar) (hD : nStar * W < D)
    (g : Fin v → SegmentedPolynomial d W 0 D) (Y : Fin v → Point d)
    (hgone : ∀ j, (g j).angularValue (Y j) = 1) (k : Fin v) :
    (∑ j : Fin v,
      (anchorRemainder hv hD g j).angularValue (Y k) * (g j).angularValue (Y k)) = 1 := by
  simp only [anchorRemainder_angularValue]
  exact scalar_prefix_reconstruction (fun j => (g j).angularValue (Y k)) k (hgone k)

/-- Exact geometric mass sum used after the anchor estimates. -/
theorem anchor_geometric_sum (v : ℕ) (B : ℝ) :
    B * (∑ j : Fin v, (1 + B) ^ j.val) = (1 + B) ^ v - 1 := by
  classical
  induction v with
  | zero => simp
  | succ v ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [mul_add, ih, pow_succ]
    ring

end
end LeanNumDetect.MultiTuran.MultiClump
