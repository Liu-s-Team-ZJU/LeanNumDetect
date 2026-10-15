import MultiTuran.MultiClump.BlockRestoration
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # The volume of a rectangle swept along one nonnegative segment

The swept convex body is covered by the original rectangle and its upper
faces swept along the segment.  Determinants give a volume bound linear in
the translation length, with no product of coordinate expansion factors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators Pointwise ENNReal
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

def coordinateBoxSweep {d : ℕ} (a b u : Point d) : Set (Point d) :=
  coordinateBox a b + segment ℝ 0 u

theorem coordinateBoxSweep_isCompact {d : ℕ} (a b u : Point d) :
    IsCompact (coordinateBoxSweep a b u) := by
  apply (isCompact_univ_pi (fun _ => isCompact_Icc)).add
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image (by fun_prop)

theorem coordinateBoxSweep_convex {d : ℕ} (a b u : Point d) :
    Convex ℝ (coordinateBoxSweep a b u) :=
  (convex_pi (fun _ _ => convex_Icc _ _)).add (convex_segment _ _)

theorem coordinateBox_subset_sweep {d : ℕ} (a b u : Point d) :
    coordinateBox a b ⊆ coordinateBoxSweep a b u := by
  intro x hx
  exact Set.mem_add.mpr ⟨x,hx,0,left_mem_segment ℝ 0 u,by simp⟩

theorem coordinateBox_add_subset_sweep {d : ℕ} (a b u : Point d) :
    (fun x => x+u) '' coordinateBox a b ⊆ coordinateBoxSweep a b u := by
  rintro _ ⟨x,hx,rfl⟩
  exact Set.mem_add.mpr ⟨x,hx,u,right_mem_segment ℝ 0 u,rfl⟩

private def sweepMatrix {d : ℕ} (a b u : Point d) (q : Fin d) :
    Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.diagonal (fun i => b i-a i)).updateCol q u

private def sweepPrismBase {d : ℕ} (a b : Point d) (q : Fin d) : Point d :=
  fun i => if i=q then b q else a i

private def sweepPrism {d : ℕ} (a b u : Point d) (q : Fin d) : Set (Point d) :=
  (fun z => sweepPrismBase a b q + Matrix.toLin' (sweepMatrix a b u q) z) ''
    coordinateBox (fun _ => 0) (fun _ => 1)

private theorem sweepMatrix_apply {d : ℕ} (a b u : Point d) (q : Fin d)
    (z : Point d) (i : Fin d) :
    Matrix.toLin' (sweepMatrix a b u q) z i =
      (if i=q then 0 else (b i-a i)*z i) + u i*z q := by
  classical
  rw [Matrix.toLin'_apply]
  change (∑ j, (sweepMatrix a b u q) i j*z j) = _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ q)]
  simp only [sweepMatrix, Matrix.updateCol_apply, ite_true]
  have hsum : ∑ j ∈ Finset.univ.erase q,
      (if j=q then u i else Matrix.diagonal (fun k => b k-a k) i j)*z j =
      ∑ j ∈ Finset.univ.erase q, Matrix.diagonal (fun k => b k-a k) i j*z j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_neg (Finset.mem_erase.mp hj).1]
  rw [hsum]
  by_cases hi : i=q
  · subst i
    simp [Matrix.diagonal, Finset.mem_erase]
  · simp [Matrix.diagonal, hi, Ne.symm hi]

private theorem sweepMatrix_det {d : ℕ} (a b u : Point d) (q : Fin d)
    (hab : ∀ i, a i < b i) :
    (sweepMatrix a b u q).det = (u q/(b q-a q)) * ∏ i, (b i-a i) := by
  classical
  have hrepr (k : Fin d) :
      u k = ∑ i, (u i/(b i-a i)) • Matrix.diagonal (fun j => b j-a j) k i := by
    simp [Matrix.diagonal, ne_of_gt (sub_pos.mpr (hab k))]
  calc
    _ = ((Matrix.diagonal (fun j => b j-a j)).updateCol q
        (fun k => ∑ i, (u i/(b i-a i)) • Matrix.diagonal (fun j => b j-a j) k i)).det := by
      congr 2
      exact funext hrepr
    _ = _ := by rw [Matrix.det_updateCol_sum, Matrix.det_diagonal, smul_eq_mul]

private theorem sweepPrism_volume {d : ℕ} (a b u : Point d) (q : Fin d)
    (hab : ∀ i, a i < b i) (hu : ∀ i, 0 ≤ u i) :
    volume (sweepPrism a b u q) =
      ENNReal.ofReal ((u q/(b q-a q)) * ∏ i, (b i-a i)) := by
  have himage : sweepPrism a b u q =
      (fun x => sweepPrismBase a b q+x) ''
        (Matrix.toLin' (sweepMatrix a b u q) '' coordinateBox (fun _ => 0) (fun _ => 1)) := by
    rw [Set.image_image]
    rfl
  rw [himage, Set.image_add_left, measure_preimage_add,
    Measure.addHaar_image_linearMap]
  rw [LinearMap.det_toLin', sweepMatrix_det a b u q hab]
  have hp : 0 ≤ (u q/(b q-a q)) * ∏ i, (b i-a i) :=
    mul_nonneg (div_nonneg (hu q) (sub_pos.mpr (hab q)).le)
      (Finset.prod_nonneg fun i _ => (sub_pos.mpr (hab i)).le)
  rw [abs_of_nonneg hp, coordinateBox_volume]
  · simp
  · intro i
    norm_num

private theorem coordinateBoxSweep_subset_prisms {d : ℕ} (hd : 0 < d)
    (a b u : Point d) (hab : ∀ i, a i < b i) (hu : ∀ i, 0 ≤ u i) :
    coordinateBoxSweep a b u ⊆ coordinateBox a b ∪ ⋃ q, sweepPrism a b u q := by
  classical
  intro x hx
  by_cases hbox : x ∈ coordinateBox a b
  · exact Or.inl hbox
  obtain ⟨r,hr,s,hs,hx⟩ := Set.mem_add.mp hx
  rw [segment_eq_image] at hs
  obtain ⟨t,ht,hst⟩ := hs
  simp only [smul_zero, zero_add] at hst
  subst s
  subst x
  have hrlo (i : Fin d) : a i ≤ r i := (hr i (Set.mem_univ i)).1
  have hrhi (i : Fin d) : r i ≤ b i := (hr i (Set.mem_univ i)).2
  have houtside : ∃ i, b i < r i+t*u i := by
    by_contra! h
    apply hbox
    intro i _
    exact ⟨by dsimp; linarith [hrlo i,mul_nonneg ht.1 (hu i)], h i⟩
  obtain ⟨p,hp⟩ := houtside
  have hup : 0 < u p := by
    by_contra! hz
    linarith [hrhi p,mul_nonpos_of_nonneg_of_nonpos ht.1 hz]
  let ratio : Fin d → ℝ := fun i => (r i+t*u i-b i)/u i
  obtain ⟨q,_,hq⟩ := Finset.exists_max_image Finset.univ ratio
    ⟨⟨0,hd⟩, Finset.mem_univ _⟩
  let v := ratio q
  have hvpos : 0 < v :=
    (div_pos (sub_pos.mpr hp) hup).trans_le (hq p (Finset.mem_univ p))
  have huq : 0 < u q := by
    have hne : u q ≠ 0 := by
      intro hz
      have : v=0 := by simp [v,ratio,hz]
      linarith
    exact lt_of_le_of_ne (hu q) (Ne.symm hne)
  have hvt : v ≤ t := by
    dsimp [v,ratio]
    apply (div_le_iff₀ huq).mpr
    nlinarith [hrhi q]
  let z : Point d := fun i =>
    if i=q then v else (r i+t*u i-v*u i-a i)/(b i-a i)
  have hz : z ∈ coordinateBox (fun _ => 0) (fun _ => 1) := by
    intro i _
    by_cases hi : i=q
    · simp only [z,hi,ite_true]
      exact ⟨hvpos.le,hvt.trans ht.2⟩
    · simp only [z,hi,ite_false]
      have hl : 0 ≤ r i+t*u i-v*u i-a i := by
        nlinarith [hrlo i,mul_nonneg (sub_nonneg.mpr hvt) (hu i)]
      have hh : r i+t*u i-v*u i ≤ b i := by
        by_cases hui : u i=0
        · simpa [hui] using hrhi i
        · have hui' : 0 < u i := lt_of_le_of_ne (hu i) (Ne.symm hui)
          have h := (div_le_iff₀ hui').mp (hq i (Finset.mem_univ i))
          change r i+t*u i-b i ≤ v*u i at h
          linarith
      exact ⟨div_nonneg hl (sub_pos.mpr (hab i)).le,
        (div_le_one (sub_pos.mpr (hab i))).mpr (by linarith)⟩
  apply Or.inr
  apply Set.mem_iUnion.mpr
  refine ⟨q, z,hz,?_⟩
  funext i
  change sweepPrismBase a b q i + Matrix.toLin' (sweepMatrix a b u q) z i = r i+t*u i
  rw [sweepMatrix_apply]
  by_cases hi : i=q
  · subst i
    simp only [sweepPrismBase,ite_true,z,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    have h : v*u q = r q+t*u q-b q := by
      dsimp [v,ratio]
      exact div_mul_cancel₀ _ huq.ne'
    linarith
  · simp only [sweepPrismBase,hi,ite_false,z,ite_true,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    field_simp [ne_of_gt (sub_pos.mpr (hab i))]
    <;> ring

/-- The volume increases linearly along one segment, even when every
coordinate of the translation is nonzero. -/
theorem coordinateBoxSweep_volume_le {d : ℕ} (hd : 0 < d)
    (a b u : Point d) (hab : ∀ i, a i < b i) (hu : ∀ i, 0 ≤ u i) :
    volume (coordinateBoxSweep a b u) ≤
      ENNReal.ofReal ((∏ i, (b i-a i)) * (1+∑ i, u i/(b i-a i))) := by
  classical
  have hprod : 0 ≤ ∏ i, (b i-a i) := Finset.prod_nonneg fun i _ => (sub_pos.mpr (hab i)).le
  have hterm (i : Fin d) : 0 ≤ (u i/(b i-a i)) * ∏ j, (b j-a j) :=
    mul_nonneg (div_nonneg (hu i) (sub_pos.mpr (hab i)).le) hprod
  calc
    _ ≤ volume (coordinateBox a b ∪ ⋃ q, sweepPrism a b u q) :=
      measure_mono (coordinateBoxSweep_subset_prisms hd a b u hab hu)
    _ ≤ volume (coordinateBox a b) + ∑ q, volume (sweepPrism a b u q) :=
      (measure_union_le _ _).trans (add_le_add_right (measure_iUnion_fintype_le _ _) _)
    _ = ENNReal.ofReal (∏ i, (b i-a i)) +
        ∑ q, ENNReal.ofReal ((u q/(b q-a q)) * ∏ i, (b i-a i)) := by
      rw [coordinateBox_volume a b (fun i => (hab i).le)]
      simp_rw [sweepPrism_volume a b u _ hab hu]
    _ = ENNReal.ofReal ((∏ i, (b i-a i)) * (1+∑ i, u i/(b i-a i))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hterm i),
        ← ENNReal.ofReal_add hprod (Finset.sum_nonneg fun i _ => hterm i)]
      congr 1
      rw [← Finset.sum_mul]
      ring

end
end LeanNumDetect.MultiTuran.MultiClump
