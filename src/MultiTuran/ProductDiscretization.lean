import MultiTuran.Energy
import MultiTuran.BoundFormula
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Integration over the actual measured unit cells

The closed unit cells cover the genuine segmented thickening. Their interiors
are disjoint, but the upper Riemann estimate needs only the cover. In particular
no abstract replacement for either the measured sum or the integral is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

private theorem update_fin_cons_zero {d : ℕ} (u v : ℝ) (x : Point d) :
    Function.update (Fin.cons u x : Point (d+1)) 0 v = Fin.cons v x := by
  ext q
  refine Fin.cases ?_ (fun r => ?_) q <;> simp

private theorem update_fin_cons_succ {d : ℕ} (u v : ℝ) (x : Point d) (q : Fin d) :
    Function.update (Fin.cons u x : Point (d+1)) q.succ v =
      Fin.cons u (Function.update x q v) := by
  ext r
  refine Fin.cases ?_ (fun r => ?_) r
  · rw [Function.update_of_ne (Fin.succ_ne_zero q).symm]
    rfl
  · by_cases hr : r = q
    · subst r; simp
    · simp [hr, Fin.succ_inj]

/-- Changing coordinates one at a time bounds the oscillation on a product
set by the sum of the scalar-coordinate oscillations. -/
theorem pi_oscillation_le_sum (d : ℕ) (S : Fin d → Set ℝ) (D : Fin d → ℝ)
    (f : Point d → ℝ)
    (hsection : ∀ q (z : Point d), (∀ r, z r ∈ S r) →
      ∀ u ∈ S q, |f (Function.update z q u) - f z| ≤ D q)
    (x y : Point d) (hx : ∀ q, x q ∈ S q) (hy : ∀ q, y q ∈ S q) :
    |f x - f y| ≤ ∑ q, D q := by
  induction d with
  | zero =>
    have hxy : x = y := Subsingleton.elim _ _
    simp [hxy]
  | succ d ih =>
    let xt : Point d := fun q => x q.succ
    let yt : Point d := fun q => y q.succ
    have hxcons : Fin.cons (x 0) xt = x := by
      ext q
      refine Fin.cases ?_ (fun r => ?_) q <;> rfl
    have hycons : Fin.cons (y 0) yt = y := by
      ext q
      refine Fin.cases ?_ (fun r => ?_) q <;> rfl
    have hfirst : |f x - f (Fin.cons (y 0) xt)| ≤ D 0 := by
      have h := hsection 0 x hx (y 0) (hy 0)
      rw [← hxcons, update_fin_cons_zero, hxcons, abs_sub_comm] at h
      exact h
    have htail : |f (Fin.cons (y 0) xt) - f (Fin.cons (y 0) yt)| ≤
        ∑ q : Fin d, D q.succ := by
      apply ih (fun q => S q.succ) (fun q => D q.succ)
        (fun z => f (Fin.cons (y 0) z))
      · intro q z hz u hu
        have hmem : ∀ r, (Fin.cons (y 0) z : Point (d+1)) r ∈ S r := by
          intro r
          refine Fin.cases ?_ (fun r => ?_) r
          · exact hy 0
          · exact hz r
        simpa only [update_fin_cons_succ] using hsection q.succ
          (Fin.cons (y 0) z) hmem u hu
      · exact fun q => hx q.succ
      · exact fun q => hy q.succ
    calc
      |f x - f y| ≤ |f x - f (Fin.cons (y 0) xt)| +
          |f (Fin.cons (y 0) xt) - f y| := abs_sub_le _ _ _
      _ ≤ D 0 + ∑ q : Fin d, D q.succ := by
        rw [← hycons]
        exact add_le_add hfirst htail
      _ = ∑ q, D q := (Fin.sum_univ_succ D).symm

namespace SegmentedGrid
variable {d : ℕ} (G : SegmentedGrid d)

/-- The actual real vector corresponding to a measured integer row. -/
def rowPoint (k : G.Row) : Point d := fun q => (G.rowVector k q : ℝ)

/-- The closed unit cube beginning at a measured row. -/
def unitCell (k : G.Row) : Set (Point d) :=
  Set.pi Set.univ (fun q => Set.Icc (G.rowPoint k q) (G.rowPoint k q + 1))

theorem unitCell_isCompact (k : G.Row) : IsCompact (G.unitCell k) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem unitCell_measurableSet (k : G.Row) : MeasurableSet (G.unitCell k) :=
  (G.unitCell_isCompact k).isClosed.measurableSet

@[simp] theorem unitCell_volume (k : G.Row) : volume (G.unitCell k) = 1 := by
  rw [unitCell, volume_pi_pi]
  simp [Real.volume_Icc]

theorem unitCell_subset_thickening (k : G.Row) : G.unitCell k ⊆ G.thickening := by
  intro x hx q hq
  obtain ⟨m,hm⟩ := (G.mem_coordinateRows q _).1 (k q).property
  obtain ⟨hlo,hhi⟩ := (G.mem_blockRows q m _).1 hm
  apply Set.mem_iUnion.2
  refine ⟨m, ?_⟩
  have hlow : (G.start q m : ℝ) ≤ G.rowPoint k q := by
    change (G.start q m : ℝ) ≤ ((k q).val : ℝ)
    exact_mod_cast hlo
  have hhigh : G.rowPoint k q + 1 ≤ (G.start q m + G.thickLength q m : ℕ) := by
    dsimp only [thickLength]
    push_cast
    have h : G.rowPoint k q ≤ (G.start q m : ℝ) + G.length q m := by
      change ((k q).val : ℝ) ≤ (G.start q m : ℝ) + G.length q m
      exact_mod_cast hhi
    linarith
  exact ⟨hlow.trans (hx q hq).1, (hx q hq).2.trans hhigh⟩

private theorem interval_unit_cover (a l : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (a : ℝ) (a+l+1 : ℕ)) :
    ∃ k : ℕ, (a ≤ k ∧ k ≤ a+l) ∧ t ∈ Set.Icc (k : ℝ) (k+1) := by
  have ht0 : 0 ≤ t := (Nat.cast_nonneg a).trans ht.1
  let k := min ⌊t⌋₊ (a+l)
  have halow : a ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0).2 ht.1
  refine ⟨k, ⟨le_min halow (by omega), min_le_right _ _⟩, ?_, ?_⟩
  · exact (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le ht0)
  · by_cases h : ⌊t⌋₊ ≤ a+l
    · dsimp [k]
      rw [min_eq_left h]
      exact (Nat.lt_floor_add_one t).le
    · dsimp [k]
      rw [min_eq_right (le_of_not_ge h)]
      simpa only [Nat.cast_add, Nat.cast_one] using ht.2

/-- Every point of the true thickening belongs to a measured unit cell,
including upper block endpoints. -/
theorem thickening_eq_iUnion_unitCell : G.thickening = ⋃ k : G.Row, G.unitCell k := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hex (q : Fin d) : ∃ k : {k : ℕ // k ∈ G.coordinateRows q},
        x q ∈ Set.Icc (k.val : ℝ) (k.val+1) := by
      obtain ⟨m,hm⟩ := Set.mem_iUnion.mp (hx q (Set.mem_univ q))
      change x q ∈ Set.Icc (G.start q m : ℝ)
        (G.start q m + (G.length q m + 1) : ℕ) at hm
      rw [← Nat.add_assoc] at hm
      obtain ⟨k,hk,hxk⟩ := interval_unit_cover (G.start q m) (G.length q m) hm
      refine ⟨⟨k, (G.mem_coordinateRows q k).2 ⟨m, (G.mem_blockRows q m k).2 hk⟩⟩, hxk⟩
    choose k hk using hex
    exact Set.mem_iUnion.2 ⟨k, fun q _ => hk q⟩
  · exact Set.iUnion_subset fun k => G.unitCell_subset_thickening k

/-- A nonnegative continuous function integrates over the thickening to at
most the sum of its integrals over the measured unit cells. -/
theorem integral_thickening_le_sum_cells (f : Point d → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 ≤ f x) :
    (∫ x in G.thickening, f x) ≤ ∑ k : G.Row, ∫ x in G.unitCell k, f x := by
  classical
  have hInt : Integrable ((G.thickening).indicator f) :=
    (integrable_indicator_iff G.thickening_measurableSet).2
      (hf.continuousOn.integrableOn_compact G.thickening_isCompact)
  have hcell (k : G.Row) : Integrable ((G.unitCell k).indicator f) :=
    (integrable_indicator_iff (G.unitCell_measurableSet k)).2
      (hf.continuousOn.integrableOn_compact (G.unitCell_isCompact k))
  have hsum : Integrable (fun x => ∑ k : G.Row, (G.unitCell k).indicator f x) :=
    integrable_finsetSum _ fun k _ => hcell k
  rw [← integral_indicator G.thickening_measurableSet]
  calc
    _ ≤ ∫ x, ∑ k : G.Row, (G.unitCell k).indicator f x := by
      apply integral_mono hInt hsum
      intro x
      by_cases hx : x ∈ G.thickening
      · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (G.thickening_eq_iUnion_unitCell ▸ hx)
        rw [Set.indicator_of_mem hx]
        calc
          f x = (G.unitCell k).indicator f x := (Set.indicator_of_mem hk f).symm
          _ ≤ ∑ j : G.Row, (G.unitCell j).indicator f x :=
            Finset.single_le_sum (fun j _ => Set.indicator_nonneg (fun x _ => hpos x) x)
              (Finset.mem_univ k)
      · rw [Set.indicator_of_notMem hx]
        exact Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun x _ => hpos x) x
    _ = ∑ k : G.Row, ∫ x in G.unitCell k, f x := by
      rw [integral_finsetSum _ (fun k _ => hcell k)]
      apply Finset.sum_congr rfl
      intro k _
      exact integral_indicator (G.unitCell_measurableSet k)

/-- Multidimensional upper Riemann estimate with the literal measured rows.
The oscillation premise can be obtained from directional derivative bounds. -/
theorem integral_thickening_le_sum_rows_add_error
    (f : Point d → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x)
    (ε : ℝ) (hosc : ∀ (k : G.Row) x, x ∈ G.unitCell k →
      f x ≤ f (G.rowPoint k) + ε) :
    (∫ x in G.thickening, f x) ≤
      (∑ k : G.Row, f (G.rowPoint k)) + G.rowCount * ε := by
  calc
    _ ≤ ∑ k : G.Row, ∫ x in G.unitCell k, f x :=
      G.integral_thickening_le_sum_cells f hf hpos
    _ ≤ ∑ k : G.Row, (f (G.rowPoint k) + ε) := by
      apply Finset.sum_le_sum
      intro k _
      have hc : IntegrableOn (fun _ : Point d => f (G.rowPoint k) + ε) (G.unitCell k) :=
        integrableOn_const (by simp)
      have hm := setIntegral_mono_on
        (hf.continuousOn.integrableOn_compact (G.unitCell_isCompact k)) hc
        (G.unitCell_measurableSet k) (hosc k)
      simpa [setIntegral_const, measureReal_def] using hm
    _ = _ := by simp [Finset.sum_add_distrib, rowCount, Nat.cast_prod]

end SegmentedGrid

/-- The actual continuous/discrete relative-error implication in dimension
`d`. This is a transfer lemma; it does not assume a Bernstein theorem. -/
theorem continuousNorming_half_of_cell_oscillation {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d)
    (ε : (Fin n → ℂ) → ℝ)
    (hosc : ∀ c (k : G.Row) x, x ∈ G.unitCell k →
      ‖exponentialSum Y c x‖ ^ 2 ≤
        ‖exponentialSum Y c (G.rowPoint k)‖ ^ 2 + ε c)
    (herror : ∀ c, G.rowCount * ε c ≤ (1 / 2 : ℝ) * continuousEnergy G Y c) :
    ContinuousNorming G Y (1 / 2) := by
  intro c
  have h := G.integral_thickening_le_sum_rows_add_error
    (fun x => ‖exponentialSum Y c x‖ ^ 2) ((continuous_exponentialSum Y c).norm.pow 2)
    (fun x => sq_nonneg _) (ε c) (hosc c)
  change continuousEnergy G Y c ≤ discreteEnergy G Y c + G.rowCount * ε c at h
  linarith [herror c]

/-- A coordinate Lipschitz bound on each measured unit cell supplies its full
multidimensional Riemann error, with the sum of the coordinate coefficients. -/
theorem continuousNorming_half_of_coordinate_lipschitz {d n : ℕ}
    (G : SegmentedGrid d) (Y : Fin n → Point d)
    (D : (Fin n → ℂ) → Fin d → ℝ) (hD : ∀ c q, 0 ≤ D c q)
    (hLip : ∀ c (k : G.Row) q (z : Point d), z ∈ G.unitCell k →
      ∀ u ∈ Set.Icc (G.rowPoint k q) (G.rowPoint k q + 1),
      |‖exponentialSum Y c (Function.update z q u)‖ ^ 2 -
        ‖exponentialSum Y c z‖ ^ 2| ≤ D c q * |u-z q|)
    (herror : ∀ c, G.rowCount * (∑ q, D c q) ≤
      (1 / 2 : ℝ) * continuousEnergy G Y c) :
    ContinuousNorming G Y (1 / 2) := by
  apply continuousNorming_half_of_cell_oscillation G Y (fun c => ∑ q, D c q) ?_ herror
  intro c k x hx
  have hosc := pi_oscillation_le_sum d
    (fun q => Set.Icc (G.rowPoint k q) (G.rowPoint k q + 1)) (D c)
    (fun z => ‖exponentialSum Y c z‖ ^ 2)
    (fun q z hz u hu => ?_) x (G.rowPoint k)
    (fun q => hx q (Set.mem_univ q)) (fun _ => ⟨le_rfl, by linarith⟩)
  · exact (le_abs_self _).trans hosc |> fun h => by linarith
  · have hzcell : z ∈ G.unitCell k := fun r _ => hz r
    have hdist : |u - z q| ≤ 1 := by
      obtain ⟨hzlo,hzhi⟩ := hz q
      obtain ⟨hulo,huhi⟩ := hu
      exact abs_le.2 ⟨by linarith, by linarith⟩
    exact (hLip c k q z hzcell u hu).trans
      ((mul_le_mul_of_nonneg_left hdist (hD c q)).trans_eq (mul_one _))

/-- Combining a genuine coordinate Lipschitz estimate with the article's
literal block condition gives uniform norming. The analytic Lipschitz
estimate is stated openly as a premise of this transfer theorem. -/
theorem continuousNorming_half_of_blockCondition_and_coordinate_lipschitz
    {d n : ℕ} (G : SegmentedGrid d) (Y : Fin n → Point d)
    {K : ℝ} (hK : 0 ≤ K)
    (hblock : SegmentedBlockCondition (2 * (d : ℝ) * K) G n)
    (hLip : ∀ c (k : G.Row) q (z : Point d), z ∈ G.unitCell k →
      ∀ u ∈ Set.Icc (G.rowPoint k q) (G.rowPoint k q + 1),
      |‖exponentialSum Y c (Function.update z q u)‖ ^ 2 -
        ‖exponentialSum Y c z‖ ^ 2| ≤
        (K * (n : ℝ) ^ (4 * d + 5) / (G.minThickLength : ℝ) ^ (d + 1) *
          continuousEnergy G Y c) * |u-z q|) :
    ContinuousNorming G Y (1 / 2) := by
  let A : ℝ := K * (n : ℝ) ^ (4 * d + 5) / (G.minThickLength : ℝ) ^ (d + 1)
  have hL : (0 : ℝ) < G.minThickLength := by
    have h := G.minLength_add_one_le_minThickLength
    exact_mod_cast (show 0 < G.minThickLength by omega)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  apply continuousNorming_half_of_coordinate_lipschitz G Y
    (fun c _ => A * continuousEnergy G Y c)
    (fun c _ => mul_nonneg hA (continuousEnergy_nonneg G Y c)) hLip
  intro c
  have ht := blockCondition_thickened_power_threshold
    (by positivity : 0 ≤ 2 * (d : ℝ) * K) G hblock
  have hhalf : (G.rowCount : ℝ) * d * A ≤ 1 / 2 := by
    dsimp [A]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (pow_pos hL (d+1))).2
    nlinarith
  calc
    _ = ((G.rowCount : ℝ) * d * A) * continuousEnergy G Y c := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ (1 / 2 : ℝ) * continuousEnergy G Y c :=
      mul_le_mul_of_nonneg_right hhalf (continuousEnergy_nonneg G Y c)

end
end LeanNumDetect.MultiTuran
