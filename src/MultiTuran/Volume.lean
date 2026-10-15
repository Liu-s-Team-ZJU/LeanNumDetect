import MultiTuran.SegmentedGrid
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Lebesgue geometry of segmented products

The thickening is the actual finite union of closed intervals in each
coordinate. Passing to half-open intervals removes only finitely many null
endpoints; their disjointness then computes its true Lebesgue measure.
The multidimensional identity uses the Lebesgue product measure on `Point d`.
-/

set_option autoImplicit false
open scoped BigOperators ENNReal
open Set MeasureTheory Function

namespace LeanNumDetect.MultiTuran.SegmentedGrid
noncomputable section

variable {d : ℕ} (G : SegmentedGrid d)

/-- The genuine aperture box `J = ∏q [0,N_q]`. -/
def apertureBox : Set (Point d) :=
  Set.pi Set.univ (fun q => Set.Icc (0 : ℝ) (G.aperture q : ℝ))

theorem coordinateThickening_isCompact (q : Fin d) :
    IsCompact (G.coordinateThickening q) :=
  isCompact_iUnion fun _ => isCompact_Icc

theorem coordinateThickening_measurableSet (q : Fin d) :
    MeasurableSet (G.coordinateThickening q) :=
  (G.coordinateThickening_isCompact q).isClosed.measurableSet

theorem thickening_isCompact : IsCompact G.thickening :=
  isCompact_univ_pi G.coordinateThickening_isCompact

theorem thickening_measurableSet : MeasurableSet G.thickening :=
  G.thickening_isCompact.isClosed.measurableSet

theorem apertureBox_isCompact : IsCompact G.apertureBox :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem apertureBox_measurableSet : MeasurableSet G.apertureBox :=
  G.apertureBox_isCompact.isClosed.measurableSet

theorem coordinateThickening_subset_Icc (q : Fin d) :
    G.coordinateThickening q ⊆ Set.Icc (0 : ℝ) (G.aperture q : ℝ) := by
  intro t ht
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp ht
  have hend : G.start q m + G.thickLength q m ≤ G.aperture q := by
    have h := G.block_end_le_last q m
    unfold thickLength aperture
    omega
  exact ⟨(Nat.cast_nonneg _).trans hm.1, hm.2.trans (by exact_mod_cast hend)⟩

theorem thickening_subset_apertureBox : G.thickening ⊆ G.apertureBox := by
  intro t ht q hq
  exact G.coordinateThickening_subset_Icc q (ht q hq)

private theorem coordinate_halfOpen_pairwise_disjoint (q : Fin d) :
    Pairwise (Disjoint on (fun m : G.Block q =>
      Set.Ico (G.start q m : ℝ) (G.start q m + G.thickLength q m : ℕ))) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro t hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hnat : G.start q i + G.thickLength q i ≤ G.start q j := by
      simpa [thickLength, Nat.add_assoc] using G.separated q i j hlt
    have hreal : ((G.start q i + G.thickLength q i : ℕ) : ℝ) ≤ G.start q j := by
      exact_mod_cast hnat
    exact (not_lt_of_ge (hreal.trans hj.1)) hi.2
  · have hnat : G.start q j + G.thickLength q j ≤ G.start q i := by
      simpa [thickLength, Nat.add_assoc] using G.separated q j i hgt
    have hreal : ((G.start q j + G.thickLength q j : ℕ) : ℝ) ≤ G.start q i := by
      exact_mod_cast hnat
    exact (not_lt_of_ge (hreal.trans hi.1)) hj.2

/-- Every thickened coordinate row contributes exactly one unit of measure. -/
theorem coordinateThickening_volume (q : Fin d) :
    volume (G.coordinateThickening q) = ((G.coordinateRows q).card : ℝ≥0∞) := by
  classical
  have hae :
      (⋃ m : G.Block q,
        Set.Ico (G.start q m : ℝ) (G.start q m + G.thickLength q m : ℕ))
        =ᵐ[volume] G.coordinateThickening q :=
    Filter.EventuallyEq.countable_iUnion fun _ => Ico_ae_eq_Icc
  calc
    _ = volume (⋃ m : G.Block q,
        Set.Ico (G.start q m : ℝ) (G.start q m + G.thickLength q m : ℕ)) :=
      measure_congr hae.symm
    _ = ∑' m : G.Block q,
        volume (Set.Ico (G.start q m : ℝ)
          (G.start q m + G.thickLength q m : ℕ)) :=
      measure_iUnion (G.coordinate_halfOpen_pairwise_disjoint q) fun _ => measurableSet_Ico
    _ = ∑ m : G.Block q, (G.thickLength q m : ℝ≥0∞) := by
      simp [Real.volume_Ico, Nat.cast_add]
    _ = ((G.coordinateRows q).card : ℝ≥0∞) := by
      rw [G.coordinateRows_card q]
      simp only [Nat.cast_sum]

theorem coordinateThickening_volume_toReal (q : Fin d) :
    (volume (G.coordinateThickening q)).toReal = ((G.coordinateRows q).card : ℝ) := by
  rw [G.coordinateThickening_volume, ENNReal.toReal_natCast]

/-- Product Lebesgue measure of the true multidimensional thickening. -/
theorem thickening_volume : volume G.thickening = (G.rowCount : ℝ≥0∞) := by
  rw [thickening, volume_pi_pi]
  simp only [G.coordinateThickening_volume, rowCount, Nat.cast_prod]

theorem thickening_volume_toReal : (volume G.thickening).toReal = (G.rowCount : ℝ) := by
  rw [G.thickening_volume, ENNReal.toReal_natCast]

theorem apertureBox_volume : volume G.apertureBox = ENNReal.ofReal G.boxVolume := by
  rw [apertureBox, volume_pi_pi]
  simp only [Real.volume_Icc, sub_zero]
  exact (ENNReal.ofReal_prod_of_nonneg (fun q _ => Nat.cast_nonneg (G.aperture q))).symm

theorem apertureBox_volume_toReal : (volume G.apertureBox).toReal = G.boxVolume := by
  rw [G.apertureBox_volume, ENNReal.toReal_ofReal G.boxVolume_pos.le]

/-- The manuscript filling ratio is the ratio of the actual Lebesgue volumes. -/
theorem fillingRatio_eq_volume_ratio :
    G.fillingRatio = (volume G.thickening).toReal / (volume G.apertureBox).toReal := by
  rw [G.thickening_volume_toReal, G.apertureBox_volume_toReal]
  rfl

end
end LeanNumDetect.MultiTuran.SegmentedGrid
