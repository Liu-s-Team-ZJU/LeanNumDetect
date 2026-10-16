import MultiTuran.Turan.GeometryPolar

/-! # Selecting a ray with large relative one-dimensional measure

Polar disintegration and convexity give the geometric part of the
multidimensional Turan reduction. A factor two is allowed in the absolute
constant so that no attainment assumption on a directional density is needed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ENNReal

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- A finite-volume set and a positive-volume subset have a direction whose
weighted ray density exceeds half their total volume ratio. -/
theorem exists_direction_weighted_density {d : ℕ} (hd : 0 < d)
    {B Z : Set (Point d)} (hB : MeasurableSet B) (hZ : MeasurableSet Z)
    (hZB : Z ⊆ B) (hBfin : volume B ≠ ∞) (hZpos : 0 < volume Z) (x : Point d) :
    ∃ u : sphere (0 : Point d) 1,
      ENNReal.ofReal ((volume Z).toReal / (2*(volume B).toReal)) *
          weightedRayMass (d-1) B x u.val < weightedRayMass (d-1) Z x u.val := by
  have hZfin : volume Z ≠ ∞ := ne_top_of_le_ne_top hBfin (measure_mono hZB)
  have hBpos : 0 < volume B := hZpos.trans_le (measure_mono hZB)
  have hBr : 0 < (volume B).toReal := ENNReal.toReal_pos (ne_of_gt hBpos) hBfin
  have hZr : 0 < (volume Z).toReal := ENNReal.toReal_pos (ne_of_gt hZpos) hZfin
  let β : ℝ := (volume Z).toReal / (2*(volume B).toReal)
  have hβ : 0 < β := div_pos hZr (mul_pos (by norm_num) hBr)
  by_contra hnone
  push Not at hnone
  have hi := lintegral_mono (μ := (volume : Measure (Point d)).toSphere) hnone
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← volume_eq_lintegral_weightedRayMass hd hZ x,
    ← volume_eq_lintegral_weightedRayMass hd hB x] at hi
  have hir := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin) hi
  change (volume Z).toReal ≤
    (ENNReal.ofReal β * volume B).toReal at hir
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hβ.le] at hir
  have hhalf : β * (volume B).toReal = (volume Z).toReal / 2 := by
    dsimp [β]
    field_simp
  rw [hhalf] at hir
  linarith

/-- A genuine unit ray through any point of a compact convex body contains a
segment on which a measurable subset has at least its global relative volume
ratio divided by twice the dimension. -/
theorem exists_ray_dense_segment {d : ℕ} (hd : 0 < d)
    {B Z : Set (Point d)} (hcompact : IsCompact B) (hconvex : Convex ℝ B)
    (hZ : MeasurableSet Z) (hZB : Z ⊆ B) (hZpos : 0 < volume Z)
    {x : Point d} (hx : x ∈ B) :
    ∃ u : Point d, ∃ R : ℝ, ‖u‖ = 1 ∧ 0 < R ∧
      (∀ r ∈ Icc (0 : ℝ) R, x+r•u ∈ B) ∧
      MeasurableSet (raySection Z x u) ∧
      0 < volume (raySection Z x u) ∧
      raySection Z x u ⊆ Icc 0 R ∧
      (volume Z).toReal / (2*(d : ℝ)*(volume B).toReal) ≤
        (volume (raySection Z x u)).toReal / R := by
  have hBfin : volume B ≠ ∞ := hcompact.measure_lt_top.ne
  have hB : MeasurableSet B := hcompact.measurableSet
  have hZfin : volume Z ≠ ∞ := ne_top_of_le_ne_top hBfin (measure_mono hZB)
  have hBpos : 0 < volume B := hZpos.trans_le (measure_mono hZB)
  have hBr : 0 < (volume B).toReal := ENNReal.toReal_pos (ne_of_gt hBpos) hBfin
  have hZr : 0 < (volume Z).toReal := ENNReal.toReal_pos (ne_of_gt hZpos) hZfin
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨u,hdensity⟩ := exists_direction_weighted_density hd hB hZ hZB hBfin hZpos x
  have hu : ‖u.val‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using u.property
  obtain ⟨R,hR,hBR,hsection,hsegment⟩ := exists_ray_radius hcompact hconvex hx hu
  have hZsection : raySection Z x u.val ⊆ Ioc 0 R := by
    intro r hr
    rw [← hsection]
    exact ⟨hr.1,hZB hr.2⟩
  have hRpos : 0 < R := by
    by_contra hnot
    have hRzero : R = 0 := le_antisymm (le_of_not_gt hnot) hR
    have hzempty : raySection Z x u.val = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro r hr
      have h := hZsection hr
      rw [hRzero] at h
      exact (not_lt_of_ge h.2) h.1
    simp only [weightedRayMass, hzempty, Measure.restrict_empty, lintegral_zero_measure] at hdensity
    exact (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ _ from bot_le)) hdensity
  have hlinefin : volume (raySection Z x u.val) ≠ ∞ := by
    apply ne_top_of_le_ne_top (show volume (Ioc (0:ℝ) R) ≠ ∞ by simp)
    exact measure_mono hZsection
  have hweightedB := weightedRayMass_of_section_eq_Ioc (d-1) x u.val hR hsection
  have hdim : d-1+1=d := Nat.sub_add_cancel hd
  rw [hdim] at hweightedB
  rw [hweightedB] at hdensity
  have hupper := weightedRayMass_le_endpoint_weight_mul_length (d-1) hZ x u.val hR hZsection
  have hstrict := hdensity.trans_le hupper
  have hβ : 0 ≤ (volume Z).toReal / (2*(volume B).toReal) := by positivity
  have hp : 0 ≤ R^(d-1) := pow_nonneg hR _
  have hpow : 0 ≤ R^d/(d : ℝ) := div_nonneg (pow_nonneg hR _) hdR.le
  have hreal := (ENNReal.toReal_lt_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlinefin)).2 hstrict
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hβ, ENNReal.toReal_ofReal hp,
    ENNReal.toReal_ofReal hpow] at hreal
  have hpower : R^d = R^(d-1)*R := by rw [← pow_succ, hdim]
  rw [hpower] at hreal
  have hfactor : 0 < R^(d-1) := pow_pos hRpos _
  have hcancel : ((volume Z).toReal / (2*(volume B).toReal)) * R / (d : ℝ) <
      (volume (raySection Z x u.val)).toReal := by
    have he : (volume Z).toReal / (2*(volume B).toReal) *
        (R^(d-1)*R/(d : ℝ)) =
        R^(d-1) * ((volume Z).toReal / (2*(volume B).toReal)*R/(d : ℝ)) := by ring
    rw [he] at hreal
    exact (mul_lt_mul_iff_right₀ hfactor).mp hreal
  have hlinepos : 0 < (volume (raySection Z x u.val)).toReal :=
    lt_of_lt_of_le (div_pos (mul_pos (div_pos hZr (by positivity)) hRpos) hdR)
      hcancel.le
  refine ⟨u.val,R,hu,hRpos,hsegment,measurableSet_raySection hZ x u.val,
    ENNReal.toReal_pos_iff.mp hlinepos |>.1,?_,?_⟩
  · exact hZsection.trans Ioc_subset_Icc_self
  · apply (le_div_iff₀ hRpos).2
    have he : (volume Z).toReal / (2*(d : ℝ)*(volume B).toReal)*R =
        ((volume Z).toReal / (2*(volume B).toReal))*R/(d : ℝ) := by ring
    rw [he]
    exact hcancel.le

end
end LeanNumDetect.MultiTuran
