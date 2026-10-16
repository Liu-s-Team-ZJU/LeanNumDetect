import MultiTuran.Turan.GeometryDensity
import MultiTuran.Preliminaries.Energy
import MultiTuran.Nikolskii.NikolskiiIntervals

/-! # Multidimensional reduction to a one-dimensional measurable-set comparison

The only analytic premise in this module is the explicitly quantified scalar
comparison. The convex geometry, polar disintegration, ray restriction and
linear dependence on the dimension are all proved in this import chain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The precise scalar comparison used by the ray reduction. This definition
is a hypothesis interface, not an assertion that the comparison holds. -/
def OneDimensionalTuranComparison (C₀ : ℝ) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    (a b : ℝ), a < b → ∀ (E : Set ℝ), MeasurableSet E → E ⊆ Icc a b →
      0 < volume E → ∀ (M : ℝ), 0 ≤ M →
        (∀ t ∈ E, ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ≤ M) →
        ∀ t ∈ Icc a b,
          ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ≤
            M * (C₀*(b-a)/(volume E).toReal)^(n-1)

/-- A scalar measurable-set comparison implies the multidimensional estimate
on every compact convex body, with the exact factor `2*C₀*d`. -/
theorem multidim_norm_le_of_oneDimensional_comparison {C₀ : ℝ} (hC₀ : 0 < C₀)
    (h1d : OneDimensionalTuranComparison C₀) {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {B Z : Set (Point d)} (hcompact : IsCompact B) (hconvex : Convex ℝ B)
    (hZ : MeasurableSet Z) (hZB : Z ⊆ B) (hZpos : 0 < volume Z)
    (Y : Fin n → Point d) (c : Fin n → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ Z, ‖exponentialSum Y c z‖ ≤ M) :
    ∀ x ∈ B, ‖exponentialSum Y c x‖ ≤
      M * (2*C₀*(d : ℝ)*(volume B).toReal/(volume Z).toReal)^(n-1) := by
  intro x hx
  obtain ⟨u,R,hu,hR,hsegment,hE,hEpos,hsub,hratio⟩ :=
    exists_ray_dense_segment hd hcompact hconvex hZ hZB hZpos hx
  let frequency : Fin n → ℝ := fun j => ∑ q, u q * Y j q
  let a : Fin n → ℂ := fun j => c j * Complex.exp
    (Complex.I * ((∑ q, x q * Y j q : ℝ) : ℂ))
  have hscalar := h1d n hn frequency a 0 R hR (raySection Z x u) hE hsub hEpos M hM
    (fun t ht => by
      rw [show ExponentialSumEstimates.exponentialSum frequency a t =
          exponentialSum Y c (x+t•u) from (exponentialSum_ray Y c x u t).symm]
      exact hbound _ ht.2) 0 ⟨le_rfl,hR.le⟩
  rw [show ExponentialSumEstimates.exponentialSum frequency a 0 =
      exponentialSum Y c x from by simpa only [zero_smul, add_zero, frequency, a] using (exponentialSum_ray Y c x u 0).symm] at hscalar
  have hBpos : 0 < volume B := hZpos.trans_le (measure_mono hZB)
  have hBr : 0 < (volume B).toReal :=
    ENNReal.toReal_pos (ne_of_gt hBpos) hcompact.measure_lt_top.ne
  have hZfin : volume Z ≠ ∞ :=
    ne_top_of_le_ne_top hcompact.measure_lt_top.ne (measure_mono hZB)
  have hZr : 0 < (volume Z).toReal := ENNReal.toReal_pos (ne_of_gt hZpos) hZfin
  have hEfin : volume (raySection Z x u) ≠ ∞ :=
    ne_top_of_le_ne_top (show volume (Icc (0:ℝ) R) ≠ ∞ by simp) (measure_mono hsub)
  have hEr : 0 < (volume (raySection Z x u)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hEpos) hEfin
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcross := (div_le_div_iff₀ (by positivity : 0 < 2*(d:ℝ)*(volume B).toReal) hR).mp hratio
  have hquot : R/(volume (raySection Z x u)).toReal ≤
      2*(d : ℝ)*(volume B).toReal/(volume Z).toReal := by
    apply (div_le_div_iff₀ hEr hZr).2
    nlinarith only [hcross]
  have hcoef : C₀*(R-0)/(volume (raySection Z x u)).toReal ≤
      2*C₀*(d : ℝ)*(volume B).toReal/(volume Z).toReal := by
    calc
      _ = C₀*(R/(volume (raySection Z x u)).toReal) := by ring
      _ ≤ C₀*(2*(d : ℝ)*(volume B).toReal/(volume Z).toReal) :=
        mul_le_mul_of_nonneg_left hquot hC₀.le
      _ = _ := by ring
  exact hscalar.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hcoef (n-1)) hM)

/-- The actual supremum version of the same proved geometric reduction. -/
theorem multidim_supNorm_le_of_oneDimensional_comparison {C₀ : ℝ} (hC₀ : 0 < C₀)
    (h1d : OneDimensionalTuranComparison C₀) {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {B Z : Set (Point d)} (hcompact : IsCompact B) (hconvex : Convex ℝ B)
    (hZ : MeasurableSet Z) (hZB : Z ⊆ B) (hZpos : 0 < volume Z)
    (Y : Fin n → Point d) (c : Fin n → ℂ) :
    setSupNorm (exponentialSum Y c) B ≤
      (2*C₀*(d : ℝ)*(volume B).toReal/(volume Z).toReal)^(n-1) *
        setSupNorm (exponentialSum Y c) Z := by
  have hbdd : BddAbove ((fun z => ‖exponentialSum Y c z‖) '' Z) :=
    (hcompact.bddAbove_image (continuous_exponentialSum Y c).norm.continuousOn).mono
      (Set.image_mono hZB)
  have hM : 0 ≤ setSupNorm (exponentialSum Y c) Z := by
    unfold setSupNorm
    exact Real.sSup_nonneg (fun _ hz => by rcases hz with ⟨z,hz,rfl⟩; exact norm_nonneg _)
  have hpoint := multidim_norm_le_of_oneDimensional_comparison hC₀ h1d hd hn
    hcompact hconvex hZ hZB hZpos Y c hM (fun z hz => le_csSup hbdd ⟨z,hz,rfl⟩)
  apply Real.sSup_le
  · rintro v ⟨x,hx,rfl⟩
    simpa only [mul_comm] using hpoint x hx
  · exact mul_nonneg (by positivity) hM


/-- The exact filling-ratio form required by the segmented-array transfer.
Only the displayed universal one-dimensional comparison remains a premise. -/
theorem aperture_supNorm_le_of_oneDimensional_comparison {C₀ : ℝ} (hC₀ : 0 < C₀)
    (h1d : OneDimensionalTuranComparison C₀) {d n : ℕ} (G : SegmentedGrid d)
    (hn : 0 < n) (Y : Fin n → Point d) (c : Fin n → ℂ) :
    setSupNorm (exponentialSum Y c) G.apertureBox ≤
      ((2*C₀)*(d : ℝ)/G.fillingRatio)^(n-1) *
        setSupNorm (exponentialSum Y c) G.thickening := by
  have hconvex : Convex ℝ G.apertureBox := convex_pi (fun _ _ => convex_Icc _ _)
  have hvol : 0 < volume G.thickening := by
    rw [G.thickening_volume]
    exact_mod_cast G.rowCount_pos
  have h := multidim_supNorm_le_of_oneDimensional_comparison hC₀ h1d
    G.dimension_pos hn G.apertureBox_isCompact hconvex G.thickening_measurableSet
    G.thickening_subset_apertureBox hvol Y c
  rw [G.apertureBox_volume_toReal, G.thickening_volume_toReal] at h
  have hc : (2*C₀)*(d : ℝ)/G.fillingRatio =
      2*C₀*(d : ℝ)*G.boxVolume/(G.rowCount : ℝ) := by
    rw [SegmentedGrid.fillingRatio, div_div_eq_mul_div]
  rw [hc]
  exact h

end
end LeanNumDetect.MultiTuran
