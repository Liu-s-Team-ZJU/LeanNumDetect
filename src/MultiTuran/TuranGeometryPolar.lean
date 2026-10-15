import MultiTuran.TuranGeometryRay
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Group.LIntegral

/-! # Polar disintegration for actual ray sections

This is the geometric reduction used in the proof of Brudnyi--Yomdin,
Theorem 3.2 (arXiv:1312.6050). The measure on directions is mathlib's Haar
sphere measure; the radial density is the genuine power `r^(d-1)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ENNReal

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The weighted radial mass in polar coordinates. -/
def weightedRayMass {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (S : Set E) (x u : E) : ℝ≥0∞ :=
  ∫⁻ r in raySection S x u, ENNReal.ofReal (r^k)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Measurability of a literal ray section. -/
theorem measurableSet_raySection {S : Set E} (hS : MeasurableSet S) (x u : E) :
    MeasurableSet (raySection S x u) :=
  measurableSet_Ioi.inter (hS.preimage
    (continuous_const.add (continuous_id.smul continuous_const)).measurable)

/-- The same mass expressed on the positive radial subtype with its density
measure, exactly as in generalized polar coordinates. -/
theorem weightedRayMass_eq_positive_integral (k : ℕ) {S : Set E}
    (hS : MeasurableSet S) (x u : E) :
    weightedRayMass k S x u =
      ∫⁻ r : Ioi (0 : ℝ), S.indicator (fun _ => (1 : ℝ≥0∞)) (x + r.val • u)
        ∂Measure.volumeIoiPow k := by
  unfold weightedRayMass Measure.volumeIoiPow
  have hw : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.val^k)) := by
    fun_prop
  have hg : Measurable (fun r : Ioi (0 : ℝ) =>
      S.indicator (fun _ => (1:ℝ≥0∞)) (x+r.val•u)) := by
    apply (measurable_const.indicator hS).comp
    exact (continuous_const.add (continuous_subtype_val.smul continuous_const)).measurable
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hg]
  change (∫⁻ r in raySection S x u, ENNReal.ofReal (r^k)) =
    ∫⁻ r : Ioi (0 : ℝ),
      (fun t : ℝ => ENNReal.ofReal (t^k) * S.indicator (fun _ => (1:ℝ≥0∞)) (x+t•u)) r.val
      ∂Measure.comap Subtype.val volume
  rw [lintegral_subtype_comap (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t : ℝ => ENNReal.ofReal (t^k) * S.indicator (fun _ => (1:ℝ≥0∞)) (x+t•u))]
  rw [← lintegral_indicator (measurableSet_raySection hS x u),
    ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro r
  by_cases hp : 0 < r <;> by_cases hm : x + r • u ∈ S <;>
    simp [raySection, hp, hm]

/-- Exact polar disintegration of Lebesgue volume around an arbitrary point. -/
theorem volume_eq_lintegral_weightedRayMass {d : ℕ} (hd : 0 < d)
    {S : Set (Point d)} (hS : MeasurableSet S) (x : Point d) :
    volume S = ∫⁻ u : sphere (0 : Point d) 1,
      weightedRayMass (d-1) S x u.val ∂(volume : Measure (Point d)).toSphere := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let f : Point d → ℝ≥0∞ := fun y => S.indicator (fun _ => 1) (x+y)
  let H := homeomorphUnitSphereProd (Point d)
  have hp := (volume : Measure (Point d)).measurePreserving_homeomorphUnitSphereProd
    |>.lintegral_comp_emb (Homeomorph.measurableEmbedding H)
      (fun p => f ((H.symm p).val))
  simp only [H, Homeomorph.symm_apply_apply] at hp
  rw [lintegral_subtype_comap (measurableSet_singleton (0 : Point d)).compl,
    restrict_compl_singleton] at hp
  have htrans : (∫⁻ y, f y) = volume S := by
    dsimp [f]
    rw [lintegral_add_left_eq_self (μ := volume)]
    exact lintegral_indicator_one hS
  rw [htrans] at hp
  have hF : Measurable (fun p : sphere (0 : Point d) 1 × Ioi (0 : ℝ) =>
      S.indicator (fun _ => (1 : ℝ≥0∞)) (x + p.2.val • p.1.val)) :=
    (measurable_const.indicator hS).comp
      (continuous_const.add ((continuous_subtype_val.comp continuous_snd).smul
        (continuous_subtype_val.comp continuous_fst))).measurable
  simp only [homeomorphUnitSphereProd_symm_apply_coe, f,
    Module.finrank_fin_fun] at hp
  rw [lintegral_prod _ hF.aemeasurable] at hp
  rw [hp]
  apply lintegral_congr
  intro u
  exact (weightedRayMass_eq_positive_integral (d-1) hS x u.val).symm

/-- On a bounded ray section, the radial weight is bounded by its endpoint
weight times the ordinary one-dimensional length. -/
theorem weightedRayMass_le_endpoint_weight_mul_length (k : ℕ) {S : Set E}
    (hS : MeasurableSet S) (x u : E) {R : ℝ} (hR : 0 ≤ R)
    (hbound : raySection S x u ⊆ Ioc 0 R) :
    weightedRayMass k S x u ≤ ENNReal.ofReal (R^k) * volume (raySection S x u) := by
  unfold weightedRayMass
  calc
    _ ≤ ∫⁻ _r in raySection S x u, ENNReal.ofReal (R^k) := by
      apply setLIntegral_mono' (measurableSet_raySection hS x u)
      intro r hr
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hbound hr).1.le (hbound hr).2 k)
    _ = _ := by simp [mul_comm]


/-- The radial mass of the full ray interval, including its exact dimension
factor. -/
theorem weightedRayMass_of_section_eq_Ioc (k : ℕ) {S : Set E} (x u : E)
    {R : ℝ} (hR : 0 ≤ R) (hsection : raySection S x u = Ioc 0 R) :
    weightedRayMass k S x u = ENNReal.ofReal (R^(k+1)/((k+1:ℕ):ℝ)) := by
  unfold weightedRayMass
  rw [hsection]
  have hi : IntegrableOn (fun r : ℝ => r^k) (Ioc 0 R) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).1
      ((continuous_id.pow k).intervalIntegrable 0 R)
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) R)] (fun r : ℝ => r^k) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact pow_nonneg hr.1.le k
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    ← intervalIntegral.integral_of_le hR, integral_pow]
  simp

end
end LeanNumDetect.MultiTuran
