import MultiTuran.TuranGeometryTransfer
import MultiTuran.TuranGeometricBase
import MultiTuran.NikolskiiAffine

/-! The literal affine interval transfer for measurable-set Turan estimates.
The normalized comparison is an explicit conversion input; its eventual
analytic proof is supplied independently. All set measures and phase changes
in this module are actual Lebesgue quantities and exponential sums. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- Translating and dilating a measured set to the centred unit interval has
exactly the inverse-length volume factor. -/
theorem volume_preimage_affine_pos {L : ℝ} (hL : 0 < L) (a : ℝ) (E : Set ℝ) :
    volume ((fun u : ℝ => L*u+a) ⁻¹' E) = ENNReal.ofReal L⁻¹ * volume E := by
  change volume ((L*·) ⁻¹' ((fun u : ℝ => u+a) ⁻¹' E)) = _
  rw [Real.volume_preimage_mul_left hL.ne',measure_preimage_add_right]
  rw [abs_of_pos (inv_pos.mpr hL)]

/-- The genuine scalar comparison on the centred unit interval transfers to
every bounded interval, with the exact original-set volume in its coefficient. -/
theorem oneDimensionalTuranComparison_of_unit_norm_bound {C₀ : ℝ}
    (hunit : ∀ (n : ℕ), 0 < n → ∀ (frequency : Fin n → ℝ) (c : Fin n → ℂ)
      (E : Set ℝ), MeasurableSet E → E ⊆ Icc (-1/2 : ℝ) (1/2) →
        0 < volume E → ∀ (M : ℝ), 0 ≤ M →
          (∀ t ∈ E, ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ≤ M) →
          ∀ t ∈ Icc (-1/2 : ℝ) (1/2),
            ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ≤
              M*(C₀/(volume E).toReal)^(n-1)) :
    OneDimensionalTuranComparison C₀ := by
  intro n hn frequency c a b hab E hE hEsub hEpos M hM hbound t ht
  let L := b-a
  let mid := (a+b)/2
  have hL : 0 < L := sub_pos.mpr hab
  let E' : Set ℝ := (fun u : ℝ => L*u+mid) ⁻¹' E
  let frequency' : Fin n → ℝ := fun j => L*frequency j
  let c' : Fin n → ℂ := fun j => c j * Complex.exp (Complex.I * ((mid*frequency j : ℝ) : ℂ))
  have hrepr (u : ℝ) : ExponentialSumEstimates.exponentialSum frequency' c' u =
      ExponentialSumEstimates.exponentialSum frequency c (L*u+mid) :=
    ExponentialSumEstimates.exponentialSum_affine frequency c mid L u
  have hE'meas : MeasurableSet E' := hE.preimage (by fun_prop)
  have hE'sub : E' ⊆ Icc (-1/2 : ℝ) (1/2) := by
    intro u hu
    have hmem := hEsub hu
    change a ≤ L*u+mid ∧ L*u+mid ≤ b at hmem
    have hlow : L*(-1/2) ≤ L*u := by dsimp [L,mid] at *; linarith [hmem.1]
    have hupp : L*u ≤ L*(1/2) := by dsimp [L,mid] at *; linarith [hmem.2]
    exact ⟨(mul_le_mul_iff_right₀ hL).mp hlow,(mul_le_mul_iff_right₀ hL).mp hupp⟩
  have hvol := volume_preimage_affine_pos hL mid E
  change volume E' = ENNReal.ofReal L⁻¹ * volume E at hvol
  have hE'pos : 0 < volume E' := by
    rw [hvol]
    positivity
  have hEfin : volume E ≠ ∞ :=
    ne_top_of_le_ne_top (by simp : volume (Icc a b) ≠ ∞) (measure_mono hEsub)
  have hEr : 0 < (volume E).toReal := ENNReal.toReal_pos (ne_of_gt hEpos) hEfin
  have hvolR : (volume E').toReal = L⁻¹*(volume E).toReal := by
    rw [hvol,ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr hL.le)]
  let u : ℝ := (t-mid)/L
  have hu : u ∈ Icc (-1/2 : ℝ) (1/2) := by
    have hlow : L*(-1/2) ≤ t-mid := by dsimp [L,mid]; linarith [ht.1]
    have hupp : t-mid ≤ L*(1/2) := by dsimp [L,mid]; linarith [ht.2]
    constructor
    · exact (le_div_iff₀ hL).mpr (by nlinarith only [hlow])
    · exact (div_le_iff₀ hL).mpr (by nlinarith only [hupp])
  have harg : L*u+mid=t := by dsimp [u]; field_simp <;> ring
  have hb' : ∀ s ∈ E', ‖ExponentialSumEstimates.exponentialSum frequency' c' s‖ ≤ M := by
    intro s hs
    rw [hrepr]
    exact hbound _ hs
  have h := hunit n hn frequency' c' E' hE'meas hE'sub hE'pos M hM hb' u hu
  rw [hrepr,harg] at h
  have hcoef : C₀/(volume E').toReal = C₀*(b-a)/(volume E).toReal := by
    rw [hvolR]
    dsimp [L]
    field_simp
  rwa [hcoef] at h

/-- An actual normalized geometric-mean estimate and actual logarithmic
regularity imply the scalar comparison required by the multidimensional
geometry reduction. No geometric-mean scaling premise is used. -/
theorem oneDimensionalTuranComparison_of_unit_geometric_bound {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hgeometric : ∀ (E : Set ℝ), MeasurableSet E → E ⊆ Icc (-1/2 : ℝ) (1/2) →
      0 < volume E → ∀ (n : ℕ), 0 < n → ∀ (frequency : Fin n → ℝ) (c : Fin n → ℂ),
        ∀ t ∈ Icc (-1/2 : ℝ) (1/2),
          ‖ExponentialSumEstimates.exponentialSum frequency c t‖ ≤
            (C₀/(volume E).toReal)^(n-1)*
              geometricMean E (ExponentialSumEstimates.exponentialSum frequency c))
    (hregular : ∀ (E : Set ℝ), MeasurableSet E → E ⊆ Icc (-1/2 : ℝ) (1/2) →
      0 < volume E → ∀ (n : ℕ), 0 < n → ∀ (frequency : Fin n → ℝ) (c : Fin n → ℂ),
        ExponentialSumEstimates.exponentialSum frequency c ≠ 0 →
          LogRegular (volume.restrict E) (ExponentialSumEstimates.exponentialSum frequency c)) :
    OneDimensionalTuranComparison C₀ := by
  apply oneDimensionalTuranComparison_of_unit_norm_bound
  intro n hn frequency c E hE hEsub hEpos M hM hbound t ht
  have hEfin : volume E < ∞ :=
    lt_of_le_of_lt (measure_mono hEsub) (by simp : volume (Icc (-1/2 : ℝ) (1/2)) < ∞)
  have hgeom := geometricMean_le_of_bound hE hEfin hEpos
    (hregular E hE hEsub hEpos n hn frequency c) hM hbound
  have hEr : 0 < (volume E).toReal := ENNReal.toReal_pos (ne_of_gt hEpos) hEfin.ne
  calc
    _ ≤ (C₀/(volume E).toReal)^(n-1)*
        geometricMean E (ExponentialSumEstimates.exponentialSum frequency c) :=
      hgeometric E hE hEsub hEpos n hn frequency c t ht
    _ ≤ (C₀/(volume E).toReal)^(n-1)*M :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by ring

end
end LeanNumDetect.MultiTuran
