import MultiTuran.Turan.GeometryTransfer
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! The convex-body comparison also controls the literal essential
`L∞` norms on arbitrary measurable subsets, including null exceptional sets. -/

set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal

namespace LeanNumDetect.MultiTuran
noncomputable section

theorem multidim_norm_le_of_ae_oneDimensional_comparison {C₀ : ℝ} (hC₀ : 0 < C₀)
    (h1d : OneDimensionalTuranComparison C₀) {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {B Z : Set (Point d)} (hcompact : IsCompact B) (hconvex : Convex ℝ B)
    (hZ : MeasurableSet Z) (hZB : Z ⊆ B) (hZpos : 0 < volume Z)
    (Y : Fin n → Point d) (c : Fin n → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ z ∂volume.restrict Z, ‖exponentialSum Y c z‖ ≤ M) :
    ∀ x ∈ B, ‖exponentialSum Y c x‖ ≤
      M*(2*C₀*(d : ℝ)*(volume B).toReal/(volume Z).toReal)^(n-1) := by
  let Z' := Z ∩ {z | ‖exponentialSum Y c z‖ ≤ M}
  have hZ' : MeasurableSet Z' := hZ.inter
    (measurableSet_le (continuous_exponentialSum Y c).norm.measurable measurable_const)
  have hae : ∀ᵐ z ∂volume, z ∈ Z → ‖exponentialSum Y c z‖ ≤ M :=
    (ae_restrict_iff' hZ).mp hbound
  have heq : Z' =ᵐ[volume] Z := by
    filter_upwards [hae] with z hz
    exact propext ⟨fun h => h.1,fun h => ⟨h,hz h⟩⟩
  have hvol : volume Z'=volume Z := measure_congr heq
  have hp : 0 < volume Z' := by rwa [hvol]
  have h := multidim_norm_le_of_oneDimensional_comparison hC₀ h1d hd hn hcompact hconvex
    hZ' (fun z hz => hZB hz.1) hp Y c hM (fun z hz => hz.2)
  simpa only [hvol] using h

/-- The exact essential-supremum formulation of the convex-body estimate.
The scalar comparison remains explicit only in this reusable conversion. -/
theorem multidim_eLpNorm_top_le_of_oneDimensional_comparison {C₀ : ℝ} (hC₀ : 0 < C₀)
    (h1d : OneDimensionalTuranComparison C₀) {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {B Z : Set (Point d)} (hcompact : IsCompact B) (hconvex : Convex ℝ B)
    (hZ : MeasurableSet Z) (hZB : Z ⊆ B) (hZpos : 0 < volume Z)
    (Y : Fin n → Point d) (c : Fin n → ℂ) :
    eLpNorm (exponentialSum Y c) ∞ (volume.restrict B) ≤
      ENNReal.ofReal ((2*C₀*(d : ℝ)*(volume B).toReal/(volume Z).toReal)^(n-1))*
        eLpNorm (exponentialSum Y c) ∞ (volume.restrict Z) := by
  let f := exponentialSum Y c
  obtain ⟨M,hMb⟩ := hcompact.bddAbove_image (continuous_exponentialSum Y c).norm.continuousOn
  have hbound : ∀ᵐ z ∂volume.restrict Z, ‖f z‖ ≤ M := by
    filter_upwards [ae_restrict_mem hZ] with z hz
    exact hMb ⟨z,hZB hz,rfl⟩
  have hfinite : eLpNormEssSup f (volume.restrict Z) < ∞ :=
    eLpNormEssSup_lt_top_of_ae_bound hbound
  have hnorm : ∀ᵐ z ∂volume.restrict Z,
      ‖f z‖ ≤ (eLpNormEssSup f (volume.restrict Z)).toReal := by
    filter_upwards [ae_le_eLpNormEssSup (f:=f) (μ:=volume.restrict Z)] with z hz
    have h := ENNReal.toReal_mono hfinite.ne hz
    simpa using h
  have hpoint := multidim_norm_le_of_ae_oneDimensional_comparison hC₀ h1d hd hn
    hcompact hconvex hZ hZB hZpos Y c ENNReal.toReal_nonneg hnorm
  let A := (2*C₀*(d : ℝ)*(volume B).toReal/(volume Z).toReal)^(n-1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have haeb : ∀ᵐ x ∂volume.restrict B,
      ‖f x‖ ≤ (eLpNormEssSup f (volume.restrict Z)).toReal*A := by
    filter_upwards [ae_restrict_mem hcompact.measurableSet] with x hx
    exact hpoint x hx
  have hle := eLpNormEssSup_le_of_ae_bound haeb
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hfinite.ne] at hle
  simpa only [eLpNorm_exponent_top,f,A,mul_comm] using hle

end
end LeanNumDetect.MultiTuran
