import General.Probability.BoundedRowEstimates
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite measurable quantization of bounded complex rows. All decoding
centers lie in the original closed ball, so quantization preserves the exact
coordinate envelope. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u v

namespace LeanNumDetect.BoundedRieszConcentration

/-- A finite measurable row alphabet, with globally bounded decoding and
uniform approximation on the closed row ball. -/
structure BoundedRowQuantizer (N : ℕ) (K ε : ℝ) where
  alphabetSize : ℕ
  alphabet_pos : 0 < alphabetSize
  decoder : Fin alphabetSize → ComplexVector N
  quantize : ComplexVector N → Fin alphabetSize
  measurable_quantize : Measurable quantize
  decoder_bound : ∀ a, ‖decoder a‖ ≤ K
  approximation : ∀ x, ‖x‖ ≤ K → ‖x - decoder (quantize x)‖ ≤ ε

theorem boundedRowQuantizer_exists (N : ℕ) {K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 < ε) : Nonempty (BoundedRowQuantizer N K ε) := by
  classical
  let B := Metric.closedBall (0 : ComplexVector N) K
  have hcompact : IsCompact B := isCompact_closedBall _ _
  obtain ⟨t, htB, htfinite, htcover⟩ := hcompact.finite_cover_balls hε
  letI : Fintype t := htfinite.fintype
  let C := Fintype.card t
  let enumerate : Fin C ≃ t := (Fintype.equivFin t).symm
  let e : ℕ → ComplexVector N := fun k =>
    if hk : k < C then (enumerate ⟨k, hk⟩ : ComplexVector N) else 0
  let decoder : Fin (C + 1) → ComplexVector N := fun a => e a.val
  let truncate : ℕ → Fin (C + 1) := fun k =>
    if hk : k < C + 1 then ⟨k, hk⟩ else ⟨0, Nat.succ_pos C⟩
  let quantize : ComplexVector N → Fin (C + 1) := fun x =>
    truncate (SimpleFunc.nearestPtInd e C x)
  have hindex (x : ComplexVector N) : SimpleFunc.nearestPtInd e C x < C + 1 :=
    Nat.lt_succ_of_le (SimpleFunc.nearestPtInd_le e C x)
  have hdecode (x : ComplexVector N) : decoder (quantize x) = SimpleFunc.nearestPt e C x := by
    simp only [decoder, quantize, truncate, dif_pos (hindex x), SimpleFunc.nearestPt,
      SimpleFunc.map_apply]
  have he_bound (k : ℕ) : ‖e k‖ ≤ K := by
    dsimp [e]
    split_ifs with hk
    · have hball := htB (enumerate ⟨k, hk⟩).property
      simpa only [B, Metric.mem_closedBall, dist_zero_right] using hball
    · simpa only [norm_zero] using hK
  have hmeas : Measurable quantize :=
    (measurable_of_countable truncate).comp (SimpleFunc.nearestPtInd e C).measurable
  refine ⟨⟨C + 1, Nat.succ_pos C, decoder, quantize, hmeas,
    fun a => he_bound a.val, ?_⟩⟩
  intro x hx
  have hxB : x ∈ B := by simpa only [B, Metric.mem_closedBall, dist_zero_right] using hx
  have hxc := htcover hxB
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hxc
  obtain ⟨y, hy, hxy⟩ := hxc
  let a : Fin C := enumerate.symm ⟨y, hy⟩
  have hea : e a.val = y := by
    simp only [e, dif_pos a.isLt]
    exact congrArg Subtype.val (enumerate.apply_symm_apply ⟨y, hy⟩)
  have hn := SimpleFunc.edist_nearestPt_le e x (Nat.le_of_lt a.isLt)
  rw [hea] at hn
  have hdist : dist (SimpleFunc.nearestPt e C x) x ≤ dist y x :=
    by simpa only [dist_edist] using ENNReal.toReal_mono (edist_ne_top y x) hn
  rw [hdecode, ← dist_eq_norm]
  have hdist' : dist x (SimpleFunc.nearestPt e C x) ≤ dist x y := by
    simpa only [dist_comm] using hdist
  exact hdist'.trans hxy.le

namespace BoundedRowQuantizer

variable {N : ℕ} {K ε : ℝ} (Q : BoundedRowQuantizer N K ε)

theorem measurable_decoder : Measurable Q.decoder := measurable_of_countable _

def decoded (x : ComplexVector N) : ComplexVector N := Q.decoder (Q.quantize x)

theorem measurable_decoded : Measurable Q.decoded :=
  Q.measurable_decoder.comp Q.measurable_quantize

theorem decoded_norm_le (x : ComplexVector N) : ‖Q.decoded x‖ ≤ K :=
  Q.decoder_bound (Q.quantize x)

theorem decoded_coordinate_norm_le (x : ComplexVector N) (j : Fin N) :
    ‖Q.decoded x j‖ ≤ K := (norm_le_pi_norm (Q.decoded x) j).trans (Q.decoded_norm_le x)

theorem decoded_error_le (x : ComplexVector N) (hx : ‖x‖ ≤ K) :
    ‖x - Q.decoded x‖ ≤ ε := Q.approximation x hx

theorem aemeasurable_quantized {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ComplexVector N) (hX : AEMeasurable X μ) :
    AEMeasurable (fun ω => Q.quantize (X ω)) μ :=
  Q.measurable_quantize.comp_aemeasurable hX

theorem aemeasurable_decoded {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ComplexVector N) (hX : AEMeasurable X μ) :
    AEMeasurable (fun ω => Q.decoded (X ω)) μ :=
  Q.measurable_decoded.comp_aemeasurable hX

theorem ae_decoded_error_le {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ComplexVector N) (hK : 0 ≤ K)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    ∀ᵐ ω ∂μ, ‖X ω - Q.decoded (X ω)‖ ≤ ε := by
  have hball : ∀ᵐ ω ∂μ, ∀ j, ‖X ω j‖ ≤ K := ae_all_iff.mpr hbound
  filter_upwards [hball] with ω hω
  exact Q.decoded_error_le (X ω) ((pi_norm_le_iff_of_nonneg hK).mpr hω)

theorem identDistrib_quantized {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → ComplexVector N) (Y : Ω' → ComplexVector N)
    (hcopy : IdentDistrib Y X ν μ) :
    IdentDistrib (fun ω => Q.quantize (Y ω)) (fun ω => Q.quantize (X ω)) ν μ :=
  hcopy.comp Q.measurable_quantize

theorem identDistrib_decoded {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → ComplexVector N) (Y : Ω' → ComplexVector N)
    (hcopy : IdentDistrib Y X ν μ) :
    IdentDistrib (fun ω => Q.decoded (Y ω)) (fun ω => Q.decoded (X ω)) ν μ :=
  hcopy.comp Q.measurable_decoded

theorem ae_copied_decoded_error_le {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω')
    (X : Ω → ComplexVector N) (Y : Ω' → ComplexVector N)
    (hcopy : IdentDistrib Y X ν μ) (hK : 0 ≤ K)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    ∀ᵐ ω ∂ν, ‖Y ω - Q.decoded (Y ω)‖ ≤ ε := by
  have hY := identDistrib_ae_all_coordinates_bound μ ν X Y hcopy hbound
  exact Q.ae_decoded_error_le ν Y hK (ae_all_iff.mp hY)

/-- A finite tuple of copied rows is approximated simultaneously outside
a single null set. -/
theorem ae_sampled_decoded_error_le {Ω : Type u} {Ω' : Type v}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω')
    {m : ℕ} (X : Ω → ComplexVector N) (rows : Fin m → Ω' → ComplexVector N)
    (hcopy : ∀ i, IdentDistrib (rows i) X ν μ) (hK : 0 ≤ K)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, ‖X ω j‖ ≤ K) :
    ∀ᵐ ω ∂ν, ∀ i, ‖rows i ω - Q.decoded (rows i ω)‖ ≤ ε := by
  apply ae_all_iff.mpr
  intro i
  exact Q.ae_copied_decoded_error_le μ ν X (rows i) (hcopy i) hK hbound

/-- Quantization preserves every coordinate bound everywhere, including
on samples outside the original almost sure row ball. -/
theorem sampled_decoded_coordinate_norm_le {Ω : Type u} {m : ℕ}
    (rows : Fin m → Ω → ComplexVector N) (ω : Ω) (i : Fin m) (j : Fin N) :
    ‖Q.decoded (rows i ω) j‖ ≤ K := Q.decoded_coordinate_norm_le _ _

theorem independent_quantized {Ω : Type u} [MeasurableSpace Ω]
    (ν : Measure Ω) {m : ℕ} (rows : Fin m → Ω → ComplexVector N)
    (hindep : iIndepFun rows ν) :
    iIndepFun (fun i ω => Q.quantize (rows i ω)) ν :=
  hindep.comp (fun _ => Q.quantize) (fun _ => Q.measurable_quantize)

theorem independent_decoded {Ω : Type u} [MeasurableSpace Ω]
    (ν : Measure Ω) {m : ℕ} (rows : Fin m → Ω → ComplexVector N)
    (hindep : iIndepFun rows ν) :
    iIndepFun (fun i ω => Q.decoded (rows i ω)) ν :=
  hindep.comp (fun _ => Q.decoded) (fun _ => Q.measurable_decoded)

end BoundedRowQuantizer

end LeanNumDetect.BoundedRieszConcentration
