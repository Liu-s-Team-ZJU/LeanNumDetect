import MultiTuran.TuranCauchyHalfPlane
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Whole-line weak distribution estimates for actual finite Cauchy sums. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology ENNReal ComplexConjugate
open Set Filter MeasureTheory Complex Metric InnerProductSpace Real

namespace LeanNumDetect.MultiTuran
noncomputable section

private theorem log_norm_cauchy_majorant_ge {v : ℂ} (hv : v.im ≤ 0)
    {y : ℝ} (hy : 0 < y) (hlarge : y < ‖v‖) :
    Real.log 2/2 ≤ Real.log ‖1+Complex.I*v/(y : ℂ)‖ := by
  have hidentity : ‖1+Complex.I*v/(y : ℂ)‖^2 =
      1-2*v.im/y+‖v‖^2/y^2 := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
      Complex.one_re,Complex.one_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
      Complex.I_mul_re,Complex.I_mul_im]
    field_simp
    ring
  have hvsq : y^2 < ‖v‖^2 := (sq_lt_sq₀ hy.le (norm_nonneg _)).mpr hlarge
  have hquot : 1 < ‖v‖^2/y^2 := (lt_div_iff₀ (sq_pos_of_pos hy)).mpr (by simpa using hvsq)
  have him : 2*v.im/y ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith) hy.le
  have hnorm : 2 ≤ ‖1+Complex.I*v/(y : ℂ)‖^2 := by nlinarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnorm
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

/-- A half-plane pole family obeys an actual whole-line weak estimate with
an explicit absolute constant, including repeated and real poles. -/
theorem cauchySum_lowerHalfPlane_weak_bound {N : ℕ} (poles : Fin N → ℂ)
    (hpoles : ∀ j, (poles j).im ≤ 0) {y : ℝ} (hy : 0 < y) :
    volume {x : ℝ | y < ‖cauchySum poles (x : ℂ)‖} ≤
      ENNReal.ofReal ((4*Real.pi/Real.log 2)*(N : ℝ)/y) := by
  let c : ℝ := Real.log 2/2
  have hc : 0 < c := by dsimp [c]; exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (cauchyLogMajorant poles y (x : ℂ))) := by
    unfold cauchyLogMajorant cauchySum
    fun_prop
  have hsub : {x : ℝ | y < ‖cauchySum poles (x : ℂ)‖} ⊆
      {x : ℝ | ENNReal.ofReal c ≤ ENNReal.ofReal (cauchyLogMajorant poles y (x : ℂ))} := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    exact log_norm_cauchy_majorant_ge (cauchySum_im_nonpos poles hpoles (by simp)) hy hx
  calc
    _ ≤ volume {x : ℝ | ENNReal.ofReal c ≤ ENNReal.ofReal (cauchyLogMajorant poles y (x : ℂ))} :=
      measure_mono hsub
    _ ≤ (∫⁻ x : ℝ, ENNReal.ofReal (cauchyLogMajorant poles y (x : ℂ)))/ENNReal.ofReal c :=
      meas_ge_le_lintegral_div hf.aemeasurable (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2*Real.pi*(N : ℝ)/y)/ENNReal.ofReal c :=
      ENNReal.div_le_div_right (lintegral_cauchyLogMajorant_le poles hpoles hy) _
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos hc]
      congr 1
      dsimp [c]
      ring

/-- Reindexing allows the half-plane estimate on any finite family. -/
theorem finiteCauchySum_lowerHalfPlane_weak_bound {ι : Type*} [Fintype ι]
    (poles : ι → ℂ) (hpoles : ∀ j, (poles j).im ≤ 0) {y : ℝ} (hy : 0 < y) :
    volume {x : ℝ | y < ‖∑ j, ((x : ℂ)-poles j)⁻¹‖} ≤
      ENNReal.ofReal ((4*Real.pi/Real.log 2)*(Fintype.card ι : ℝ)/y) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hsum (w : ℂ) : cauchySum (fun j => poles (e j)) w = ∑ j, (w-poles j)⁻¹ := by
    exact e.sum_comp (fun j => (w-poles j)⁻¹)
  have h := cauchySum_lowerHalfPlane_weak_bound (fun j => poles (e j)) (fun j => hpoles (e j)) hy
  simpa only [hsum] using h

/-- Arbitrary complex poles obey a genuine whole-line weak Cauchy bound.
The two half-plane families are separated and the upper one is conjugated. -/
theorem finiteCauchySum_weak_bound {ι : Type*} [Fintype ι]
    (poles : ι → ℂ) {y : ℝ} (hy : 0 < y) :
    volume {x : ℝ | y < ‖∑ j, ((x : ℂ)-poles j)⁻¹‖} ≤
      ENNReal.ofReal ((8*Real.pi/Real.log 2)*(Fintype.card ι : ℝ)/y) := by
  classical
  let p : ι → Prop := fun j => (poles j).im ≤ 0
  let L := {j : ι // p j}
  let U := {j : ι // ¬p j}
  let FL : ℝ → ℂ := fun x => ∑ j : L, ((x : ℂ)-poles j.val)⁻¹
  let FU : ℝ → ℂ := fun x => ∑ j : U, ((x : ℂ)-conj (poles j.val))⁻¹
  have hconj (x : ℝ) : conj (FU x) = ∑ j : U, ((x : ℂ)-poles j.val)⁻¹ := by
    dsimp [FU]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp
  have hsplit (x : ℝ) : (∑ j, ((x : ℂ)-poles j)⁻¹) = FL x+conj (FU x) := by
    rw [hconj]
    exact (Fintype.sum_subtype_add_sum_subtype p (fun j => ((x : ℂ)-poles j)⁻¹)).symm
  have hLp : ∀ j : L, (poles j.val).im ≤ 0 := fun j => j.property
  have hUp : ∀ j : U, (conj (poles j.val)).im ≤ 0 := by
    intro j
    simp only [Complex.conj_im]
    exact neg_nonpos.mpr (lt_of_not_ge j.property).le
  have hL := finiteCauchySum_lowerHalfPlane_weak_bound (fun j : L => poles j.val) hLp
    (div_pos hy (by norm_num : (0 : ℝ) < 2))
  have hU := finiteCauchySum_lowerHalfPlane_weak_bound (fun j : U => conj (poles j.val)) hUp
    (div_pos hy (by norm_num : (0 : ℝ) < 2))
  change volume {x : ℝ | y/2 < ‖FL x‖} ≤ _ at hL
  change volume {x : ℝ | y/2 < ‖FU x‖} ≤ _ at hU
  have hsub : {x : ℝ | y < ‖∑ j, ((x : ℂ)-poles j)⁻¹‖} ⊆
      {x : ℝ | y/2 < ‖FL x‖} ∪ {x : ℝ | y/2 < ‖FU x‖} := by
    intro x hx
    by_contra hn
    have hnotL : ¬y/2 < ‖FL x‖ := fun h => hn (Or.inl h)
    have hnotU : ¬y/2 < ‖FU x‖ := fun h => hn (Or.inr h)
    have hl := le_of_not_gt hnotL
    have hu := le_of_not_gt hnotU
    have hnorm := norm_add_le (FL x) (conj (FU x))
    rw [Complex.norm_conj] at hnorm
    change y < ‖∑ j, ((x : ℂ)-poles j)⁻¹‖ at hx
    rw [hsplit x] at hx
    linarith
  have hcard : Fintype.card L+Fintype.card U=Fintype.card ι := by
    dsimp [L,U]
    rw [Fintype.card_subtype_compl]
    have h := Fintype.card_subtype_le p
    omega
  have hcardR : (Fintype.card L : ℝ)+(Fintype.card U : ℝ)=(Fintype.card ι : ℝ) := by
    exact_mod_cast hcard
  calc
    _ ≤ volume ({x : ℝ | y/2 < ‖FL x‖} ∪ {x : ℝ | y/2 < ‖FU x‖}) := measure_mono hsub
    _ ≤ volume {x : ℝ | y/2 < ‖FL x‖}+volume {x : ℝ | y/2 < ‖FU x‖} := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((4*Real.pi/Real.log 2)*(Fintype.card L : ℝ)/(y/2))+
        ENNReal.ofReal ((4*Real.pi/Real.log 2)*(Fintype.card U : ℝ)/(y/2)) := add_le_add hL hU
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      calc
        _ = (8*Real.pi/Real.log 2)*((Fintype.card L : ℝ)+(Fintype.card U : ℝ))/y := by ring
        _ = _ := by rw [hcardR]

/-- The `Fin N` form of the absolute weak Cauchy estimate. -/
theorem cauchySum_weak_bound {N : ℕ} (poles : Fin N → ℂ) {y : ℝ} (hy : 0 < y) :
    volume {x : ℝ | y < ‖cauchySum poles (x : ℂ)‖} ≤
      ENNReal.ofReal ((8*Real.pi/Real.log 2)*(N : ℝ)/y) := by
  simpa only [cauchySum,Fintype.card_fin] using finiteCauchySum_weak_bound poles hy

/-- One explicit absolute constant for the whole-line weak Cauchy bound. -/
def cauchyWeakConstant : ℝ := 8*Real.pi/Real.log 2

theorem cauchyWeakConstant_pos : 0 < cauchyWeakConstant := by
  unfold cauchyWeakConstant
  exact div_pos (by positivity) (Real.log_pos (by norm_num))

/-- The literal real-measure estimate on any measured subset of the line. -/
theorem cauchySum_weak_bound_on_set_toReal {N : ℕ} (poles : Fin N → ℂ)
    (E : Set ℝ) {y : ℝ} (hy : 0 < y) :
    (volume (E ∩ {x : ℝ | y < ‖cauchySum poles (x : ℂ)‖})).toReal ≤
      cauchyWeakConstant*(N : ℝ)/y := by
  have h := (measure_mono (show E ∩ {x : ℝ | y < ‖cauchySum poles (x : ℂ)‖} ⊆
    {x : ℝ | y < ‖cauchySum poles (x : ℂ)‖} from inter_subset_right)).trans
    (cauchySum_weak_bound poles hy)
  have hR := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity)] at hR
  exact hR

end
end LeanNumDetect.MultiTuran
