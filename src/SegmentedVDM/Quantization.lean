import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import General.Finite.FiniteRealGeometry

/-! Integer frequency quantization for the NumDetect manuscript's
`lem:freq_quantization`. The general statement `frequency_quantization_of_lp_separation`
holds in every dimension `d` and for all Hölder conjugate exponents `p`, `p'`,
including the endpoints `(p, p') = (1, ∞)` and `(∞, 1)`. Its `d = 1`, `p = ∞`
case is `scalar_frequency_quantization`, where no signed recentering is
necessary: the nonnegative integer frequency works for either sign of the
difference. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ENNReal NNReal

open LeanNumDetect

namespace SegmentedVDM

theorem sin_quarter_chord {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ Real.pi / 4) :
    (2 * Real.sqrt 2 / Real.pi) * x ≤ Real.sin x := by
  let t := x / (Real.pi / 4)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := (div_le_one (by positivity)).2 hx'
  have h := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by constructor <;> positivity)
    (show Real.pi / 4 ∈ Set.Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos])
    (sub_nonneg.mpr ht1) ht (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero, Real.sin_pi_div_four] at h
  have he : t * (Real.pi / 4) = x := div_mul_cancel₀ _ (by positivity)
  rw [he] at h
  convert! h using 1
  all_goals
    dsimp [t] at *
    try field_simp
    ring

theorem exp_sub_one_norm_abs (x : ℝ) (hx : |x| ≤ Real.pi) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ = 2 * Real.sin (|x| / 2) := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsin : 0 ≤ Real.sin (|x| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg h] at hsin ⊢
    rw [abs_of_nonneg hsin]
  · have hn : x ≤ 0 := le_of_not_ge h
    rw [abs_of_nonpos hn, neg_div, Real.sin_neg] at hsin ⊢
    rw [abs_of_nonpos (by linarith : Real.sin (x / 2) ≤ 0)]

/-- The phase lower bound is evaluated before applying the sine chord; this
retains the factor √2 in the original proof. -/
theorem exp_sub_one_lower {x b : ℝ} (hb : 0 ≤ b) (hbπ : b ≤ Real.pi / 2)
    (hbx : b ≤ |x|) (hx : |x| ≤ Real.pi) :
    2 * Real.sqrt 2 / Real.pi * b ≤ ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ := by
  rw [exp_sub_one_norm_abs x hx]
  have hchord := sin_quarter_chord (by linarith : 0 ≤ b / 2) (by linarith)
  have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ b / 2)
    (by linarith : |x| / 2 ≤ Real.pi / 2) (by linarith : b / 2 ≤ |x| / 2)
  linarith

theorem floor_ge_half {t : ℝ} (ht : 2 ≤ t) : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one t
  have hfloor : (1 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by
    exact_mod_cast (show 1 ≤ ⌊t⌋₊ by exact Nat.le_floor (by norm_num; linarith))
  linarith

/-- The frequency-quantization lemma of the NumDetect manuscript,
`lem:freq_quantization`, at full strength. Here `q` is the Hölder conjugate
`p'` of `p` on `ℝ≥0∞` (so `p⁻¹ + q⁻¹ = 1`, with `1⁻¹ = ⊤` and `⊤⁻¹ = 1`), the
manuscript's norm `‖x‖_r` is `lpNorm r x`, and the dimension factor `d^{1/p}` is
`(d : ℝ) ^ p.toReal⁻¹`, equal to `d^0 = 1` at `p = ⊤`. The vector `u` is a
nonzero difference in the sense that `0 < ‖u‖_{p'}`, at scale `α > 0` with
`‖u‖_{p'} ≤ 2πα ≤ π/(2 D d^{1/p})`; the conclusion quantizes an ideal frequency
to an integer frequency vector `k ∈ ℤ^d` with `‖k‖_p ≤ 1/(2 D α)`,
`‖u‖_{p'}/(4 α) ≤ D |k · u| ≤ π`, and `|1 - e^{i D k · u}| ≥ √2 ‖u‖_{p'}/(2 π α)`.

The manuscript additionally assumes that `u ∈ (-π, π]^d` is the coordinatewise
shortest representative of a nonzero torus difference. That geometric context is
not used by the proof and is recorded in
`frequency_quantization_of_shortest_representative`. -/
theorem frequency_quantization_of_lp_separation {d : ℕ} {p q : ℝ≥0∞}
    (hpq : ENNReal.HolderConjugate p q) {D α : ℝ} (hD : 0 < D) (hα : 0 < α)
    (u : Fin d → ℝ) (hun : 0 < lpNorm q u) (huα : lpNorm q u ≤ 2 * Real.pi * α)
    (hαD : 2 * Real.pi * α ≤ Real.pi / (2 * D * (d : ℝ) ^ p.toReal⁻¹)) :
    ∃ k : Fin d → ℤ,
      lpNorm p (fun j => (k j : ℝ)) ≤ 1 / (2 * D * α) ∧
      lpNorm q u / (4 * α) ≤ D * |∑ j, (k j : ℝ) * u j| ∧
      D * |∑ j, (k j : ℝ) * u j| ≤ Real.pi ∧
      Real.sqrt 2 / (2 * Real.pi * α) * lpNorm q u ≤
        ‖1 - Complex.exp (Complex.I * ((D * ∑ j, (k j : ℝ) * u j : ℝ) : ℂ))‖ := by
  have hp0 := holderConjugate_ne_zero hpq
  obtain ⟨v, hv_le, hvu⟩ := exists_lpNorm_norming hpq hun
  set t := (2 * D * α)⁻¹ with htdef
  have ht : t = 1 / (2 * D * α) := by rw [htdef]; exact (one_div _).symm
  have ht2 : t / 2 = 1 / (4 * D * α) := by rw [htdef]; field_simp; ring
  have hc : 0 < t := by rw [htdef]; exact inv_pos.mpr (by positivity)
  have hdim : (d : ℝ) ^ p.toReal⁻¹ ≤ 1 / (4 * D * α) := by
    have hpos : 0 < 2 * D * (d : ℝ) ^ p.toReal⁻¹ := by
      by_contra h
      have hz : 2 * D * (d : ℝ) ^ p.toReal⁻¹ = 0 :=
        le_antisymm (le_of_not_gt h) (by positivity)
      rw [hz, div_zero] at hαD
      nlinarith [Real.pi_pos]
    have hmul : 2 * Real.pi * α * (2 * D * (d : ℝ) ^ p.toReal⁻¹) ≤ Real.pi :=
      (le_div_iff₀ hpos).mp hαD
    have hdivπ : (2 * Real.pi * α * (2 * D * (d : ℝ) ^ p.toReal⁻¹)) / Real.pi ≤ 1 := by
      have := div_le_div_of_nonneg_right hmul (le_of_lt Real.pi_pos)
      rwa [div_self Real.pi_ne_zero] at this
    rw [le_div_iff₀ (by positivity : 0 < 4 * D * α)]
    have hm : (d : ℝ) ^ p.toReal⁻¹ * (4 * D * α)
        = (2 * Real.pi * α * (2 * D * (d : ℝ) ^ p.toReal⁻¹)) / Real.pi := by
      field_simp
      ring
    rw [hm]
    exact hdivπ
  set k : Fin d → ℤ := fun j => truncate (t * v j) with hkdef
  have hkabs : ∀ j, |(k j : ℝ)| ≤ |t * v j| := by
    intro j
    rw [hkdef]
    exact abs_truncate_le (t * v j)
  have hksub : ∀ j, |(k j : ℝ) - t * v j| < 1 := by
    intro j
    rw [hkdef, abs_sub_comm]
    exact abs_sub_truncate_lt_one (t * v j)
  have hk1 : lpNorm p (fun j => (k j : ℝ)) ≤ t := by
    refine (lpNorm_mono hkabs).trans ?_
    rw [lpNorm_const_mul hp0.1 hc.le v]
    have h2 := mul_le_mul_of_nonneg_left hv_le hc.le
    rwa [mul_one] at h2
  have hdot : ∑ j, (t * v j) * u j = t * lpNorm q u := by
    have h : ∑ j, (t * v j) * u j = ∑ j, t * (v j * u j) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [h, ← Finset.mul_sum, hvu]
  have hsum : (∑ j, (k j : ℝ) * u j)
      = ∑ j, (t * v j) * u j + ∑ j, ((k j : ℝ) - t * v j) * u j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have herr : |∑ j, ((k j : ℝ) - t * v j) * u j| ≤ t * lpNorm q u / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∑ j, |((k j : ℝ) - t * v j) * u j| ≤ ∑ j, |u j| := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul]
      have := mul_le_mul_of_nonneg_right (hksub j).le (abs_nonneg (u j))
      rwa [one_mul] at this
    refine h1.trans ?_
    have h2 := sum_abs_le_card_pow_mul_lpNorm hpq u
    rw [Fintype.card_fin] at h2
    have h3 : (d : ℝ) ^ p.toReal⁻¹ * lpNorm q u ≤ (1 / (4 * D * α)) * lpNorm q u :=
      mul_le_mul_of_nonneg_right hdim (lpNorm_nonneg q u)
    refine h2.trans (h3.trans ?_)
    rw [← ht2]
    exact le_of_eq (div_mul_eq_mul_div t 2 (lpNorm q u))
  have htri : |t * lpNorm q u| - |∑ j, ((k j : ℝ) - t * v j) * u j|
      ≤ |∑ j, (k j : ℝ) * u j| := by
    have h := abs_sub_abs_le_abs_sub (∑ j, (t * v j) * u j)
      (-∑ j, ((k j : ℝ) - t * v j) * u j)
    rw [abs_neg, sub_neg_eq_add, ← hsum] at h
    rw [← hdot]
    exact h
  have hlo : lpNorm q u / (4 * α) ≤ D * |∑ j, (k j : ℝ) * u j| := by
    have hA : |t * lpNorm q u| = t * lpNorm q u :=
      abs_of_nonneg (mul_nonneg hc.le (lpNorm_nonneg q u))
    have hmid : t * lpNorm q u / 2 ≤ |∑ j, (k j : ℝ) * u j| := by
      have h1 := htri
      rw [hA] at h1
      linarith [herr]
    have hD' : D * (t * lpNorm q u / 2) = lpNorm q u / (4 * α) := by
      rw [htdef]
      field_simp
      ring
    rw [← hD']
    exact mul_le_mul_of_nonneg_left hmid hD.le
  have hhi : D * |∑ j, (k j : ℝ) * u j| ≤ Real.pi := by
    have h1 : |∑ j, (k j : ℝ) * u j| ≤ t * lpNorm q u :=
      (abs_dot_le_lpNorm_mul_lpNorm hpq (fun j => (k j : ℝ)) u).trans
        (mul_le_mul_of_nonneg_right hk1 (lpNorm_nonneg q u))
    have h2 : t * lpNorm q u ≤ t * (2 * Real.pi * α) :=
      mul_le_mul_of_nonneg_left huα hc.le
    have h3 : t * (2 * Real.pi * α) = Real.pi / D := by
      rw [htdef]
      field_simp
    have h4 : |∑ j, (k j : ℝ) * u j| ≤ Real.pi / D := h1.trans (h2.trans (le_of_eq h3))
    have h5 : |∑ j, (k j : ℝ) * u j| * D ≤ Real.pi := (le_div_iff₀ hD).mp h4
    rwa [mul_comm] at h5
  refine ⟨k, ?_, hlo, hhi, ?_⟩
  · rw [← ht]
    exact hk1
  · rw [norm_sub_rev]
    have hx : |D * ∑ j, (k j : ℝ) * u j| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos hD]
      exact hhi
    have hre : Real.sqrt 2 / (2 * Real.pi * α) * lpNorm q u
        = 2 * Real.sqrt 2 / Real.pi * (lpNorm q u / (4 * α)) := by
      field_simp
      ring
    rw [hre]
    have hbπ : lpNorm q u / (4 * α) ≤ Real.pi / 2 := by
      have := div_le_div_of_nonneg_right huα (by positivity : 0 ≤ 4 * α)
      rw [show (2 * Real.pi * α) / (4 * α) = Real.pi / 2 by field_simp; ring] at this
      exact this
    have hbX : lpNorm q u / (4 * α) ≤ |D * ∑ j, (k j : ℝ) * u j| := by
      rw [abs_mul, abs_of_pos hD]
      exact hlo
    exact exp_sub_one_lower (by positivity) hbπ hbX hx

/-- The manuscript form of NumDetect `lem:freq_quantization`, stated for `u` the
coordinatewise shortest representative of a nonzero torus difference:
`u ∈ (-π, π]^d`. The range hypothesis is part of the manuscript's statement but
is not used by its proof; see `frequency_quantization_of_lp_separation` for the
analytic core, which applies without it. -/
theorem frequency_quantization_of_shortest_representative {d : ℕ} {p q : ℝ≥0∞}
    (hpq : ENNReal.HolderConjugate p q) {D α : ℝ} (hD : 0 < D) (hα : 0 < α)
    (u : Fin d → ℝ) (_hu : ∀ j, u j ∈ Set.Ioc (-Real.pi) Real.pi)
    (hun : 0 < lpNorm q u) (huα : lpNorm q u ≤ 2 * Real.pi * α)
    (hαD : 2 * Real.pi * α ≤ Real.pi / (2 * D * (d : ℝ) ^ p.toReal⁻¹)) :
    ∃ k : Fin d → ℤ,
      lpNorm p (fun j => (k j : ℝ)) ≤ 1 / (2 * D * α) ∧
      lpNorm q u / (4 * α) ≤ D * |∑ j, (k j : ℝ) * u j| ∧
      D * |∑ j, (k j : ℝ) * u j| ≤ Real.pi ∧
      Real.sqrt 2 / (2 * Real.pi * α) * lpNorm q u ≤
        ‖1 - Complex.exp (Complex.I * ((D * ∑ j, (k j : ℝ) * u j : ℝ) : ℂ))‖ :=
  frequency_quantization_of_lp_separation hpq hD hα u hun huα hαD

/-- Scalar version of the three frequency-quantization inequalities. This is the
`d = 1`, `p = ∞`, `p' = 1` case of `frequency_quantization_of_lp_separation`,
with the sign of the integer frequency absorbed into `|u|`. -/
theorem scalar_frequency_quantization {D α u : ℝ}
    (hD : 0 < D) (hα : 0 < α) (hu : 0 < |u|)
    (huα : |u| ≤ 2 * Real.pi * α) (hαD : α ≤ 1 / (4 * D)) :
    ∃ k : ℕ, (k : ℝ) ≤ 1 / (2 * D * α) ∧
      |u| / (4 * α) ≤ D * |(k : ℝ) * u| ∧
      D * |(k : ℝ) * u| ≤ Real.pi ∧
      Real.sqrt 2 / (2 * Real.pi * α) * |u| ≤
        ‖1 - Complex.exp (Complex.I * ((D * k * u : ℝ) : ℂ))‖ := by
  set w : Fin 1 → ℝ := fun _ => u with hwdef
  have hpq : ENNReal.HolderConjugate ⊤ 1 := inferInstance
  have hwp : lpNorm 1 w = |u| := by
    rw [hwdef, lpNorm_one, Fin.sum_univ_one]
  have hwp' : lpNorm ⊤ w = |u| := by
    rw [hwdef, lpNorm_top]
    exact ciSup_const
  have hcard : ((1:ℕ):ℝ) ^ ((⊤ : ℝ≥0∞).toReal)⁻¹ = (1:ℝ) := by simp
  have hse : 2 * Real.pi * α ≤ Real.pi / (2 * D * ((1:ℕ):ℝ) ^ ((⊤ : ℝ≥0∞).toReal)⁻¹) := by
    rw [hcard, mul_one]
    have h1 : α * (4 * D) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 4 * D)).mp hαD
    have h2 : 4 * D * α ≤ 1 := by linarith
    have h3 : 2 * Real.pi * α * (2 * D) = (4 * D * α) * Real.pi := by ring
    rw [le_div_iff₀ (by positivity : 0 < 2 * D), h3]
    have h4 := mul_le_mul_of_nonneg_right h2 (le_of_lt Real.pi_pos)
    rwa [one_mul] at h4
  obtain ⟨kv, hk, hlo, hhi, hden⟩ := frequency_quantization_of_lp_separation
    (d := 1) (p := ⊤) (q := 1) hpq hD hα w (by rwa [hwp]) (by rwa [hwp]) hse
  have hcast : (((kv 0).natAbs : ℕ) : ℝ) = |(kv 0 : ℝ)| :=
    (Nat.cast_natAbs (kv 0)).trans Int.cast_abs
  have hsum1 : ∑ j : Fin 1, (kv j : ℝ) * w j = (kv 0 : ℝ) * u := by
    simp [hwdef]
  refine ⟨(kv 0).natAbs, ?_, ?_, ?_, ?_⟩
  · have h0 : |(kv 0 : ℝ)| ≤ lpNorm ⊤ (fun j => (kv j : ℝ)) :=
      lpNorm_top_le (fun j => (kv j : ℝ)) (0 : Fin 1)
    have := h0.trans hk
    rw [hcast]
    exact this
  · rw [hwp, hsum1] at hlo
    rw [hcast, abs_mul, abs_abs, ← abs_mul]
    exact hlo
  · rw [hsum1] at hhi
    rw [hcast, abs_mul, abs_abs, ← abs_mul]
    exact hhi
  · rw [hwp, hsum1] at hden
    have hπ : |D * ((kv 0 : ℝ) * u)| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos hD]
      rwa [hsum1] at hhi
    have heq : |D * (((kv 0).natAbs : ℕ) : ℝ) * u| = |D * ((kv 0 : ℝ) * u)| := by
      rw [hcast]
      simp only [abs_mul, abs_abs, abs_of_pos hD]
      ring
    have hπ' : |D * (((kv 0).natAbs : ℕ) : ℝ) * u| ≤ Real.pi := by
      rw [heq]
      exact hπ
    rw [norm_sub_rev, exp_sub_one_norm_abs _ hπ']
    rw [heq]
    rw [norm_sub_rev, exp_sub_one_norm_abs _ hπ] at hden
    exact hden

/-- Budget-scale form of `frequency_quantization_of_lp_separation`, giving the
per-node quantized data of the NumDetect manuscript's `lem:neighborset_segmented`
from `lem:freq_quantization`. Writing `t = 1/(2 D α)` for the budget scale of
`lem:freq_quantization`, the scale constraints `‖u‖_{p'} ≤ 2πα ≤ π/(2 D d^{1/p})`
read `‖u‖_{p'} ≤ π/(D t)` and `2 d^{1/p} ≤ t`, the quantized frequency obeys
`‖k‖_p ≤ t`, and the two-point denominator satisfies
`√2 D t ‖u‖_{p'} / π ≤ |1 - e^{i D k·u}|`. -/
theorem frequency_quantization_of_budgetScale {d : ℕ} {p q : ℝ≥0∞}
    (hpq : ENNReal.HolderConjugate p q) {D t : ℝ} (hD : 0 < D)
    (hdim : 0 < (d : ℝ) ^ p.toReal⁻¹) (ht : 2 * (d : ℝ) ^ p.toReal⁻¹ ≤ t)
    (u : Fin d → ℝ) (hun : 0 < lpNorm q u) (hut : lpNorm q u ≤ Real.pi / (D * t)) :
    ∃ k : Fin d → ℤ,
      lpNorm p (fun j => (k j : ℝ)) ≤ t ∧
      Real.sqrt 2 * D * t * lpNorm q u / Real.pi ≤
        ‖1 - Complex.exp (Complex.I * ((D * ∑ j, (k j : ℝ) * u j : ℝ) : ℂ))‖ := by
  have htpos : 0 < t := by
    have h1 : 0 < Real.pi / (D * t) := lt_of_lt_of_le hun hut
    have h2 : 0 < D * t := (div_pos_iff_of_pos_left Real.pi_pos).mp h1
    exact pos_of_mul_pos_right h2 (le_of_lt hD)
  have hαpos : (0 : ℝ) < 1 / (2 * D * t) := by positivity
  have hscale : 2 * Real.pi * (1 / (2 * D * t)) = Real.pi / (D * t) := by
    field_simp
  have hαD : 2 * Real.pi * (1 / (2 * D * t)) ≤
      Real.pi / (2 * D * (d : ℝ) ^ p.toReal⁻¹) := by
    rw [hscale]
    have h2pos : 0 < 2 * D * (d : ℝ) ^ p.toReal⁻¹ :=
      mul_pos (mul_pos (by norm_num) hD) hdim
    rw [div_le_div_iff₀ (mul_pos hD htpos) h2pos]
    have hmul := mul_le_mul_of_nonneg_left ht (le_of_lt Real.pi_pos)
    have hD' := mul_le_mul_of_nonneg_right hmul (le_of_lt hD)
    have he1 : Real.pi * (2 * D * (d : ℝ) ^ p.toReal⁻¹)
        = (Real.pi * (2 * (d : ℝ) ^ p.toReal⁻¹)) * D := by ring
    have he2 : Real.pi * (D * t) = (Real.pi * t) * D := by ring
    rw [he1, he2]
    exact hD'
  obtain ⟨k, hk, _, _, hden⟩ := frequency_quantization_of_lp_separation hpq hD hαpos
    u hun (by rw [hscale]; exact hut) hαD
  have hk' : lpNorm p (fun j => (k j : ℝ)) ≤ t := by
    have heq : t = 1 / (2 * D * (1 / (2 * D * t))) := by
      have h2 : D * t ≠ 0 := (mul_pos hD htpos).ne'
      field_simp
    rw [heq]
    exact hk
  refine ⟨k, hk', ?_⟩
  have heq : Real.sqrt 2 * D * t * lpNorm q u / Real.pi
      = Real.sqrt 2 / (2 * Real.pi * (1 / (2 * D * t))) * lpNorm q u := by
    have h2 : D * t ≠ 0 := (mul_pos hD htpos).ne'
    field_simp
  rw [heq]
  exact hden

end SegmentedVDM
