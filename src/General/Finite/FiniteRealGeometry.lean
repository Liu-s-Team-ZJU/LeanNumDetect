import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENNReal.Holder
import Mathlib.Data.Real.Pointwise
import Mathlib.Tactic
set_option autoImplicit false

open scoped ENNReal NNReal

namespace LeanNumDetect

theorem finite_nodes_enclosing_diameter {q : ℕ} (hq : 0 < q) (x : Fin q → ℝ) :
    ∃ c : ℝ, ∀ j, x j ∈ Set.Icc c (c+Metric.diam (Set.range x)) := by
  classical
  letI : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  refine ⟨x i, fun j => ⟨hi j (Finset.mem_univ _), ?_⟩⟩
  have hh := Metric.dist_le_diam_of_mem (Set.finite_range x).isBounded
    (Set.mem_range_self j) (Set.mem_range_self i)
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hi j (Finset.mem_univ _)))] at hh
  linarith

theorem finite_nodes_diameter_zero {q : ℕ} (hq : 0 < q) (hq' : q ≤ 1) (x : Fin q → ℝ) :
    Metric.diam (Set.range x) = 0 := by
  have he : q = 1 := by omega
  subst q
  have hx : x = fun _ => x 0 := funext (fun j => congrArg x (Subsingleton.elim j 0))
  rw [hx, Set.range_const, Metric.diam_singleton]

theorem exists_periodic_gap_le_pi (x : ℝ) :
    ∃ p : ℤ, |x-2*Real.pi*p| ≤ Real.pi := by
  refine ⟨round (x/(2*Real.pi)), ?_⟩
  have hh := abs_sub_round (x/(2*Real.pi))
  have he : x-2*Real.pi*(round (x/(2*Real.pi)) : ℝ) =
      (2*Real.pi)*(x/(2*Real.pi)-(round (x/(2*Real.pi)) : ℝ)) := by field_simp
  rw [he, abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi)]
  nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*Real.pi by positivity)]

theorem periodic_separation_lt_half {x β : ℝ}
    (hsep : ∀ p : ℤ, 2*Real.pi*β < |x-2*Real.pi*p|) : β < 1/2 := by
  obtain ⟨p,hp⟩ := exists_periodic_gap_le_pi x
  have hh := (hsep p).trans_le hp
  nlinarith [Real.pi_pos]

/-! ### Finite-dimensional `ℓ^q` norms

`lpNorm q x` is the ordinary vector `ℓ^q`-norm of `x : ι → ℝ` on a finite index
type, for an extended nonnegative exponent `q` with the endpoint convention that
`q = ⊤` is the sup norm. These are the norms `‖·‖_q` of the NumDetect manuscript
`lem:freq_quantization`, whose conjugate exponents `p`, `p'` include the pairs
`(1, ∞)` and `(∞, 1)`. This interface supersedes `LeanNumDetect.NumDetect.lpNorm`,
which is only defined for real exponents. -/

/-- The `ℓ^q`-norm of a real vector on a finite index type, for an extended
nonnegative exponent `q`; `q = ⊤` is the sup norm and `q < ⊤` gives
`(∑ k, |x k| ^ q.toReal) ^ q.toReal⁻¹`, including `ℓ^1`. -/
noncomputable def lpNorm {ι : Type*} [Fintype ι] (q : ℝ≥0∞) (x : ι → ℝ) : ℝ :=
  if q = ⊤ then ⨆ k, |x k| else (∑ k, |x k| ^ q.toReal) ^ (q.toReal)⁻¹

/-- Truncation of a real number toward zero: the unique integer `n` with
`|a - n| < 1` and `|n| ≤ |a|`, written `[a]` in the proof of the manuscript's
`lem:freq_quantization`. -/
noncomputable def truncate (a : ℝ) : ℤ := if 0 ≤ a then ⌊a⌋ else ⌈a⌉

variable {ι : Type*} [Fintype ι]

theorem lpNorm_of_eq_top {q : ℝ≥0∞} (hq : q = ⊤) (x : ι → ℝ) :
    lpNorm q x = ⨆ k, |x k| := by
  rw [lpNorm, if_pos hq]

theorem lpNorm_of_ne_top {q : ℝ≥0∞} (hq : q ≠ ⊤) (x : ι → ℝ) :
    lpNorm q x = (∑ k, |x k| ^ q.toReal) ^ (q.toReal)⁻¹ := by
  rw [lpNorm, if_neg hq]

@[simp] theorem lpNorm_top (x : ι → ℝ) : lpNorm ⊤ x = ⨆ k, |x k| :=
  lpNorm_of_eq_top rfl x

@[simp] theorem lpNorm_one (x : ι → ℝ) : lpNorm 1 x = ∑ k, |x k| := by
  rw [lpNorm_of_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)]
  simp [Real.rpow_one]

theorem lpNorm_nonneg (q : ℝ≥0∞) (x : ι → ℝ) : 0 ≤ lpNorm q x := by
  obtain hq | hq := eq_or_ne q ⊤
  · rw [lpNorm_of_eq_top hq]
    exact Real.iSup_nonneg fun k => abs_nonneg _
  · rw [lpNorm_of_ne_top hq]
    exact Real.rpow_nonneg (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (abs_nonneg _) _) _

theorem lpNorm_top_le (x : ι → ℝ) (k : ι) : |x k| ≤ lpNorm ⊤ x := by
  rw [lpNorm_top]
  exact le_ciSup (Set.finite_range fun k => |x k|).bddAbove k

theorem lpNorm_abs (q : ℝ≥0∞) (x : ι → ℝ) :
    lpNorm q (fun k => |x k|) = lpNorm q x := by
  obtain hq | hq := eq_or_ne q ⊤
  · rw [lpNorm_of_eq_top hq, lpNorm_of_eq_top hq]
    simp only [abs_abs]
  · rw [lpNorm_of_ne_top hq, lpNorm_of_ne_top hq]
    simp only [abs_abs]

theorem lpNorm_mono {q : ℝ≥0∞} {x y : ι → ℝ} (h : ∀ k, |y k| ≤ |x k|) :
    lpNorm q y ≤ lpNorm q x := by
  obtain hq | hq := eq_or_ne q ⊤
  · rw [lpNorm_of_eq_top hq, lpNorm_of_eq_top hq]
    exact ciSup_mono (Set.finite_range fun k => |x k|).bddAbove fun k => h k
  · rw [lpNorm_of_ne_top hq, lpNorm_of_ne_top hq]
    have hsum : ∑ k, |y k| ^ q.toReal ≤ ∑ k, |x k| ^ q.toReal :=
      Finset.sum_le_sum fun k _ =>
        Real.rpow_le_rpow (abs_nonneg _) (h k) ENNReal.toReal_nonneg
    exact Real.rpow_le_rpow
      (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (abs_nonneg _) _) hsum
      (inv_nonneg.mpr ENNReal.toReal_nonneg)

theorem lpNorm_const_mul {q : ℝ≥0∞} (hq : q ≠ 0) {c : ℝ} (hc : 0 ≤ c) (x : ι → ℝ) :
    lpNorm q (fun k => c * x k) = c * lpNorm q x := by
  obtain hq' | hq' := eq_or_ne q ⊤
  · rw [lpNorm_of_eq_top hq', lpNorm_of_eq_top hq']
    have h1 : (⨆ k, |c * x k|) = ⨆ k, c * |x k| := by
      congr 1 with k
      rw [abs_mul, abs_of_nonneg hc]
    rw [h1, Real.mul_iSup_of_nonneg hc]
  · rw [lpNorm_of_ne_top hq', lpNorm_of_ne_top hq']
    have hr : q.toReal ≠ 0 := by
      intro hzero
      rw [ENNReal.toReal_eq_zero_iff] at hzero
      exact hq (hzero.resolve_right hq')
    have habs : ∀ k, |c * x k| = c * |x k| := by
      intro k
      rw [abs_mul, abs_of_nonneg hc]
    have hmul : ∀ k, (c * |x k|) ^ q.toReal = c ^ q.toReal * |x k| ^ q.toReal :=
      fun k => Real.mul_rpow hc (abs_nonneg _)
    calc (∑ k, |c * x k| ^ q.toReal) ^ q.toReal⁻¹
        = (∑ k, (c * |x k|) ^ q.toReal) ^ q.toReal⁻¹ := by simp only [habs]
      _ = (∑ k, c ^ q.toReal * |x k| ^ q.toReal) ^ q.toReal⁻¹ := by simp only [hmul]
      _ = (c ^ q.toReal * ∑ k, |x k| ^ q.toReal) ^ q.toReal⁻¹ := by rw [← Finset.mul_sum]
      _ = (c ^ q.toReal) ^ q.toReal⁻¹ * (∑ k, |x k| ^ q.toReal) ^ q.toReal⁻¹ := by
          rw [Real.mul_rpow (Real.rpow_nonneg hc _)
            (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (abs_nonneg _) _)]
      _ = c * (∑ k, |x k| ^ q.toReal) ^ q.toReal⁻¹ := by rw [Real.rpow_rpow_inv hc hr]

theorem abs_sub_truncate_lt_one (a : ℝ) : |a - (truncate a : ℝ)| < 1 := by
  by_cases h : 0 ≤ a
  · rw [truncate, if_pos h]
    have hle : (0 : ℝ) ≤ a - (⌊a⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le a)
    rw [abs_of_nonneg hle]
    have hlt : a < (⌊a⌋ : ℝ) + 1 := Int.lt_floor_add_one a
    linarith
  · rw [truncate, if_neg h]
    have hle : a - (⌈a⌉ : ℝ) ≤ 0 := sub_nonpos.mpr (Int.le_ceil a)
    rw [abs_of_nonpos hle]
    have hlt : (⌈a⌉ : ℝ) < a + 1 := Int.ceil_lt_add_one a
    linarith

theorem abs_truncate_le (a : ℝ) : |(truncate a : ℝ)| ≤ |a| := by
  by_cases h : 0 ≤ a
  · rw [truncate, if_pos h]
    have hnn : (0 : ℝ) ≤ (⌊a⌋ : ℝ) := by
      exact_mod_cast Int.floor_nonneg.mpr h
    rw [abs_of_nonneg hnn, abs_of_nonneg h]
    exact Int.floor_le a
  · rw [truncate, if_neg h]
    have hnon : (⌈a⌉ : ℤ) ≤ 0 := by
      apply Int.ceil_le.mpr
      exact_mod_cast le_of_lt (lt_of_not_ge h)
    have hnon' : (⌈a⌉ : ℝ) ≤ 0 := by exact_mod_cast hnon
    rw [abs_of_nonpos hnon', abs_of_nonpos (le_of_not_ge h)]
    have := Int.le_ceil a
    linarith

theorem lpNorm_truncate_le {q : ℝ≥0∞} (x : ι → ℝ) :
    lpNorm q (fun k => (truncate (x k) : ℝ)) ≤ lpNorm q x :=
  lpNorm_mono fun k => abs_truncate_le (x k)

/-- Conjugate exponents on `ℝ≥0∞` are at least one. -/
theorem holderConjugate_one_le {p q : ℝ≥0∞} (hpq : ENNReal.HolderConjugate p q) :
    1 ≤ p ∧ 1 ≤ q := by
  have hinv : p⁻¹ + q⁻¹ = 1 := @ENNReal.HolderConjugate.inv_add_inv_eq_one p q hpq
  have hp : p⁻¹ ≤ 1 := by rw [← hinv]; exact le_self_add
  have hq : q⁻¹ ≤ 1 := by
    rw [← hinv]
    exact (le_self_add (a := q⁻¹)).trans_eq (add_comm _ _)
  exact ⟨ENNReal.inv_le_one.mp hp, ENNReal.inv_le_one.mp hq⟩

theorem holderConjugate_ne_zero {p q : ℝ≥0∞} (hpq : ENNReal.HolderConjugate p q) :
    p ≠ 0 ∧ q ≠ 0 := by
  obtain ⟨hp, hq⟩ := holderConjugate_one_le hpq
  exact ⟨(zero_lt_one.trans_le hp).ne', (zero_lt_one.trans_le hq).ne'⟩

/-- Conjugate exponents on `ℝ≥0∞`, with the endpoint conventions `1⁻¹ = ⊤` and
`⊤⁻¹ = 1`, are either the endpoint pair or genuine real conjugate exponents. -/
theorem holderConjugate_cases {p q : ℝ≥0∞} (hpq : ENNReal.HolderConjugate p q) :
    (p = ⊤ ∧ q = 1) ∨ (p = 1 ∧ q = ⊤) ∨ Real.HolderConjugate p.toReal q.toReal := by
  have hinv : p⁻¹ + q⁻¹ = 1 := @ENNReal.HolderConjugate.inv_add_inv_eq_one p q hpq
  have h1 := holderConjugate_one_le hpq
  have hple : p⁻¹ ≤ 1 := by rw [← hinv]; exact le_self_add
  have hqle : q⁻¹ ≤ 1 := by
    rw [← hinv]
    exact (le_self_add (a := q⁻¹)).trans_eq (add_comm _ _)
  by_cases hp : p = ⊤
  · left
    refine ⟨hp, ENNReal.inv_eq_one.mp ?_⟩
    rw [hp, ENNReal.inv_top, zero_add] at hinv
    exact hinv
  · by_cases hp1 : p = 1
    · right
      left
      refine ⟨hp1, ENNReal.inv_eq_zero.mp ?_⟩
      have h11 : ((1 : ℝ≥0∞))⁻¹ = 1 := ENNReal.inv_eq_one.mpr rfl
      rw [hp1, h11] at hinv
      have hle : q⁻¹ ≤ (0 : ℝ≥0∞) :=
        ENNReal.le_of_add_le_add_left ENNReal.one_ne_top
          (by rw [add_zero]; exact le_of_eq hinv)
      exact le_zero_iff.mp hle
    · right
      right
      have hpne : p⁻¹ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hple
      have hqne : q⁻¹ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hqle
      have hsum : p.toReal⁻¹ + q.toReal⁻¹ = 1 := by
        rw [← ENNReal.toReal_inv, ← ENNReal.toReal_inv, ← ENNReal.toReal_add hpne hqne, hinv,
          ENNReal.toReal_one]
      have hlt : (1:ℝ≥0∞) < p := lt_of_le_of_ne h1.1 (Ne.symm hp1)
      have hlt' : (1:ℝ) < p.toReal :=
        by simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hlt
      exact Real.holderConjugate_iff.mpr ⟨hlt', hsum⟩

/-- The `ℓ^p`-norm of the constant vector `1` is the dimension factor `d^{1/p}`,
with `d^{1/⊤} = d^0 = 1`. -/
theorem lpNorm_const_one {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    lpNorm p (fun _ : ι => (1:ℝ)) = (Fintype.card ι : ℝ) ^ p.toReal⁻¹ := by
  rw [lpNorm_of_ne_top hp]
  simp [Real.one_rpow, Finset.sum_const, nsmul_eq_mul]

/-- Hölder's inequality for the scalar product of finite real vectors, for
conjugate exponents `p`, `q` including the endpoint pairs `(1, ⊤)` and `(⊤, 1)`. -/
theorem abs_dot_le_lpNorm_mul_lpNorm {p q : ℝ≥0∞} (hpq : ENNReal.HolderConjugate p q)
    (x y : ι → ℝ) : |∑ k, x k * y k| ≤ lpNorm p x * lpNorm q y := by
  have habs : |∑ k, x k * y k| ≤ ∑ k, |x k| * |y k| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
  have hxs : ∀ k, |x k| ≤ ⨆ k, |x k| :=
    fun k => le_ciSup (Set.finite_range fun k => |x k|).bddAbove k
  have hys : ∀ k, |y k| ≤ ⨆ k, |y k| :=
    fun k => le_ciSup (Set.finite_range fun k => |y k|).bddAbove k
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hpq' := holderConjugate_cases hpq
  · rw [lpNorm_top, lpNorm_one]
    refine habs.trans ?_
    calc ∑ k, |x k| * |y k| ≤ ∑ k, (⨆ k, |x k|) * |y k| :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hxs k) (abs_nonneg _)
      _ = (⨆ k, |x k|) * ∑ k, |y k| := (Finset.mul_sum _ _ _).symm
  · rw [lpNorm_one, lpNorm_top]
    refine habs.trans ?_
    calc ∑ k, |x k| * |y k| ≤ ∑ k, |x k| * ⨆ k, |y k| :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hys k) (abs_nonneg _)
      _ = (∑ k, |x k|) * ⨆ k, |y k| := (Finset.sum_mul _ _ _).symm
  · have hpne : p ≠ ⊤ := by
      rintro rfl
      have := hpq'.lt
      norm_num at this
    have hqne : q ≠ ⊤ := by
      rintro rfl
      have := hpq'.symm.lt
      norm_num at this
    rw [lpNorm_of_ne_top hpne, lpNorm_of_ne_top hqne]
    have h := Real.inner_le_Lp_mul_Lq Finset.univ (fun k => |x k|) (fun k => |y k|) hpq'
    rw [one_div, one_div] at h
    refine habs.trans ?_
    simpa [abs_abs] using h

/-- The comparison `‖x‖₁ ≤ d^{1/p} ‖x‖_{p'}` for conjugate exponents `p` and
`q = p'`, with the dimension factor `d^{1/p}` equal to `1` at `p = ⊤`. -/
theorem sum_abs_le_card_pow_mul_lpNorm {p q : ℝ≥0∞} (hpq : ENNReal.HolderConjugate p q)
    (x : ι → ℝ) : ∑ k, |x k| ≤ (Fintype.card ι : ℝ) ^ p.toReal⁻¹ * lpNorm q x := by
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hpq' := holderConjugate_cases hpq
  · rw [lpNorm_one]
    simp
  · rw [lpNorm_top]
    have h1 : ∀ k, |x k| ≤ ⨆ k, |x k| :=
      fun k => le_ciSup (Set.finite_range fun k => |x k|).bddAbove k
    refine (Finset.sum_le_sum fun k _ => h1 k).trans ?_
    rw [Finset.sum_const]
    simp [nsmul_eq_mul]
  · have hpne : p ≠ ⊤ := by
      rintro rfl
      have := hpq'.lt
      norm_num at this
    have h := abs_dot_le_lpNorm_mul_lpNorm hpq (fun _ : ι => (1:ℝ)) (fun k => |x k|)
    have h3 : abs (∑ k, (1:ℝ) * |x k|) = ∑ k, |x k| := by
      have hnn : 0 ≤ ∑ k, (1:ℝ) * |x k| :=
        Finset.sum_nonneg fun k _ => mul_nonneg zero_le_one (abs_nonneg _)
      rw [abs_of_nonneg hnn]
      simp
    rw [h3, lpNorm_const_one hpne, lpNorm_abs] at h
    exact h

/-- Existence of a norming vector: for conjugate exponents `p`, `q = p'`, some
vector `v` in the closed unit ball of `ℓ^p` satisfies `∑ k, v k * x k = ‖x‖_{p'}`.
This is the equality case of Hölder's inequality used in the manuscript's
`lem:freq_quantization`, including the endpoints `(p, q) = (⊤, 1)` and `(1, ⊤)`. -/
theorem exists_lpNorm_norming {p q : ℝ≥0∞} (hpq : ENNReal.HolderConjugate p q)
    {x : ι → ℝ} (hx : 0 < lpNorm q x) :
    ∃ v : ι → ℝ, lpNorm p v ≤ 1 ∧ ∑ k, v k * x k = lpNorm q x := by
  classical
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hpq' := holderConjugate_cases hpq
  · refine ⟨fun k => if 0 ≤ x k then (1:ℝ) else -1, ?_, ?_⟩
    · rw [lpNorm_top]
      refine Real.iSup_le (fun k => ?_) (by norm_num)
      by_cases h : 0 ≤ x k <;> simp [h]
    · have hsum : ∀ k, (if 0 ≤ x k then (1:ℝ) else -1) * x k = |x k| := by
        intro k
        by_cases h : 0 ≤ x k
        · rw [if_pos h, one_mul, abs_of_nonneg h]
        · rw [if_neg h, neg_one_mul, abs_of_neg (lt_of_not_ge h)]
      simp only [hsum]
      rw [lpNorm_one]
  · have hne : Nonempty ι := by
      rcases isEmpty_or_nonempty ι with h | h
      · letI := h
        rw [lpNorm_top] at hx
        simp at hx
      · exact h
    letI := hne
    obtain ⟨k₀, _, hk₀⟩ :=
      Finset.exists_max_image Finset.univ (fun k => |x k|) Finset.univ_nonempty
    have hmax : lpNorm ⊤ x = |x k₀| := by
      rw [lpNorm_top]
      exact le_antisymm
        (Real.iSup_le (fun k => hk₀ k (Finset.mem_univ k)) (abs_nonneg _))
        (le_ciSup (Set.finite_range fun k => |x k|).bddAbove k₀)
    refine ⟨fun k => if k = k₀ then (if 0 ≤ x k₀ then (1:ℝ) else -1) else 0, ?_, ?_⟩
    · rw [lpNorm_one]
      have h1 : ∑ k, |if k = k₀ then (if 0 ≤ x k₀ then (1:ℝ) else -1) else 0|
          = |if 0 ≤ x k₀ then (1:ℝ) else -1| := by
        rw [Finset.sum_eq_single k₀]
        · simp
        · intro b _ hb
          simp [hb]
        · intro hk
          exact absurd (Finset.mem_univ k₀) hk
      rw [h1]
      by_cases h : 0 ≤ x k₀ <;> simp [h]
    · have h2 : ∑ k, (if k = k₀ then (if 0 ≤ x k₀ then (1:ℝ) else -1) else 0) * x k
          = (if 0 ≤ x k₀ then (1:ℝ) else -1) * x k₀ := by
        rw [Finset.sum_eq_single k₀]
        · simp
        · intro b _ hb
          simp [hb]
        · intro hk
          exact absurd (Finset.mem_univ k₀) hk
      rw [h2, hmax]
      by_cases h : 0 ≤ x k₀
      · rw [if_pos h, one_mul, abs_of_nonneg h]
      · rw [if_neg h, neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  · have hpne : p ≠ ⊤ := by
      rintro rfl
      have := hpq'.lt
      norm_num at this
    have hqne : q ≠ ⊤ := by
      rintro rfl
      have := hpq'.symm.lt
      norm_num at this
    set f : ι → ℝ≥0 := fun k => |x k|.toNNReal
    have hfp : ∀ k, (f k : ℝ) = |x k| := fun k => Real.coe_toNNReal _ (abs_nonneg _)
    have hgreatest := NNReal.isGreatest_Lp Finset.univ f (p := q.toReal) (q := p.toReal) hpq'.symm
    obtain ⟨g, hgmem, hval⟩ := hgreatest.1
    have hgm : ∑ k, g k ^ p.toReal ≤ (1 : ℝ≥0) := by
      simpa only [Set.mem_setOf_eq] using hgmem
    refine ⟨fun k => (if 0 ≤ x k then (1:ℝ) else -1) * (g k : ℝ), ?_, ?_⟩
    · have habs : ∀ k,
          |(if 0 ≤ x k then (1:ℝ) else -1) * (g k : ℝ)| = |(g k : ℝ)| := by
        intro k
        by_cases h : 0 ≤ x k
        · rw [if_pos h, one_mul]
        · rw [if_neg h, neg_one_mul, abs_neg]
      have h2 : lpNorm p (fun k => (if 0 ≤ x k then (1:ℝ) else -1) * (g k : ℝ))
          = lpNorm p (fun k => |(g k : ℝ)|) := by
        rw [← lpNorm_abs]
        congr 1 with k
        exact habs k
      rw [h2, ← lpNorm_abs, lpNorm_of_ne_top hpne]
      have hcoerce : (∑ k, |(g k : ℝ)| ^ p.toReal) = ((∑ k, g k ^ p.toReal : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [abs_of_nonneg (NNReal.coe_nonneg (g k)), NNReal.coe_rpow]
      have hle : (∑ k, |(g k : ℝ)| ^ p.toReal) ≤ 1 := by
        rw [hcoerce]
        exact_mod_cast hgm
      have := Real.rpow_le_rpow (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (abs_nonneg _) _)
        hle (inv_nonneg.mpr (ENNReal.toReal_nonneg (a := p)))
      rw [Real.one_rpow] at this
      simpa [abs_abs] using this
    · have hvx : ∀ k,          (if 0 ≤ x k then (1:ℝ) else -1) * (g k : ℝ) * x k = (g k : ℝ) * |x k| := by
        intro k
        by_cases h : 0 ≤ x k
        · rw [if_pos h, one_mul, abs_of_nonneg h]
        · rw [if_neg h, abs_of_neg (lt_of_not_ge h)]
          ring
      have hsum : ∑ k, (if 0 ≤ x k then (1:ℝ) else -1) * (g k : ℝ) * x k
          = ∑ k, (g k : ℝ) * |x k| :=
        Finset.sum_congr rfl fun k _ => hvx k
      rw [hsum]
      have hcast : (∑ k, (f k : ℝ) * (g k : ℝ))
          = ((∑ k, f k * g k : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [NNReal.coe_mul]
      have hval' : ((∑ k, f k * g k : ℝ≥0) : ℝ)
          = ((∑ k, f k ^ q.toReal : ℝ≥0) ^ (q.toReal)⁻¹ : ℝ≥0) := by
        have hvalb : (∑ i, f i * g i : ℝ≥0) = (∑ i, f i ^ q.toReal : ℝ≥0) ^ (1 / q.toReal) :=
          hval
        rw [hvalb, one_div]
      have h3 : ((∑ k, f k ^ q.toReal : ℝ≥0) ^ (q.toReal)⁻¹ : ℝ≥0)
          = (∑ k, |x k| ^ q.toReal) ^ (q.toReal)⁻¹ := by
        push_cast
        congr 1
        congr 1 with k
        rw [hfp]
      have h4 : ∑ k, (g k : ℝ) * |x k| = ∑ k, (f k : ℝ) * (g k : ℝ) :=
        Finset.sum_congr rfl fun k _ => by rw [hfp, mul_comm]
      rw [h4, hcast, hval', h3, lpNorm_of_ne_top hqne]

end LeanNumDetect
