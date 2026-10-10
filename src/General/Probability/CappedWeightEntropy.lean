import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Scalar entropy and finite layer-cake estimates for capped row weighting. -/

set_option autoImplicit false

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section

def cappedEntropy (R t : ℝ) : ℝ :=
  if t ≤ R then t else R + R * Real.log (t/R)

def cappedWeight (R t : ℝ) : ℝ :=
  if t ≤ R then 1 else R/t

theorem cappedWeight_pos_le_one {R t : ℝ} (hR : 0 < R) (_ht : 0 ≤ t) :
    0 < cappedWeight R t ∧ cappedWeight R t ≤ 1 := by
  unfold cappedWeight
  split_ifs with h
  · norm_num
  · have ht' : 0 < t := lt_trans hR (lt_of_not_ge h)
    exact ⟨div_pos hR ht', (div_le_one ht').mpr (le_of_lt (lt_of_not_ge h))⟩

theorem cappedWeight_antitone {R t u : ℝ} (hR : 0 < R)
    (_ht : 0 ≤ t) (_hu : 0 ≤ u) (htu : t ≤ u) :
    cappedWeight R u ≤ cappedWeight R t := by
  by_cases huR : u ≤ R
  · simp [cappedWeight, huR, htu.trans huR]
  · have hu' : 0 < u := hR.trans (lt_of_not_ge huR)
    rw [cappedWeight, if_neg huR]
    by_cases htR : t ≤ R
    · rw [cappedWeight, if_pos htR]
      exact (div_le_one hu').mpr (le_of_lt (lt_of_not_ge huR))
    · rw [cappedWeight, if_neg htR]
      exact div_le_div_of_nonneg_left hR.le (hR.trans (lt_of_not_ge htR)) htu

theorem cappedWeight_mul_le {R t : ℝ} (hR : 0 < R) (_ht : 0 ≤ t) :
    cappedWeight R t * t ≤ R := by
  unfold cappedWeight
  split_ifs with h
  · simpa using h
  · have ht' : 0 < t := hR.trans (lt_of_not_ge h)
    rw [div_mul_cancel₀ _ (ne_of_gt ht')]

theorem cappedEntropy_le {R t : ℝ} (hR : 0 < R) (_ht : 0 ≤ t) :
    cappedEntropy R t ≤ t := by
  unfold cappedEntropy
  split_ifs with h
  · exact le_rfl
  · have ht' : 0 < t := lt_trans hR (lt_of_not_ge h)
    have hl := Real.log_le_sub_one_of_pos (div_pos ht' hR)
    have hm := mul_le_mul_of_nonneg_left hl hR.le
    have he : R * (t/R-1) = t-R := by field_simp
    rw [he] at hm
    linarith

theorem cappedEntropy_log_lower {R t : ℝ} (hR : 0 < R) (ht : 0 ≤ t) :
    R * max 0 (Real.log (t/R)) ≤ cappedEntropy R t := by
  unfold cappedEntropy
  split_ifs with h
  · have hl : Real.log (t/R) ≤ 0 := Real.log_nonpos (div_nonneg ht hR.le)
      ((div_le_one hR).mpr h)
    rw [max_eq_left hl]
    simpa using ht
  · have hp : 1 < t/R := (one_lt_div hR).mpr (lt_of_not_ge h)
    have hl : 0 < Real.log (t/R) := Real.log_pos hp
    rw [max_eq_right hl.le]
    linarith

theorem cappedEntropy_nonneg {R t : ℝ} (hR : 0 < R) (ht : 0 ≤ t) :
    0 ≤ cappedEntropy R t :=
  (mul_nonneg hR.le (le_max_left _ _)).trans (cappedEntropy_log_lower hR ht)

/-- The tangent to the capped entropy is an upper bound at every nonnegative point. -/
theorem cappedEntropy_tangent {R t u : ℝ} (hR : 0 < R) (_ht : 0 ≤ t) (hu : 0 ≤ u) :
    cappedEntropy R u ≤ cappedEntropy R t + cappedWeight R t * (u-t) := by
  by_cases htR : t ≤ R
  · rw [show cappedEntropy R t = t by simp [cappedEntropy, htR],
      show cappedWeight R t = 1 by simp [cappedWeight, htR]]
    have hh := cappedEntropy_le hR hu
    linarith
  · have ht' : 0 < t := lt_trans hR (lt_of_not_ge htR)
    rw [show cappedEntropy R t = R + R*Real.log (t/R) by simp [cappedEntropy, htR],
      show cappedWeight R t = R/t by simp [cappedWeight, htR]]
    by_cases huR : u ≤ R
    · rw [cappedEntropy, if_pos huR]
      have hlog := Real.log_le_sub_one_of_pos (div_pos hR ht')
      have he : Real.log (R/t) = -Real.log (t/R) := by
        rw [Real.log_div (ne_of_gt hR) (ne_of_gt ht'),
          Real.log_div (ne_of_gt ht') (ne_of_gt hR)]
        ring
      rw [he] at hlog
      have hfrac : R/t ≤ 1 := (div_le_one ht').mpr (le_of_lt (lt_of_not_ge htR))
      have hm := mul_le_mul_of_nonneg_left (show 1-R/t ≤ Real.log (t/R) by linarith) hR.le
      have hmul := mul_le_mul_of_nonneg_right huR (sub_nonneg.mpr hfrac)
      have hc : (R/t)*t = R := by field_simp
      nlinarith
    · have hu' : 0 < u := lt_trans hR (lt_of_not_ge huR)
      rw [cappedEntropy, if_neg huR]
      have hl := Real.log_le_sub_one_of_pos (div_pos hu' ht')
      have he : Real.log (u/t) = Real.log (u/R) - Real.log (t/R) := by
        rw [Real.log_div (ne_of_gt hu') (ne_of_gt ht'),
          Real.log_div (ne_of_gt hu') (ne_of_gt hR),
          Real.log_div (ne_of_gt ht') (ne_of_gt hR)]
        ring
      rw [he] at hl
      have hm := mul_le_mul_of_nonneg_left hl hR.le
      have hc : R*(u/t-1) = (R/t)*(u-t) := by field_simp
      rw [hc] at hm
      linarith

/-- A finite layer-cake lower sum never exceeds the nonnegative row value. -/
theorem threshold_layercake_pointwise (a : ℕ → ℝ) (b : ℝ) (_hb : 0 ≤ b)
    (n : ℕ) (ha : ∀ k < n, a (k+1) ≤ a k) :
    (∑ k ∈ Finset.range n, if a k ≤ b then a k-a (k+1) else 0) ≤
      max 0 (b-a n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun k hk => ha k (by omega))
    rw [Finset.sum_range_succ]
    by_cases h : a n ≤ b
    · rw [if_pos h, max_eq_right (sub_nonneg.mpr h)] at *
      have hn : a (n+1) ≤ b := (ha n (by omega)).trans h
      rw [max_eq_right (sub_nonneg.mpr hn)]
      linarith
    · rw [if_neg h]
      have he : max 0 (b-a n) = 0 := max_eq_left (by linarith)
      rw [he] at ih'
      simpa only [add_zero] using ih'.trans (le_max_left 0 (b-a (n+1)))

theorem sum_weighted_differences (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ((k : ℝ)+1)*(a k-a (k+1))) =
      (∑ k ∈ Finset.range n, a k) - (n : ℝ)*a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Threshold counts imply an averaged lower bound without an integral or
an infinite layer-cake formula. The count scale `p` includes the population size. -/
theorem sum_lower_of_threshold_counts {ι : Type*} [Fintype ι]
    (a : ℕ → ℝ) (b : ι → ℝ) (n : ℕ) (p : ℝ)
    (hb : ∀ i, 0 ≤ b i) (ha : ∀ k < n, a (k+1) ≤ a k) (han : a n = 0)
    (hcount : ∀ k < n, p*((k : ℝ)+1) ≤
      ((Finset.univ.filter (fun i => a k ≤ b i)).card : ℝ)) :
    p*(∑ k ∈ Finset.range n, a k) ≤ ∑ i, b i := by
  classical
  have hpoint (i : ι) :
      (∑ k ∈ Finset.range n, if a k ≤ b i then a k-a (k+1) else 0) ≤ b i := by
    simpa only [han, sub_zero, max_eq_right (hb i)] using
      threshold_layercake_pointwise a (b i) (hb i) n ha
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hpoint i)
  rw [Finset.sum_comm] at hh
  have hsum : (∑ k ∈ Finset.range n, p*(((k : ℝ)+1)*(a k-a (k+1)))) ≤
      ∑ k ∈ Finset.range n, ∑ i, if a k ≤ b i then a k-a (k+1) else 0 := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hc := mul_le_mul_of_nonneg_right (hcount k hk') (sub_nonneg.mpr (ha k hk'))
    have he : (∑ i, if a k ≤ b i then a k-a (k+1) else 0) =
        ((Finset.univ.filter (fun i => a k ≤ b i)).card : ℝ)*(a k-a (k+1)) := by
      rw [← Finset.sum_filter]
      simp
      ring
    rw [he]
    convert hc using 1; ring
  have he : (∑ k ∈ Finset.range n, p*(((k : ℝ)+1)*(a k-a (k+1)))) =
      p*(∑ k ∈ Finset.range n, a k) := by
    rw [← Finset.mul_sum, sum_weighted_differences, han]
    simp
  rw [he] at hsum
  exact hsum.trans hh

theorem cappedEntropy_sum_lower_of_threshold_counts {ι : Type*} [Fintype ι]
    {R : ℝ} (hR : 0 < R) (a : ℕ → ℝ) (l : ι → ℝ) (n : ℕ) (p : ℝ)
    (hl : ∀ i, 0 ≤ l i) (ha : ∀ k < n, a (k+1) ≤ a k) (han : a n = 0)
    (hcount : ∀ k < n, p*((k : ℝ)+1) ≤
      ((Finset.univ.filter (fun i => a k ≤ max 0 (Real.log (l i/R)))).card : ℝ)) :
    R*p*(∑ k ∈ Finset.range n, a k) ≤ ∑ i, cappedEntropy R (l i) := by
  have hh := sum_lower_of_threshold_counts a (fun i => max 0 (Real.log (l i/R))) n p
    (fun i => le_max_left _ _) ha han hcount
  have hm := mul_le_mul_of_nonneg_left hh hR.le
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    cappedEntropy_log_lower hR (hl i))
  rw [← Finset.mul_sum] at hs
  have hh' := hm.trans hs
  simpa only [mul_assoc] using hh'

/-- The stronger translate-count fraction yields a quantitative entropy floor. -/
theorem cappedEntropy_sum_coercivity {n : ℕ} (hn : 0 < n)
    (C hmean : ℝ) (t : Fin n → ℝ)
    (hentropy : ((n : ℝ)+1)/(n : ℝ) * (∑ j, max 0 (t j-C)) ≤ hmean)
    (hupper : -(∑ j, t j)+hmean ≤ (n : ℝ)) :
    (∑ j, t j) ≤ (n : ℝ)^2 + (n : ℝ)*((n : ℝ)+1)*C := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (∑ j, t j) - (n : ℝ)*C ≤ ∑ j, max 0 (t j-C) := by
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      le_max_right 0 (t j-C))
    simpa [Finset.sum_sub_distrib] using hh
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ ((n : ℝ)+1)/(n : ℝ) by positivity)
  have he : ((n : ℝ)+1)/(n : ℝ)*((∑ j, t j)-(n : ℝ)*C) =
      ((∑ j, t j)/(n : ℝ))+(∑ j, t j)-((n : ℝ)+1)*C := by field_simp; ring
  rw [he] at hm
  have hh : ((∑ j, t j)/(n : ℝ)) ≤ (n : ℝ)+((n : ℝ)+1)*C := by linarith
  have hf := (div_le_iff₀ hn').mp hh
  nlinarith

theorem log_prod_add_card_le_sum {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    Real.log (∏ i, a i) + (Fintype.card ι : ℝ) ≤ ∑ i, a i := by
  rw [Real.log_prod (fun i _ => ne_of_gt (ha i))]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Real.log_le_sub_one_of_pos (ha i))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, mul_one] at hh
  linarith

end
end LeanNumDetect.FiniteMatrixSampling
