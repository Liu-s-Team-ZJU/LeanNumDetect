/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Euler's cotangent-square identity: `∑_{n ∈ ℤ} 1/(n+s)² = π²/sin²(πs)`

For real non-integer `s`,

  `∑' n : ℤ, 1/((n : ℝ) + s)^2 = π^2 / sin(s*π)^2`.

This is obtained from Mathlib's Mittag-Leffler expansion of the cotangent
(`cot_series_rep'`, in `Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent`):

  `π·cot(πx) − 1/x = ∑' n : ℕ, (1/(x−(n+1)) + 1/(x+(n+1)))`   (`x ∈ ℂ \ ℤ`)

by term-by-term differentiation along the real line at the point `s`, using
`hasDerivAt_tsum_of_isPreconnected` on a small interval around `s` that avoids
the integers (with a summable uniform bound `K/(n+1)²` on the derivative
terms). The derivative of the left side is `−π²/sin²(πs) + 1/s²`; the
derivative of the right side is `−∑' n, (1/(s−(n+1))² + 1/(s+(n+1))²)`.
Rearranging and folding the `ℕ`-indexed sum into a `ℤ`-indexed sum gives the
identity.

Used to discharge the axiom `htern_lem_2_3_euler_cot_sq_source_ax`
(Helfgott, arXiv:1501.05438v2, §2.3, eq. (2.4)).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.PSeries

noncomputable section

open Complex Real Set Filter

namespace MathExtras
namespace CotangentSquareSum

/-- A real number avoiding all integer shifts is in the complex integer
complement. -/
lemma ofReal_mem_integerComplement {s : ℝ} (hs : ∀ n : ℤ, (n : ℝ) + s ≠ 0) :
    (s : ℂ) ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have hn' : (n : ℝ) = s := by exact_mod_cast hn
  exact hs (-n) (by push_cast; rw [hn']; ring)

/-- Around a non-integer real `s` there is a margin `d` such that the interval
`(s - d/2, s + d/2)` keeps distance `d/2` from every integer. -/
lemma exists_gap {s : ℝ} (hs : ∀ n : ℤ, (n : ℝ) + s ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ∀ y ∈ Ioo (s - d / 2) (s + d / 2), ∀ k : ℤ, d / 2 ≤ |y - k| := by
  set m : ℤ := ⌊s⌋ with hm
  have hfloor : (m : ℝ) ≤ s := Int.floor_le s
  have hlt : s < (m : ℝ) + 1 := Int.lt_floor_add_one s
  have hne : (m : ℝ) ≠ s := fun h => hs (-m) (by push_cast; rw [h]; ring)
  have hflt : (m : ℝ) < s := lt_of_le_of_ne hfloor hne
  refine ⟨min (s - m) ((m : ℝ) + 1 - s), by positivity, ?_, ?_⟩
  · exact le_trans (min_le_right _ _) (by linarith)
  · intro y hy k
    obtain ⟨hy1, hy2⟩ := hy
    have hd1 : min (s - m) ((m : ℝ) + 1 - s) ≤ s - m := min_le_left _ _
    have hd2 : min (s - m) ((m : ℝ) + 1 - s) ≤ (m : ℝ) + 1 - s := min_le_right _ _
    rcases le_or_gt (k : ℝ) (m : ℝ) with hk | hk
    · -- k ≤ m : the point y sits at least d/2 above k
      refine le_abs.mpr (Or.inl ?_)
      linarith
    · -- k ≥ m + 1
      have hk' : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (by exact_mod_cast hk : m < k)
      refine le_abs.mpr (Or.inr ?_)
      linarith

/-- The complex form at a real point: term-by-term differentiation of
Mathlib's cotangent Mittag-Leffler series. -/
theorem complex_pi_sq_div_sin_sq {s : ℝ} (hs : ∀ n : ℤ, (n : ℝ) + s ≠ 0) :
    ((π : ℂ)) ^ 2 / Complex.sin ((π : ℂ) * (s : ℂ)) ^ 2
      = 1 / (s : ℂ) ^ 2
        + ∑' n : ℕ, (1 / ((s : ℂ) - (n + 1)) ^ 2 + 1 / ((s : ℂ) + (n + 1)) ^ 2) := by
  classical
  obtain ⟨d, hd, hd1, hgap⟩ := exists_gap hs
  have hd2 : 0 < d / 2 := by positivity
  set t : Set ℝ := Ioo (s - d / 2) (s + d / 2) with ht_def
  have ht : IsOpen t := isOpen_Ioo
  have htc : IsPreconnected t := (convex_Ioo _ _).isPreconnected
  have hst : s ∈ t := ⟨by linarith, by linarith⟩
  -- every point of t is a non-integer real
  have hyC : ∀ y ∈ t, (y : ℂ) ∈ Complex.integerComplement := by
    intro y hy
    rintro ⟨k, hk⟩
    have hk' : (k : ℝ) = y := by exact_mod_cast hk
    have := hgap y hy k
    rw [hk'] at this
    simp only [sub_self, abs_zero] at this
    linarith
  -- nonvanishing of the shifted denominators on t
  have hne : ∀ y ∈ t, ∀ k : ℤ, (y : ℂ) + (k : ℂ) ≠ 0 := fun y hy k =>
    Complex.integerComplement_add_ne_zero (hyC y hy) k
  have hne_sub : ∀ y ∈ t, ∀ n : ℕ, (y : ℂ) - ((n : ℂ) + 1) ≠ 0 := by
    intro y hy n
    have := hne y hy (-(n + 1))
    push_cast at this
    simpa [sub_eq_add_neg] using this
  have hne_add : ∀ y ∈ t, ∀ n : ℕ, (y : ℂ) + ((n : ℂ) + 1) ≠ 0 := by
    intro y hy n
    have := hne y hy (n + 1)
    push_cast at this
    exact this
  -- the series terms and their derivatives, as functions ℝ → ℂ
  set g : ℕ → ℝ → ℂ :=
    fun n y => 1 / ((y : ℂ) - ((n : ℂ) + 1)) + 1 / ((y : ℂ) + ((n : ℂ) + 1)) with hg_def
  set g' : ℕ → ℝ → ℂ :=
    fun n y => -(1 / ((y : ℂ) - ((n : ℂ) + 1)) ^ 2) - 1 / ((y : ℂ) + ((n : ℂ) + 1)) ^ 2
    with hg'_def
  have hgderiv : ∀ n : ℕ, ∀ y ∈ t, HasDerivAt (g n) (g' n y) y := by
    intro n y hy
    have d1 : HasDerivAt (fun z : ℂ => z - ((n : ℂ) + 1)) 1 (y : ℂ) :=
      (hasDerivAt_id _).sub_const _
    have d2 : HasDerivAt (fun z : ℂ => z + ((n : ℂ) + 1)) 1 (y : ℂ) :=
      (hasDerivAt_id _).add_const _
    have i1 := d1.inv (by simpa using hne_sub y hy n)
    have i2 := d2.inv (by simpa using hne_add y hy n)
    have hC : HasDerivAt
        (fun z : ℂ => (z - ((n : ℂ) + 1))⁻¹ + (z + ((n : ℂ) + 1))⁻¹)
        (-1 / ((y : ℂ) - ((n : ℂ) + 1)) ^ 2 + -1 / ((y : ℂ) + ((n : ℂ) + 1)) ^ 2)
        (y : ℂ) := i1.add i2
    have := hC.comp_ofReal
    simp only [hg_def, hg'_def, one_div]
    convert this using 1
    ring
  -- summable uniform bound on the derivatives over t
  set R : ℝ := |s| + 1 with hR_def
  have hR1 : 1 ≤ R := by rw [hR_def]; linarith [abs_nonneg s]
  set K : ℝ := max 8 (8 * (2 * R) ^ 2 / (d / 2) ^ 2) with hK_def
  have hK8 : (8 : ℝ) ≤ K := le_max_left _ _
  set u : ℕ → ℝ := fun n => K / ((n : ℝ) + 1) ^ 2 with hu_def
  have hu : Summable u := by
    have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      have := (summable_nat_add_iff 1).mpr h1
      simpa using this
    simpa [hu_def, div_eq_mul_inv, one_div] using h2.mul_left K
  have hyabs : ∀ y ∈ t, |y| ≤ R := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [abs_le]
    constructor
    · have := neg_abs_le s; linarith
    · have := le_abs_self s; linarith
  have hbound : ∀ n : ℕ, ∀ y ∈ t, ‖g' n y‖ ≤ u n := by
    intro n y hy
    have hyR := hyabs y hy
    -- norms of the two pieces
    have e1 : ‖(1 : ℂ) / ((y : ℂ) - ((n : ℂ) + 1)) ^ 2‖
        = 1 / |y - ((n : ℝ) + 1)| ^ 2 := by
      have hcast : ((y : ℂ) - ((n : ℂ) + 1)) = ((y - ((n : ℝ) + 1) : ℝ) : ℂ) := by
        push_cast; ring
      rw [norm_div, norm_one, norm_pow, hcast, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(1 : ℂ) / ((y : ℂ) + ((n : ℂ) + 1)) ^ 2‖
        = 1 / |y + ((n : ℝ) + 1)| ^ 2 := by
      have hcast : ((y : ℂ) + ((n : ℂ) + 1)) = ((y + ((n : ℝ) + 1) : ℝ) : ℂ) := by
        push_cast; ring
      rw [norm_div, norm_one, norm_pow, hcast, Complex.norm_real, Real.norm_eq_abs]
    have hnorm : ‖g' n y‖ ≤ 1 / |y - ((n : ℝ) + 1)| ^ 2 + 1 / |y + ((n : ℝ) + 1)| ^ 2 := by
      simp only [hg'_def]
      calc ‖-(1 / ((y : ℂ) - ((n : ℂ) + 1)) ^ 2) - 1 / ((y : ℂ) + ((n : ℂ) + 1)) ^ 2‖
          = ‖-((1 / ((y : ℂ) - ((n : ℂ) + 1)) ^ 2) + 1 / ((y : ℂ) + ((n : ℂ) + 1)) ^ 2)‖ := by
            ring_nf
        _ ≤ ‖(1 : ℂ) / ((y : ℂ) - ((n : ℂ) + 1)) ^ 2‖
              + ‖(1 : ℂ) / ((y : ℂ) + ((n : ℂ) + 1)) ^ 2‖ := by
            rw [norm_neg]; exact norm_add_le _ _
        _ = 1 / |y - ((n : ℝ) + 1)| ^ 2 + 1 / |y + ((n : ℝ) + 1)| ^ 2 := by rw [e1, e2]
    -- lower bounds for the denominators
    have a1 : d / 2 ≤ |y - ((n : ℝ) + 1)| := by
      have := hgap y hy ((n : ℤ) + 1)
      push_cast at this
      exact this
    have a2 : d / 2 ≤ |y + ((n : ℝ) + 1)| := by
      have h := hgap y hy (-((n : ℤ) + 1))
      push_cast at h
      convert h using 2
      ring
    have b1 : (n : ℝ) + 1 - R ≤ |y - ((n : ℝ) + 1)| := by
      have h := abs_sub_abs_le_abs_sub ((n : ℝ) + 1) y
      rw [abs_sub_comm] at h
      have hn1 : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_nonneg (by positivity)
      linarith [hn1 ▸ h]
    have b2 : (n : ℝ) + 1 - R ≤ |y + ((n : ℝ) + 1)| := by
      have h : |(n : ℝ) + 1| - |y| ≤ |((n : ℝ) + 1) + y| := abs_sub_abs_le_abs_add _ _
      have hn1 : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_nonneg (by positivity)
      rw [hn1, add_comm ((n : ℝ) + 1) y] at h
      linarith
    have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rcases le_or_gt (2 * R) ((n : ℝ) + 1) with hcase | hcase
    · -- decay regime: |y ∓ (n+1)| ≥ (n+1)/2
      have hhalf : ((n : ℝ) + 1) / 2 ≤ (n : ℝ) + 1 - R := by linarith
      have c1 : ((n : ℝ) + 1) / 2 ≤ |y - ((n : ℝ) + 1)| := le_trans hhalf b1
      have c2 : ((n : ℝ) + 1) / 2 ≤ |y + ((n : ℝ) + 1)| := le_trans hhalf b2
      have hpos : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by positivity
      have d1' : 1 / |y - ((n : ℝ) + 1)| ^ 2 ≤ 1 / (((n : ℝ) + 1) / 2) ^ 2 := by
        gcongr
      have d2' : 1 / |y + ((n : ℝ) + 1)| ^ 2 ≤ 1 / (((n : ℝ) + 1) / 2) ^ 2 := by
        gcongr
      have hsum : 1 / |y - ((n : ℝ) + 1)| ^ 2 + 1 / |y + ((n : ℝ) + 1)| ^ 2
          ≤ 8 / ((n : ℝ) + 1) ^ 2 := by
        have h48 : (4 : ℝ) / ((n : ℝ) + 1) ^ 2 + 4 / ((n : ℝ) + 1) ^ 2
            = 8 / ((n : ℝ) + 1) ^ 2 := by ring
        have heq : (1 : ℝ) / (((n : ℝ) + 1) / 2) ^ 2 = 4 / ((n : ℝ) + 1) ^ 2 := by
          field_simp; ring
        rw [heq] at d1' d2'
        linarith
      refine le_trans hnorm (le_trans hsum ?_)
      show (8 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ K / ((n : ℝ) + 1) ^ 2
      gcongr
    · -- bounded regime: use the gap d/2 and (n+1) < 2R
      have d1' : 1 / |y - ((n : ℝ) + 1)| ^ 2 ≤ 1 / (d / 2) ^ 2 := by gcongr
      have d2' : 1 / |y + ((n : ℝ) + 1)| ^ 2 ≤ 1 / (d / 2) ^ 2 := by gcongr
      have hsum : 1 / |y - ((n : ℝ) + 1)| ^ 2 + 1 / |y + ((n : ℝ) + 1)| ^ 2
          ≤ 2 / (d / 2) ^ 2 := by
        have : (2 : ℝ) / (d / 2) ^ 2 = 1 / (d / 2) ^ 2 + 1 / (d / 2) ^ 2 := by ring
        rw [this]
        exact add_le_add d1' d2'
      refine le_trans hnorm (le_trans hsum ?_)
      -- 2/(d/2)² ≤ K/(n+1)²  since (n+1)² < (2R)² and K ≥ 8(2R)²/(d/2)²
      show (2 : ℝ) / (d / 2) ^ 2 ≤ K / ((n : ℝ) + 1) ^ 2
      have h2R : (0 : ℝ) < 2 * R := by linarith
      have hKge : 8 * (2 * R) ^ 2 / (d / 2) ^ 2 ≤ K := le_max_right _ _
      have hK0 : (0 : ℝ) ≤ K := by linarith
      have hsq : ((n : ℝ) + 1) ^ 2 ≤ (2 * R) ^ 2 := by nlinarith
      have step1 : (2 : ℝ) / (d / 2) ^ 2 ≤ 8 / (d / 2) ^ 2 := by gcongr; norm_num
      have step2 : (8 : ℝ) / (d / 2) ^ 2 = 8 * (2 * R) ^ 2 / (d / 2) ^ 2 / (2 * R) ^ 2 := by
        field_simp
      have step3 : 8 * (2 * R) ^ 2 / (d / 2) ^ 2 / (2 * R) ^ 2 ≤ K / (2 * R) ^ 2 := by gcongr
      have step4 : K / (2 * R) ^ 2 ≤ K / ((n : ℝ) + 1) ^ 2 := by gcongr
      linarith [step2 ▸ step1]
  -- convergence at the base point s
  have hsC : (s : ℂ) ∈ Complex.integerComplement := ofReal_mem_integerComplement hs
  have hg0 : Summable fun n => g n s := by
    have := summable_cotTerm hsC
    simpa [hg_def, cotTerm] using this
  -- term-by-term differentiation
  have key : HasDerivAt (fun y : ℝ => ∑' n, g n y) (∑' n, g' n s) s :=
    hasDerivAt_tsum_of_isPreconnected hu ht htc hgderiv hbound hst hg0 hst
  -- the closed form of the left-hand side and its derivative
  have hs0 : s ≠ 0 := by
    have := hs 0
    simpa using this
  have hsne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0
  have hsin : Complex.sin ((π : ℂ) * (s : ℂ)) ≠ 0 := sin_pi_mul_ne_zero hsC
  have hFc : HasDerivAt (fun z : ℂ => (π : ℂ) * Complex.cot ((π : ℂ) * z) - 1 / z)
      (-(π : ℂ) ^ 2 / Complex.sin ((π : ℂ) * (s : ℂ)) ^ 2 + 1 / (s : ℂ) ^ 2) (s : ℂ) := by
    simp only [Complex.cot_eq_cos_div_sin]
    have hπz : HasDerivAt (fun z : ℂ => (π : ℂ) * z) (π : ℂ) (s : ℂ) := by
      simpa using (hasDerivAt_id ((s : ℂ))).const_mul (π : ℂ)
    have hcos : HasDerivAt (fun z : ℂ => Complex.cos ((π : ℂ) * z))
        (-Complex.sin ((π : ℂ) * (s : ℂ)) * (π : ℂ)) (s : ℂ) :=
      (Complex.hasDerivAt_cos ((π : ℂ) * (s : ℂ))).comp (s : ℂ) hπz
    have hsin' : HasDerivAt (fun z : ℂ => Complex.sin ((π : ℂ) * z))
        (Complex.cos ((π : ℂ) * (s : ℂ)) * (π : ℂ)) (s : ℂ) :=
      (Complex.hasDerivAt_sin ((π : ℂ) * (s : ℂ))).comp (s : ℂ) hπz
    have hdiv := (hcos.div hsin' hsin).const_mul (π : ℂ)
    have hinv : HasDerivAt (fun z : ℂ => 1 / z) (-(1 / (s : ℂ) ^ 2)) (s : ℂ) := by
      simpa [one_div] using hasDerivAt_inv hsne
    have htot := hdiv.sub hinv
    refine htot.congr_deriv ?_
    have hpyth := Complex.sin_sq_add_cos_sq ((π : ℂ) * (s : ℂ))
    field_simp
    linear_combination -(((π : ℂ)) ^ 2 * (s : ℂ) ^ 2 * hpyth)
  have hF : HasDerivAt (fun y : ℝ => (π : ℂ) * Complex.cot ((π : ℂ) * (y : ℂ)) - 1 / (y : ℂ))
      (-(π : ℂ) ^ 2 / Complex.sin ((π : ℂ) * (s : ℂ)) ^ 2 + 1 / (s : ℂ) ^ 2) s :=
    hFc.comp_ofReal
  -- the two functions agree near s
  have heq : (fun y : ℝ => ∑' n, g n y)
      =ᶠ[nhds s] fun y : ℝ => (π : ℂ) * Complex.cot ((π : ℂ) * (y : ℂ)) - 1 / (y : ℂ) := by
    filter_upwards [ht.mem_nhds hst] with y hy
    have := cot_series_rep' (hyC y hy)
    simp only [hg_def]
    rw [this]
  have hF' : HasDerivAt (fun y : ℝ => ∑' n, g n y)
      (-(π : ℂ) ^ 2 / Complex.sin ((π : ℂ) * (s : ℂ)) ^ 2 + 1 / (s : ℂ) ^ 2) s :=
    hF.congr_of_eventuallyEq heq
  have hDeq : -(π : ℂ) ^ 2 / Complex.sin ((π : ℂ) * (s : ℂ)) ^ 2 + 1 / (s : ℂ) ^ 2
      = ∑' n, g' n s := hF'.unique key
  -- rearrange: ∑ g' = −∑ (1/(s−(n+1))² + 1/(s+(n+1))²)
  have hneg : ∑' n, g' n s
      = -∑' n : ℕ, (1 / ((s : ℂ) - ((n : ℂ) + 1)) ^ 2 + 1 / ((s : ℂ) + ((n : ℂ) + 1)) ^ 2) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    simp only [hg'_def]
    ring
  rw [hneg] at hDeq
  have hfinal : ((π : ℂ)) ^ 2 / Complex.sin ((π : ℂ) * (s : ℂ)) ^ 2
      = 1 / (s : ℂ) ^ 2
        + ∑' n : ℕ, (1 / ((s : ℂ) - ((n : ℂ) + 1)) ^ 2 + 1 / ((s : ℂ) + ((n : ℂ) + 1)) ^ 2) := by
    linear_combination -hDeq
  convert hfinal using 3

/-- The real form of the Mittag-Leffler half-sum. -/
theorem real_pi_sq_div_sin_sq {s : ℝ} (hs : ∀ n : ℤ, (n : ℝ) + s ≠ 0) :
    π ^ 2 / Real.sin (π * s) ^ 2
      = 1 / s ^ 2 + ∑' n : ℕ, (1 / (s - ((n : ℝ) + 1)) ^ 2 + 1 / (s + ((n : ℝ) + 1)) ^ 2) := by
  have h := complex_pi_sq_div_sin_sq hs
  rw [← Complex.ofReal_inj]
  push_cast [Complex.ofReal_tsum]
  exact h

/-- Summability of the shifted reciprocal squares over `ℤ`. -/
theorem summable_one_div_int_add_sq {s : ℝ} :
    Summable fun n : ℤ => (1 : ℝ) / ((n : ℝ) + s) ^ 2 := by
  by_cases hs : ∀ n : ℤ, (n : ℝ) + s ≠ 0
  · -- via the complex Eisenstein summability and finite-dimensionality
    have hC : Summable fun d : ℤ => (((s : ℂ) + (d : ℂ)) ^ 2)⁻¹ := by
      have h0 := EisensteinSeries.linear_right_summable (s : ℂ) 1 (k := 2) le_rfl
      apply h0.congr
      intro d
      rw [Int.cast_one, one_mul,
        show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    have hnorm : Summable fun d : ℤ => ‖(((s : ℂ) + (d : ℂ)) ^ 2)⁻¹‖ :=
      summable_norm_iff.mpr hC
    apply hnorm.congr
    intro d
    have hcast : ((s : ℂ) + (d : ℂ)) = (((s + (d : ℝ)) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    simp only [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    rw [sq_abs, one_div, add_comm s (d : ℝ)]
  · -- a pole: some term is 1/0 = ∞-free junk; the family is still summable?
    -- No: if (n₀ : ℝ) + s = 0 then s = -n₀ and the terms are 1/(n - n₀)²,
    -- with the n₀ term equal to 1/0 = 0 (division by zero convention).
    push Not at hs
    obtain ⟨n₀, hn₀⟩ := hs
    have hsval : s = -(n₀ : ℝ) := by linarith
    subst hsval
    have : (fun n : ℤ => (1 : ℝ) / ((n : ℝ) + -(n₀ : ℝ)) ^ 2)
        = fun n : ℤ => (1 : ℝ) / (((n - n₀ : ℤ) : ℝ)) ^ 2 := by
      funext n; push_cast; ring_nf
    rw [this]
    have hbase : Summable fun n : ℤ => (1 : ℝ) / ((n : ℝ)) ^ 2 :=
      Real.summable_one_div_int_pow.mpr one_lt_two
    exact hbase.comp_injective (i := fun n : ℤ => n - n₀) fun a b hab => by
      simp only at hab; omega

/-- **Euler's cotangent-square identity** (Helfgott arXiv:1501.05438v2, §2.3,
eq. (2.4)): for real non-integer `s`,
`∑' n : ℤ, 1/((n : ℝ) + s)^2 = π^2 / sin(s*π)^2`. -/
theorem tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq (s : ℝ)
    (hs : ∀ n : ℤ, (n : ℝ) + s ≠ 0) :
    (∑' n : ℤ, (1 : ℝ) / ((n : ℝ) + s) ^ 2)
      = Real.pi ^ 2 / (Real.sin (s * Real.pi)) ^ 2 := by
  have hf : Summable fun n : ℤ => (1 : ℝ) / ((n : ℝ) + s) ^ 2 :=
    summable_one_div_int_add_sq
  have h1 : Summable fun n : ℕ => (1 : ℝ) / (((n : ℤ) : ℝ) + s) ^ 2 :=
    hf.comp_injective Nat.cast_injective
  have h2 : Summable fun n : ℕ => (1 : ℝ) / (((-((n : ℤ) + 1) : ℤ) : ℝ) + s) ^ 2 :=
    hf.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1)) fun a b hab => by
      simp only at hab; omega
  have h1' : Summable fun n : ℕ => (1 : ℝ) / ((((n : ℤ) + 1 : ℤ) : ℝ) + s) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr h1
    apply this.congr
    intro n
    push_cast
    ring_nf
  -- split the ℤ-sum
  rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ => (1 : ℝ) / ((n : ℝ) + s) ^ 2) h1 h2,
    h1.tsum_eq_zero_add]
  have hsplit : (∑' n : ℕ, (1 : ℝ) / ((((n : ℤ) + 1 : ℤ) : ℝ) + s) ^ 2)
        + ∑' n : ℕ, (1 : ℝ) / (((-((n : ℤ) + 1) : ℤ) : ℝ) + s) ^ 2
      = ∑' n : ℕ, (1 / (s - ((n : ℝ) + 1)) ^ 2 + 1 / (s + ((n : ℝ) + 1)) ^ 2) := by
    rw [← h1'.tsum_add h2]
    apply tsum_congr
    intro n
    push_cast
    rw [add_comm]
    congr 2
    · ring
    · ring
  have hzero : (1 : ℝ) / ((((0 : ℕ) : ℤ) : ℝ) + s) ^ 2 = 1 / s ^ 2 := by norm_num
  have hshift : (∑' n : ℕ, (1 : ℝ) / ((((n + 1 : ℕ) : ℤ) : ℝ) + s) ^ 2)
      = ∑' n : ℕ, (1 : ℝ) / ((((n : ℤ) + 1 : ℤ) : ℝ) + s) ^ 2 := by
    apply tsum_congr
    intro n
    push_cast
    ring_nf
  rw [hzero, hshift, add_assoc, hsplit, ← real_pi_sq_div_sin_sq hs, mul_comm]

end CotangentSquareSum
end MathExtras
