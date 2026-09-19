import NumDetectMain.Basic

/-! Finite-difference counterexamples for computational resolution lower bounds. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Half of the finite-difference separation used in the CRL lower bound. -/
def numberDetectionLowerSpacing (n : ℕ) (Ω σ mMin : ℝ) : ℝ :=
  Ω⁻¹ * (σ / mMin) ^ (1 / (2 * (n : ℝ) - 2))

/-- The explicit lower bound in manuscript equation `eq:crl-number-twosided`. -/
def numberDetectionCRLLowerBound (n : ℕ) (Ω σ mMin : ℝ) : ℝ :=
  2 / Ω * (σ / mMin) ^ (1 / (2 * (n : ℝ) - 2))

private def axisPoint {d : ℕ} (axis : Fin d) (x : ℝ) : Point d :=
  fun k => if k = axis then x else 0

@[simp]
private theorem axisPoint_apply_self {d : ℕ} (axis : Fin d) (x : ℝ) :
    axisPoint axis x axis = x := by
  simp [axisPoint]

private theorem axisPoint_injective {d : ℕ} (axis : Fin d) :
    Function.Injective (axisPoint axis) := by
  intro x y hxy
  simpa only [axisPoint_apply_self] using congrFun hxy axis

private theorem axisPoint_sub {d : ℕ} (axis : Fin d) (x y : ℝ) :
    axisPoint axis x - axisPoint axis y = axisPoint axis (x - y) := by
  funext k
  by_cases hk : k = axis <;> simp [axisPoint, hk]

private theorem l1Norm_axisPoint {d : ℕ} (axis : Fin d) (x : ℝ) :
    l1Norm (axisPoint axis x) = |x| := by
  unfold l1Norm axisPoint
  rw [Finset.sum_eq_single axis]
  · simp
  · intro k _ hka
    simp [hka]
  · simp

private theorem dot_axisPoint {d : ℕ} (axis : Fin d) (x : ℝ) (ω : Point d) :
    dot (axisPoint axis x) ω = x * ω axis := by
  unfold dot axisPoint
  rw [Finset.sum_eq_single axis]
  · simp
  · intro k _ hka
    simp [hka]
  · simp

private def evenDifferenceMeasure {d m : ℕ} (axis : Fin d) (τ mMin : ℝ)
    (hτ : 0 < τ) (hmMin : 0 < mMin) :
    AtomicMeasure d (m + 1) where
  amplitude j := (mMin * ((2 * m).choose (2 * j.val) : ℝ) : ℝ)
  node j := axisPoint axis (((2 * j.val : ℕ) : ℝ) * τ)
  amplitude_ne_zero j := by
    have hj : 2 * j.val ≤ 2 * m := by omega
    have hc : 0 < (2 * m).choose (2 * j.val) := Nat.choose_pos hj
    norm_cast
    exact mul_ne_zero hmMin.ne' (by exact_mod_cast hc.ne')
  node_injective := by
    intro i j hij
    apply Fin.ext
    apply Nat.cast_injective (R := ℝ)
    have hscalar := congrArg (fun x => x axis) hij
    simp only [axisPoint_apply_self] at hscalar
    have hcast : (i.val : ℝ) = j.val := by
      apply (mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num))
      apply (mul_right_cancel₀ hτ.ne')
      simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hscalar
    exact_mod_cast hcast

private def oddDifferenceMeasure {d m : ℕ} (axis : Fin d) (τ mMin : ℝ)
    (hτ : 0 < τ) (hmMin : 0 < mMin) :
    AtomicMeasure d m where
  amplitude j := (mMin * ((2 * m).choose (2 * j.val + 1) : ℝ) : ℝ)
  node j := axisPoint axis ((((2 * j.val + 1 : ℕ) : ℝ)) * τ)
  amplitude_ne_zero j := by
    have hj : 2 * j.val + 1 ≤ 2 * m := by omega
    have hc : 0 < (2 * m).choose (2 * j.val + 1) := Nat.choose_pos hj
    norm_cast
    exact mul_ne_zero hmMin.ne' (by exact_mod_cast hc.ne')
  node_injective := by
    intro i j hij
    apply Fin.ext
    apply Nat.cast_injective (R := ℝ)
    have hscalar := congrArg (fun x => x axis) hij
    simp only [axisPoint_apply_self] at hscalar
    have hcast : ((2 * i.val + 1 : ℕ) : ℝ) = (2 * j.val + 1 : ℕ) :=
      mul_right_cancel₀ hτ.ne' hscalar
    have hnat : 2 * i.val + 1 = 2 * j.val + 1 := by
      exact_mod_cast hcast
    have hval : i.val = j.val := by omega
    exact_mod_cast hval

private theorem sum_range_even_odd (m : ℕ) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.range (2 * m + 1), f k) =
      (∑ j ∈ Finset.range (m + 1), f (2 * j)) +
        ∑ j ∈ Finset.range m, f (2 * j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [ih]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Nat.mul_succ, Nat.succ_mul]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      ring

private theorem even_odd_binomial (m : ℕ) (z : ℂ) :
    (∑ j : Fin (m + 1), ((2 * m).choose (2 * j.val) : ℂ) * z ^ (2 * j.val)) -
        (∑ j : Fin m, ((2 * m).choose (2 * j.val + 1) : ℂ) *
          z ^ (2 * j.val + 1)) =
      (1 - z) ^ (2 * m) := by
  rw [Fin.sum_univ_eq_sum_range
      (fun j => ((2 * m).choose (2 * j) : ℂ) * z ^ (2 * j)) (m + 1)]
  rw [Fin.sum_univ_eq_sum_range
      (fun j => ((2 * m).choose (2 * j + 1) : ℂ) * z ^ (2 * j + 1)) m]
  have hsplit := sum_range_even_odd m
    (fun k => (-z) ^ k * ((2 * m).choose k : ℂ))
  have hbin := add_pow (-z) 1 (2 * m)
  simp only [one_pow, mul_one] at hbin
  rw [show -z + 1 = 1 - z by ring] at hbin
  rw [hbin, hsplit]
  have heven :
      (∑ j ∈ Finset.range (m + 1), (-z) ^ (2 * j) *
          ((2 * m).choose (2 * j) : ℂ)) =
        ∑ j ∈ Finset.range (m + 1),
          ((2 * m).choose (2 * j) : ℂ) * z ^ (2 * j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [neg_pow]
    simp [pow_mul]
    ring
  have hodd :
      (∑ j ∈ Finset.range m, (-z) ^ (2 * j + 1) *
          ((2 * m).choose (2 * j + 1) : ℂ)) =
        -(∑ j ∈ Finset.range m,
          ((2 * m).choose (2 * j + 1) : ℂ) * z ^ (2 * j + 1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [neg_pow]
    simp [pow_succ, pow_mul]
    ring
  rw [heven, hodd]
  ring

private theorem exp_axis_even {d m : ℕ} (axis : Fin d) (τ : ℝ)
    (ω : Point d) (j : Fin (m + 1)) :
    Complex.exp
        (Complex.I * (dot (axisPoint axis (((2 * j.val : ℕ) : ℝ) * τ)) ω : ℂ)) =
      Complex.exp (Complex.I * ((τ * ω axis : ℝ) : ℂ)) ^ (2 * j.val) := by
  rw [dot_axisPoint]
  rw [show Complex.I * (((((2 * j.val : ℕ) : ℝ) * τ) * ω axis : ℝ) : ℂ) =
      ((2 * j.val : ℕ) : ℂ) * (Complex.I * ((τ * ω axis : ℝ) : ℂ)) by
    push_cast
    ring]
  exact Complex.exp_nat_mul _ _

private theorem exp_axis_odd {d m : ℕ} (axis : Fin d) (τ : ℝ)
    (ω : Point d) (j : Fin m) :
    Complex.exp
        (Complex.I *
          (dot (axisPoint axis ((((2 * j.val + 1 : ℕ) : ℝ)) * τ)) ω : ℂ)) =
      Complex.exp (Complex.I * ((τ * ω axis : ℝ) : ℂ)) ^ (2 * j.val + 1) := by
  rw [dot_axisPoint]
  rw [show Complex.I * (((((2 * j.val + 1 : ℕ) : ℝ) * τ) * ω axis : ℝ) : ℂ) =
      ((2 * j.val + 1 : ℕ) : ℂ) * (Complex.I * ((τ * ω axis : ℝ) : ℂ)) by
    push_cast
    ring]
  exact Complex.exp_nat_mul _ _

private theorem fourier_even_sub_odd {d m : ℕ} (axis : Fin d) (τ mMin : ℝ)
    (hτ : 0 < τ) (hmMin : 0 < mMin)
    (ω : Point d) :
    fourier (evenDifferenceMeasure (m := m) axis τ mMin hτ hmMin) ω -
        fourier (oddDifferenceMeasure (m := m) axis τ mMin hτ hmMin) ω =
      (mMin : ℂ) *
        (1 - Complex.exp (Complex.I * ((τ * ω axis : ℝ) : ℂ))) ^ (2 * m) := by
  unfold fourier evenDifferenceMeasure oddDifferenceMeasure
  simp only [exp_axis_even, exp_axis_odd, Complex.ofReal_mul, Complex.ofReal_natCast]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub]
  congr 1
  exact even_odd_binomial m _

private theorem numberDetectionLowerSpacing_pos
    {n : ℕ} {Ω σ mMin : ℝ}
    (_hn : 2 ≤ n) (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin) :
    0 < numberDetectionLowerSpacing n Ω σ mMin := by
  have hmMin : 0 < mMin := hσ.trans hnoise
  unfold numberDetectionLowerSpacing
  positivity

private theorem numberDetectionLowerSpacing_lt_inv
    {n : ℕ} {Ω σ mMin : ℝ}
    (hn : 2 ≤ n) (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin) :
    numberDetectionLowerSpacing n Ω σ mMin < Ω⁻¹ := by
  have hmMin : 0 < mMin := hσ.trans hnoise
  have hratioPos : 0 < σ / mMin := div_pos hσ hmMin
  have hratioLt : σ / mMin < 1 := (div_lt_one hmMin).2 hnoise
  have hexponent : 0 < 1 / (2 * (n : ℝ) - 2) := by
    apply one_div_pos.mpr
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hroot :
      (σ / mMin) ^ (1 / (2 * (n : ℝ) - 2)) < 1 :=
    Real.rpow_lt_one hratioPos.le hratioLt hexponent
  unfold numberDetectionLowerSpacing
  simpa only [mul_one] using mul_lt_mul_of_pos_left hroot (inv_pos.mpr hΩ)

private theorem numberDetectionLowerSpacing_band_power
    {n : ℕ} {Ω σ mMin : ℝ}
    (hn : 2 ≤ n) (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin) :
    (numberDetectionLowerSpacing n Ω σ mMin * Ω) ^ (2 * (n - 1)) =
      σ / mMin := by
  have hmMin : 0 < mMin := hσ.trans hnoise
  have hratio : 0 ≤ σ / mMin := (div_pos hσ hmMin).le
  have hexponent : 2 * (n - 1) ≠ 0 := by omega
  have hexponentCast :
      ((2 * (n - 1) : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  unfold numberDetectionLowerSpacing
  have hcancel :
      Ω⁻¹ * (σ / mMin) ^ (1 / (2 * (n : ℝ) - 2)) * Ω =
        (σ / mMin) ^ (1 / (2 * (n : ℝ) - 2)) := by
    field_simp
  rw [hcancel]
  rw [show 1 / (2 * (n : ℝ) - 2) =
      (((2 * (n - 1) : ℕ) : ℝ))⁻¹ by
    rw [hexponentCast]
    exact one_div _]
  exact Real.rpow_inv_natCast_pow hratio hexponent

private theorem evenDifferenceMeasure_positive {d m : ℕ}
    (axis : Fin d) (τ mMin : ℝ) (hτ : 0 < τ) (hmMin : 0 < mMin) :
    (evenDifferenceMeasure (m := m) axis τ mMin hτ hmMin).IsPositive := by
  intro j
  refine ⟨mMin * ((2 * m).choose (2 * j.val) : ℝ), ?_, rfl⟩
  have hj : 2 * j.val ≤ 2 * m := by omega
  exact mul_pos hmMin (by exact_mod_cast Nat.choose_pos hj)

private theorem oddDifferenceMeasure_positive {d m : ℕ}
    (axis : Fin d) (τ mMin : ℝ) (hτ : 0 < τ) (hmMin : 0 < mMin) :
    (oddDifferenceMeasure (m := m) axis τ mMin hτ hmMin).IsPositive := by
  intro j
  refine ⟨mMin * ((2 * m).choose (2 * j.val + 1) : ℝ), ?_, rfl⟩
  have hj : 2 * j.val + 1 ≤ 2 * m := by omega
  exact mul_pos hmMin (by exact_mod_cast Nat.choose_pos hj)

private theorem evenDifferenceMeasure_minAmplitude {d m : ℕ}
    (axis : Fin d) (τ mMin : ℝ) (hτ : 0 < τ) (hmMin : 0 < mMin) :
    minAmplitude (evenDifferenceMeasure (m := m) axis τ mMin hτ hmMin)
        (Nat.zero_lt_succ m) = mMin := by
  apply le_antisymm
  · calc
      minAmplitude (evenDifferenceMeasure (m := m) axis τ mMin hτ hmMin)
          (Nat.zero_lt_succ m) ≤
          ‖(evenDifferenceMeasure (m := m) axis τ mMin hτ hmMin).amplitude
            ⟨0, Nat.zero_lt_succ m⟩‖ :=
        Finset.inf'_le _ (Finset.mem_univ _)
      _ = mMin := by
        simp [evenDifferenceMeasure, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hmMin]
  · rw [minAmplitude]
    apply Finset.le_inf' (fin_univ_nonempty (Nat.zero_lt_succ m))
    intro j hj
    have hjle : 2 * j.val ≤ 2 * m := by omega
    have hchoose : (1 : ℝ) ≤ (2 * m).choose (2 * j.val) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.choose_ne_zero hjle))
    rw [show
      ‖(evenDifferenceMeasure (m := m) axis τ mMin hτ hmMin).amplitude j‖ =
        mMin * ((2 * m).choose (2 * j.val) : ℝ) by
      rw [evenDifferenceMeasure, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos hmMin (by exact_mod_cast Nat.choose_pos hjle))]]
    nlinarith

private theorem evenDifferenceMeasure_separated {d m : ℕ}
    (axis : Fin d) (τ mMin : ℝ) (hτ : 0 < τ) (hmMin : 0 < mMin) :
    ∀ i j, i ≠ j →
      2 * τ ≤
        l1Norm
          ((evenDifferenceMeasure (m := m) axis τ mMin hτ hmMin).node i -
            (evenDifferenceMeasure (m := m) axis τ mMin hτ hmMin).node j) := by
  intro i j hij
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have habs : (1 : ℝ) ≤ |(i.val : ℝ) - j.val| := by
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hcast : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hlt
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hcast : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hgt
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [evenDifferenceMeasure, axisPoint_sub, l1Norm_axisPoint]
  rw [show
      (((2 * i.val : ℕ) : ℝ) * τ - ((2 * j.val : ℕ) : ℝ) * τ) =
        2 * τ * ((i.val : ℝ) - j.val) by
    push_cast
    ring]
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * τ)]
  nlinarith

private theorem evenDifferenceMeasure_clustered {d m : ℕ}
    (axis : Fin d) {Ω σ mMin : ℝ}
    (hm : 1 ≤ m) (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin) :
    ∀ j,
      InOpenL1Ball (Real.pi * (m + 1) / Ω) 0
        ((evenDifferenceMeasure (m := m) axis
          (numberDetectionLowerSpacing (m + 1) Ω σ mMin) mMin
          (numberDetectionLowerSpacing_pos (by omega) hΩ hσ hnoise)
          (hσ.trans hnoise)).node j) := by
  intro j
  have hτ := numberDetectionLowerSpacing_pos (n := m + 1) (by omega) hΩ hσ hnoise
  have hτlt := numberDetectionLowerSpacing_lt_inv (n := m + 1)
    (by omega) hΩ hσ hnoise
  have hj : (j.val : ℝ) ≤ m := by
    exact_mod_cast (Nat.le_of_lt_succ j.isLt)
  have hnodeNonneg :
      0 ≤ ((2 * j.val : ℕ) : ℝ) *
        numberDetectionLowerSpacing (m + 1) Ω σ mMin := by positivity
  have hnodeBound :
      ((2 * j.val : ℕ) : ℝ) *
          numberDetectionLowerSpacing (m + 1) Ω σ mMin <
        2 * (m : ℝ) / Ω := by
    have hmPos : (0 : ℝ) < m := by exact_mod_cast hm
    calc
      ((2 * j.val : ℕ) : ℝ) *
          numberDetectionLowerSpacing (m + 1) Ω σ mMin ≤
          2 * (m : ℝ) * numberDetectionLowerSpacing (m + 1) Ω σ mMin := by
            push_cast
            gcongr
      _ < 2 * (m : ℝ) * Ω⁻¹ := by
        exact mul_lt_mul_of_pos_left hτlt (by positivity)
      _ = 2 * (m : ℝ) / Ω := by ring
  have hball :
      2 * (m : ℝ) / Ω < Real.pi * ((m + 1 : ℕ) : ℝ) / Ω := by
    apply (div_lt_div_iff_of_pos_right hΩ).2
    push_cast
    nlinarith [Real.pi_gt_three]
  unfold InOpenL1Ball
  rw [evenDifferenceMeasure]
  change l1Norm (axisPoint axis _ - 0) < _
  rw [sub_zero, l1Norm_axisPoint, abs_of_nonneg hnodeNonneg]
  simpa only [Nat.cast_add, Nat.cast_one] using hnodeBound.trans hball

private theorem norm_one_sub_exp_I_lt_abs {x : ℝ} (hx : x ≠ 0) :
    ‖1 - Complex.exp (Complex.I * (x : ℂ))‖ < |x| := by
  rw [norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hhalf : x / 2 ≠ 0 := div_ne_zero hx (by norm_num)
  have hsin := Real.abs_sin_lt_abs hhalf
  calc
    2 * |Real.sin (x / 2)| < 2 * |x / 2| := by linarith
    _ = |x| := by rw [abs_div]; norm_num; ring

private theorem fourier_odd_sub_even_norm_lt {d m : ℕ}
    (axis : Fin d) {Ω σ mMin : ℝ}
    (hm : 1 ≤ m) (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin)
    (ω : Point d) (hω : InFrequencyBand Ω ω) :
    ‖fourier
          (oddDifferenceMeasure (m := m) axis
            (numberDetectionLowerSpacing (m + 1) Ω σ mMin) mMin
            (numberDetectionLowerSpacing_pos (by omega) hΩ hσ hnoise)
            (hσ.trans hnoise)) ω -
        fourier
          (evenDifferenceMeasure (m := m) axis
            (numberDetectionLowerSpacing (m + 1) Ω σ mMin) mMin
            (numberDetectionLowerSpacing_pos (by omega) hΩ hσ hnoise)
            (hσ.trans hnoise)) ω‖ < σ := by
  let τ := numberDetectionLowerSpacing (m + 1) Ω σ mMin
  have hτ : 0 < τ :=
    numberDetectionLowerSpacing_pos (n := m + 1) (by omega) hΩ hσ hnoise
  have hmMin : 0 < mMin := hσ.trans hnoise
  have hexponent : 2 * m ≠ 0 := by omega
  have hcoordinate : |τ * ω axis| ≤ τ * Ω := by
    rw [abs_mul, abs_of_pos hτ]
    exact mul_le_mul_of_nonneg_left (hω axis) hτ.le
  have hpower :
      (τ * Ω) ^ (2 * m) = σ / mMin := by
    simpa only [Nat.add_sub_cancel] using
      numberDetectionLowerSpacing_band_power
        (n := m + 1) (by omega) hΩ hσ hnoise
  rw [norm_sub_rev]
  rw [fourier_even_sub_odd axis τ mMin hτ hmMin ω]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hmMin]
  by_cases hx : τ * ω axis = 0
  · simp [hx, hexponent, hσ]
  · calc
      mMin *
          ‖1 - Complex.exp (Complex.I * ((τ * ω axis : ℝ) : ℂ))‖ ^ (2 * m) <
          mMin * |τ * ω axis| ^ (2 * m) := by
            apply mul_lt_mul_of_pos_left _ hmMin
            exact pow_lt_pow_left₀
              (norm_one_sub_exp_I_lt_abs hx) (norm_nonneg _) hexponent
      _ ≤ mMin * (τ * Ω) ^ (2 * m) := by
            apply mul_le_mul_of_nonneg_left _ hmMin.le
            exact pow_le_pow_left₀ (abs_nonneg _) hcoordinate _
      _ = σ := by
            rw [hpower]
            field_simp

/-- Below the finite-difference spacing, number detection fails even for positive amplitudes. -/
theorem not_numberDetectionGuarantee_of_lt_lowerBound
    {d n : ℕ} {Ω σ mMin D : ℝ}
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin)
    (hD : D < numberDetectionCRLLowerBound n Ω σ mMin) :
    ¬NumberDetectionGuarantee d n (.finite 1 le_rfl) Ω σ mMin D
      (Nat.zero_lt_of_lt hn) := by
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  have hm : 1 ≤ m := by omega
  let axis : Fin d := ⟨0, hd⟩
  let τ := numberDetectionLowerSpacing (m + 1) Ω σ mMin
  have hτ : 0 < τ :=
    numberDetectionLowerSpacing_pos (n := m + 1) (by omega) hΩ hσ hnoise
  have hmMin : 0 < mMin := hσ.trans hnoise
  let μ : AtomicMeasure d (m + 1) :=
    evenDifferenceMeasure axis τ mMin hτ hmMin
  let ν : AtomicMeasure d m :=
    oddDifferenceMeasure axis τ mMin hτ hmMin
  have hlower :
      numberDetectionCRLLowerBound (m + 1) Ω σ mMin = 2 * τ := by
    unfold numberDetectionCRLLowerBound τ numberDetectionLowerSpacing
    field_simp
  intro hguarantee
  have hcard := hguarantee μ
    (by
      simpa only [μ] using
        evenDifferenceMeasure_minAmplitude axis τ mMin hτ hmMin)
    (by
      simpa only [μ, τ, Nat.cast_succ] using
        evenDifferenceMeasure_clustered axis hm hΩ hσ hnoise)
    (by
      intro i j hij
      have hseparated :=
        evenDifferenceMeasure_separated axis τ mMin hτ hmMin i j hij
      have hDtwo : D ≤ 2 * τ := (hD.trans_eq hlower).le
      simpa only [μ, normAt, lpNorm, one_div, inv_one, Real.rpow_one,
        l1Norm] using
        hDtwo.trans hseparated)
    (fourier μ)
    (by
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro ω hω
        simpa only [norm_zero] using hσ
      · intro ω hω
        simp)
    m ν
    (by
      intro ω hω
      simpa only [μ, ν, τ] using
        fourier_odd_sub_even_norm_lt axis hm hΩ hσ hnoise ω hω)
  omega

/-- The same finite-difference example invalidates the positive-amplitude guarantee. -/
theorem not_positiveNumberDetectionGuarantee_of_lt_lowerBound
    {d n : ℕ} {Ω σ mMin D : ℝ}
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hΩ : 0 < Ω) (hσ : 0 < σ) (hnoise : σ < mMin)
    (hD : D < numberDetectionCRLLowerBound n Ω σ mMin) :
    ¬PositiveNumberDetectionGuarantee d n (.finite 1 le_rfl) Ω σ mMin D
      (Nat.zero_lt_of_lt hn) := by
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  have hm : 1 ≤ m := by omega
  let axis : Fin d := ⟨0, hd⟩
  let τ := numberDetectionLowerSpacing (m + 1) Ω σ mMin
  have hτ : 0 < τ :=
    numberDetectionLowerSpacing_pos (n := m + 1) (by omega) hΩ hσ hnoise
  have hmMin : 0 < mMin := hσ.trans hnoise
  let μ : AtomicMeasure d (m + 1) :=
    evenDifferenceMeasure axis τ mMin hτ hmMin
  let ν : AtomicMeasure d m :=
    oddDifferenceMeasure axis τ mMin hτ hmMin
  have hlower :
      numberDetectionCRLLowerBound (m + 1) Ω σ mMin = 2 * τ := by
    unfold numberDetectionCRLLowerBound τ numberDetectionLowerSpacing
    field_simp
  intro hguarantee
  have hcard := hguarantee μ
    (by
      simpa only [μ] using
        evenDifferenceMeasure_positive axis τ mMin hτ hmMin)
    (by
      simpa only [μ] using
        evenDifferenceMeasure_minAmplitude axis τ mMin hτ hmMin)
    (by
      simpa only [μ, τ, Nat.cast_succ] using
        evenDifferenceMeasure_clustered axis hm hΩ hσ hnoise)
    (by
      intro i j hij
      have hseparated :=
        evenDifferenceMeasure_separated axis τ mMin hτ hmMin i j hij
      have hDtwo : D ≤ 2 * τ := (hD.trans_eq hlower).le
      simpa only [μ, normAt, lpNorm, one_div, inv_one, Real.rpow_one,
        l1Norm] using
        hDtwo.trans hseparated)
    (fourier μ)
    (by
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro ω hω
        simpa only [norm_zero] using hσ
      · intro ω hω
        simp)
    m ν
    ⟨by
      simpa only [ν] using oddDifferenceMeasure_positive axis τ mMin hτ hmMin,
      by
        intro ω hω
        simpa only [μ, ν, τ] using
          fourier_odd_sub_even_norm_lt axis hm hΩ hσ hnoise ω hω⟩
  omega

end

end NumDetect
end LeanNumDetect
