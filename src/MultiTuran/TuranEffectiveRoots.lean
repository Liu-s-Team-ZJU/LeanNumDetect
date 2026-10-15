import MultiTuran.TuranLogPotential
import Mathlib.MeasureTheory.Order.Lattice

/-! Actual finite root potentials and their geometric-mean bound. The maximum
runs over all subsets of at most the effective degree, so no measurable
selection of nearest roots is assumed. -/

set_option autoImplicit false
open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran
noncomputable section

private def rootSelections (N d : ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.filter (fun s => s.card ≤ d)

private theorem rootSelections_nonempty (N d : ℕ) : (rootSelections N d).Nonempty := by
  exact ⟨∅, by simp [rootSelections]⟩

/-- The sum of the largest `d` truncated negative logarithms of root distances.
This definition also handles fewer than `d` roots and repeated complex roots. -/
def effectiveLogPotential {N : ℕ} (d : ℕ) (z : Fin N → ℂ) : ℝ → ℝ :=
  (rootSelections N d).sup' (rootSelections_nonempty N d)
    (fun s x => ∑ j ∈ s, max 0 (-Real.log ‖(x : ℂ)-z j‖))

theorem measurable_effectiveLogPotential {N : ℕ} (d : ℕ) (z : Fin N → ℂ) :
    Measurable (effectiveLogPotential d z) := by
  apply Finset.measurable_sup'
  intro s _
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.max ((Complex.continuous_ofReal.sub continuous_const).norm.measurable.log.neg)

theorem effectiveLogPotential_nonneg {N : ℕ} (d : ℕ) (z : Fin N → ℂ) (x : ℝ) :
    0 ≤ effectiveLogPotential d z x := by
  unfold effectiveLogPotential
  rw [Finset.sup'_apply]
  have h := Finset.le_sup' (fun s : Finset (Fin N) =>
    ∑ j ∈ s, max 0 (-Real.log ‖(x : ℂ)-z j‖))
    (show ∅ ∈ rootSelections N d by simp [rootSelections])
  simpa using h

/-- Every choice of at most `d` roots is bounded by the effective potential. -/
theorem selected_logPotential_le_effective {N : ℕ} (d : ℕ) (z : Fin N → ℂ)
    (s : Finset (Fin N)) (hs : s.card ≤ d) (x : ℝ) :
    (∑ j ∈ s, max 0 (-Real.log ‖(x : ℂ)-z j‖)) ≤ effectiveLogPotential d z x := by
  unfold effectiveLogPotential
  rw [Finset.sup'_apply]
  exact Finset.le_sup' (fun s : Finset (Fin N) =>
    ∑ j ∈ s, max 0 (-Real.log ‖(x : ℂ)-z j‖)) (show s ∈ rootSelections N d from
    Finset.mem_filter.mpr ⟨Finset.mem_univ s,hs⟩)

/-- Splitting at the distance `r` separates the effective degree from the
number of available roots. -/
theorem effectiveLogPotential_le {N : ℕ} (d : ℕ) (z : Fin N → ℂ)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (x : ℝ) :
    effectiveLogPotential d z x ≤
      (d : ℝ)*(-Real.log r) + ∑ j, positiveLogPotential r (z j) x := by
  unfold effectiveLogPotential
  rw [Finset.sup'_apply]
  apply Finset.sup'_le
  intro s hs
  exact selected_logPotential_le z s (Finset.mem_filter.mp hs).2 hr hr1 x

/-- The finite effective potential is genuinely integrable on the whole line. -/
theorem integrable_effectiveLogPotential {N : ℕ} (d : ℕ) (z : Fin N → ℂ) :
    Integrable (effectiveLogPotential d z) := by
  have hi : Integrable (fun x : ℝ => ∑ j, positiveLogPotential 1 (z j) x) :=
    integrable_finsetSum _ (fun j _ => integrable_positiveLogPotential (by norm_num) (z j))
  apply hi.mono_nonneg (measurable_effectiveLogPotential d z).aestronglyMeasurable
    (Filter.Eventually.of_forall (effectiveLogPotential_nonneg d z))
  apply Filter.Eventually.of_forall
  intro x
  simpa only [Real.log_one, neg_zero, mul_zero, zero_add] using
    effectiveLogPotential_le d z (by norm_num : (0 : ℝ) < 1) le_rfl x

/-- Integrating the threshold decomposition gives the exact basic estimate. -/
theorem integral_effectiveLogPotential_le_threshold {N : ℕ} (d : ℕ) (z : Fin N → ℂ)
    (E : Set ℝ) (hfinite : volume E ≠ ∞)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (∫ x in E, effectiveLogPotential d z x) ≤
      (volume E).toReal * ((d : ℝ)*(-Real.log r)) + 2*N*r := by
  have hisum : IntegrableOn (fun x : ℝ => ∑ j, positiveLogPotential r (z j) x) E :=
    integrable_finsetSum _ (fun j _ => (integrable_positiveLogPotential hr (z j)).integrableOn)
  have hic : IntegrableOn (fun _ : ℝ => (d : ℝ)*(-Real.log r)) E :=
    integrableOn_const hfinite
  have h := integral_mono_ae (integrable_effectiveLogPotential d z).integrableOn
    (hic.add hisum) (Filter.Eventually.of_forall (effectiveLogPotential_le d z hr hr1))
  change (∫ x in E, effectiveLogPotential d z x) ≤
    ∫ x in E, (d : ℝ)*(-Real.log r)+(∑ j, positiveLogPotential r (z j) x) at h
  rw [integral_add hic hisum, setIntegral_const, smul_eq_mul, measureReal_def] at h
  exact h.trans (add_le_add le_rfl (integral_sum_positiveLogPotential_le z hr E))

/-- An arbitrary positive-measure set controls the effective root potential
with the sharp algebraic exponent `d`. The root-count loss is merely `2N`. -/
theorem integral_effectiveLogPotential_le_of_degree_le {N d : ℕ} (z : Fin N → ℂ)
    (hd : 0 < d) (hdN : d ≤ N) (E : Set ℝ)
    (hE : 0 < (volume E).toReal) (hE1 : (volume E).toReal ≤ 1) :
    (∫ x in E, effectiveLogPotential d z x) ≤
      (volume E).toReal * (2*N+(d : ℝ)*Real.log (1/(volume E).toReal)) := by
  let α := (volume E).toReal
  have hα : 0 < α := hE
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (0 : ℝ) < N := lt_of_lt_of_le hdR (by exact_mod_cast hdN)
  have hdNR : (d : ℝ) ≤ N := by exact_mod_cast hdN
  let r : ℝ := (d : ℝ)*α/(2*N)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < 2*N)).mpr
    have hmul := mul_le_mul_of_nonneg_left hE1 hdR.le
    dsimp [r,α]
    nlinarith
  have hfinite : volume E ≠ ∞ := by
    intro h
    simp only [h,ENNReal.toReal_top,lt_self_iff_false] at hE
  have h := integral_effectiveLogPotential_le_threshold d z E hfinite hr hr1
  have hlogr : -Real.log r = Real.log (1/α)+Real.log ((2*(N : ℝ))/(d : ℝ)) := by
    dsimp [r]
    rw [Real.log_div (mul_ne_zero hdR.ne' hα.ne') (by positivity),
      Real.log_mul hdR.ne' hα.ne', Real.log_div one_ne_zero hα.ne',
      Real.log_div (by positivity) hdR.ne',Real.log_one]
    ring
  have hlog : (d : ℝ)*Real.log ((2*(N : ℝ))/(d : ℝ)) ≤ 2*N-d := by
    have hq := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0:ℝ)<2*N) hdR)
    have hq' := mul_le_mul_of_nonneg_left hq hdR.le
    have he : (d : ℝ)*(2*N/d-1) = 2*N-d := by field_simp
    rwa [he] at hq'
  have hwidth : 2*(N : ℝ)*r=(d : ℝ)*α := by dsimp [r]; field_simp
  rw [hlogr,hwidth] at h
  have hm := mul_le_mul_of_nonneg_left hlog hα.le
  dsimp only [α] at *
  nlinarith

theorem effectiveLogPotential_eq_min {N : ℕ} (d : ℕ) (z : Fin N → ℂ) :
    effectiveLogPotential d z = effectiveLogPotential (min d N) z := by
  have hsel : rootSelections N d = rootSelections N (min d N) := by
    ext s
    simp only [rootSelections,Finset.mem_filter,Finset.mem_univ,true_and]
    have hcard : s.card ≤ N := by simpa using Finset.card_le_univ s
    exact ⟨fun hs => le_min hs hcard, fun hs => hs.trans (min_le_left _ _)⟩
  simp only [effectiveLogPotential,hsel]

theorem effectiveLogPotential_zero {N : ℕ} (z : Fin N → ℂ) :
    effectiveLogPotential 0 z = 0 := by
  funext x
  apply le_antisymm _ (effectiveLogPotential_nonneg 0 z x)
  unfold effectiveLogPotential
  rw [Finset.sup'_apply]
  apply Finset.sup'_le
  intro s hs
  have hcard : s.card=0 := Nat.eq_zero_of_le_zero (Finset.mem_filter.mp hs).2
  rw [Finset.card_eq_zero.mp hcard]
  simp

/-- The geometric-mean root estimate for every effective degree, including
zero roots, repeated roots and a degree larger than the number of roots. -/
theorem integral_effectiveLogPotential_le {N : ℕ} (d : ℕ) (z : Fin N → ℂ)
    (E : Set ℝ) (hE : 0 < (volume E).toReal) (hE1 : (volume E).toReal ≤ 1) :
    (∫ x in E, effectiveLogPotential d z x) ≤
      (volume E).toReal * (2*N+(d : ℝ)*Real.log (1/(volume E).toReal)) := by
  have hlog : 0 ≤ Real.log (1/(volume E).toReal) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hE).mpr
    simpa only [one_mul] using hE1
  rw [effectiveLogPotential_eq_min d z]
  by_cases hzero : min d N=0
  · rw [hzero,effectiveLogPotential_zero]
    simp only [Pi.zero_apply,integral_zero]
    positivity
  · have hpos : 0 < min d N := Nat.pos_of_ne_zero hzero
    have h := integral_effectiveLogPotential_le_of_degree_le z hpos (min_le_right _ _) E hE hE1
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hE.le
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_left d N) hlog)

/-- The exponential of the negative potential bounds every truncated
root product outside its actual zero set. -/
theorem exp_neg_effectiveLogPotential_le_product {N : ℕ} (d : ℕ) (z : Fin N → ℂ)
    (s : Finset (Fin N)) (hs : s.card ≤ d) (x : ℝ)
    (hroot : ∀ j ∈ s, (x : ℂ) ≠ z j) :
    Real.exp (-effectiveLogPotential d z x) ≤
      ∏ j ∈ s, min 1 ‖(x : ℂ)-z j‖ := by
  have hprod : Real.exp (-(∑ j ∈ s, max 0 (-Real.log ‖(x : ℂ)-z j‖))) =
      ∏ j ∈ s, min 1 ‖(x : ℂ)-z j‖ := by
    calc
      _ = Real.exp (∑ j ∈ s, -max 0 (-Real.log ‖(x : ℂ)-z j‖)) := by
        congr 1
        simp
      _ = ∏ j ∈ s, Real.exp (-max 0 (-Real.log ‖(x : ℂ)-z j‖)) := Real.exp_sum _ _
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j hj
        have hp : 0 < ‖(x : ℂ)-z j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hroot j hj))
        by_cases hle : ‖(x : ℂ)-z j‖ ≤ 1
        · rw [max_eq_right (neg_nonneg.mpr (Real.log_nonpos hp.le hle)),
            neg_neg,Real.exp_log hp,min_eq_right hle]
        · have hge := le_of_not_ge hle
          rw [max_eq_left (neg_nonpos.mpr (Real.log_nonneg hge)),
            neg_zero,Real.exp_zero,min_eq_left hge]
  exact (Real.exp_le_exp.mpr (neg_le_neg (selected_logPotential_le_effective d z s hs x))).trans_eq hprod

/-- Simultaneously avoiding all real roots is a full-measure condition. -/
theorem ae_ne_root_centres {N : ℕ} (z : Fin N → ℂ) :
    ∀ᵐ x : ℝ, ∀ j, (x : ℂ) ≠ z j := by
  have h : ∀ j, ∀ᵐ x : ℝ, x ≠ (z j).re := fun j => volume.ae_ne ((z j).re)
  rw [← Filter.eventually_all] at h
  filter_upwards [h] with x hx j
  intro heq
  exact hx j (by simpa only [Complex.ofReal_re] using congrArg Complex.re heq)

end
end LeanNumDetect.MultiTuran
