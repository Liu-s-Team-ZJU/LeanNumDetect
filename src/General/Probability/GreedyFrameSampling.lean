import General.Probability.GreedyCyclePotential
import General.Probability.FiniteLaplace
import General.Probability.MatrixChernoff

/-!
The finite matrix Laplace step for greedy frame sampling. An iid moment
obtained from the scalar greedy-cycle potential transfers to uniform subsets
through the fully proved convex-order comparison. The retained energy is
fixed; no relative-deviation parameter occurs in the sampling requirement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
open LeanNumDetect.TraceExponential

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section

def greedyLaplaceParameter (n : ℕ) (η : ℝ) : ℝ :=
  Real.log (4 * (n : ℝ) + 1) / η

def greedySamplingThreshold (n : ℕ) (η : ℝ) : ℝ :=
  η / (15 * (n : ℝ) * Real.log (4 * (n : ℝ) + 1))

theorem greedyLaplaceParameter_pos {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    0 < greedyLaplaceParameter n η := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (Real.log_pos (by linarith)) hη

theorem greedySamplingThreshold_pos {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    0 < greedySamplingThreshold n η := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold greedySamplingThreshold
  exact div_pos hη (mul_pos (by positivity) (Real.log_pos (by linarith)))

theorem greedyLaplaceParameter_mul_threshold {n : ℕ} (hn : 0 < n)
    {η : ℝ} (hη : 0 < η) :
    greedyLaplaceParameter n η * greedySamplingThreshold n η = 1 / (15 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (4 * (n : ℝ) + 1) := Real.log_pos (by linarith)
  unfold greedyLaplaceParameter greedySamplingThreshold
  field_simp

theorem exp_neg_greedyLaplaceParameter_mul {n : ℕ} {η : ℝ} (hη : 0 < η) :
    Real.exp (-greedyLaplaceParameter n η * η) = greedyCycleRatio n := by
  have hden : 0 < 4 * (n : ℝ) + 1 := by positivity
  have he : -greedyLaplaceParameter n η * η = -Real.log (4 * (n : ℝ) + 1) := by
    unfold greedyLaplaceParameter
    field_simp
  rw [he, Real.exp_neg, Real.exp_log hden]
  simp [greedyCycleRatio]

/-- The spectral residual-rank factor is exactly the scalar cycle potential. -/
theorem greedy_spectral_factor_eq_potential {n J r : ℕ} {η : ℝ} (hη : 0 < η) :
    Real.exp (-greedyLaplaceParameter n η * (J : ℝ) * η) *
      ((n : ℝ) - r + r * Real.exp (-greedyLaplaceParameter n η * η)) =
        (n : ℝ) * greedyCyclePotential n J r := by
  have hq := exp_neg_greedyLaplaceParameter_mul (n := n) hη
  have he : Real.exp (-greedyLaplaceParameter n η * (J : ℝ) * η) =
      greedyCycleRatio n ^ J := by
    calc
      _ = Real.exp ((J : ℝ) * (-greedyLaplaceParameter n η * η)) := by congr 1; ring
      _ = Real.exp (-greedyLaplaceParameter n η * η) ^ J := Real.exp_nat_mul _ _
      _ = _ := by rw [hq]
  rw [he, hq]
  unfold greedyCyclePotential greedyCycleRatio
  have hd : (n : ℝ) + 1 / 4 ≠ 0 := by positivity
  have hd' : 4 * (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem greedyCycleDecay_pow_le {n : ℕ} (hn : 0 < n) (m : ℕ) :
    greedyCycleDecay n ^ m ≤ Real.exp (-2 * (m : ℝ) / (5 * n)) := by
  have hc : greedyCycleDecay n ≤ Real.exp (-2 / (5 * (n : ℝ))) := by
    unfold greedyCycleDecay
    calc
      _ = -2 / (5 * (n : ℝ)) + 1 := by ring
      _ ≤ _ := Real.add_one_le_exp _
  have hp := pow_le_pow_left₀ (greedyCycleDecay_nonneg hn) hc m
  rw [← Real.exp_nat_mul] at hp
  calc
    _ ≤ Real.exp ((m : ℝ) * (-2 / (5 * (n : ℝ)))) := hp
    _ = _ := by congr 1; ring

/-- A pointwise trace bound and the scalar potential iteration give the iid
matrix moment. This interface accepts arbitrary deterministic state types. -/
theorem traceExp_iid_sum_le_of_greedyPotential {κ S : Type*}
    [Fintype κ] [Nonempty κ] {n m : ℕ}
    (hn : 0 < n) (X : κ → Matrix (Fin n) (Fin n) ℂ)
    (next : S → κ → S) (g : S → ℝ) (s : S) {t : ℝ}
    (hstep : ∀ a, finiteAverage (fun k => g (next a k)) ≤ greedyCycleDecay n * g a)
    (hinitial : g s = 1)
    (htrace : ∀ ω : Fin m → κ,
      traceExp ((-t) • ∑ i, X (ω i)) ≤ (n : ℝ) * g (greedyRun next m ω s)) :
    finiteAverage (fun ω : Fin m → κ => traceExp ((-t) • ∑ i, X (ω i))) ≤
      (n : ℝ) * greedyCycleDecay n ^ m := by
  calc
    _ ≤ finiteAverage (fun ω : Fin m → κ => (n : ℝ) * g (greedyRun next m ω s)) :=
      finiteAverage_mono htrace
    _ = (n : ℝ) * finiteAverage (fun ω : Fin m → κ => g (greedyRun next m ω s)) :=
      finiteAverage_smul (n : ℝ) _
    _ ≤ (n : ℝ) * (greedyCycleDecay n ^ m * g s) :=
      mul_le_mul_of_nonneg_left
        (finiteAverage_greedyRun_le next g (greedyCycleDecay_nonneg hn) hstep m s)
        (Nat.cast_nonneg n)
    _ = _ := by rw [hinitial, mul_one]

/-- Trace-exponential convexity transfers any iid moment bound to uniform
sampling without replacement, including multiplicities in the population. -/
theorem sampleSum_traceExp_le_of_iid {N n m : ℕ} (hmN : m ≤ N)
    (X : Fin N → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ k, (X k).IsHermitian) (t : ℝ) {b : ℝ}
    (hiid : finiteAverage (fun ω : Fin m → Fin N =>
      traceExp ((-t) • ∑ i, X (ω i))) ≤ b) :
    finiteAverage (fun Ω : Sample N m => traceExp ((-t) • sampleSum X Ω)) ≤ b := by
  let Y : Fin N → selfAdjoint (Matrix (Fin n) (Fin n) ℂ) := fun k =>
    ⟨(-t) • X k, (hX k).smul (isSelfAdjoint_iff.mpr (star_trivial (-t)))⟩
  have h := sampling_withoutReplacement_convex_le hmN Y convexOn_traceExp
  have hsubset (Ω : Sample N m) :
      (∑ k ∈ Ω.val, Y k).val = (-t) • sampleSum X Ω := by
    simp [Y, sampleSum, Finset.smul_sum]
  have htuple (ω : Fin m → Fin N) :
      (∑ i, Y (ω i)).val = (-t) • ∑ i, X (ω i) := by
    simp [Y, Finset.smul_sum]
  simp only [hsubset, htuple] at h
  exact h.trans hiid

/-- A greedy iid moment yields a dimension-only lower tail for a uniform
subset sum. The threshold is the explicit constant used in the manuscript. -/
theorem sampleSum_greedy_lower_tail {N n m : ℕ}
    (hn : 0 < n) (hmN : m ≤ N)
    (X : Fin N → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ k, (X k).PosSemidef) {η : ℝ} (hη : 0 < η)
    (hiid : finiteAverage (fun ω : Fin m → Fin N =>
      traceExp ((-greedyLaplaceParameter n η) • ∑ i, X (ω i))) ≤
      (n : ℝ) * greedyCycleDecay n ^ m) :
    probability (fun Ω : Sample N m => ∃ x : EuclideanSpace ℂ (Fin n),
      ‖x‖ = 1 ∧ quadratic (sampleSum X Ω) x ≤
        (m : ℝ) * greedySamplingThreshold n η) ≤
      (n : ℝ) * Real.exp (-(m : ℝ) / (3 * n)) := by
  let t := greedyLaplaceParameter n η
  let κ := greedySamplingThreshold n η
  have ht : 0 < t := greedyLaplaceParameter_pos hn hη
  have hmoment : finiteAverage (fun Ω : Sample N m => traceExp ((-t) • sampleSum X Ω)) ≤
      (n : ℝ) * Real.exp (-2 * (m : ℝ) / (5 * n)) := by
    apply (sampleSum_traceExp_le_of_iid hmN X (fun k => (hX k).isHermitian) t hiid).trans
    exact mul_le_mul_of_nonneg_left (greedyCycleDecay_pow_le hn m) (Nat.cast_nonneg n)
  have h := probability_le_exponential_moment
    (fun Ω : Sample N m => ∃ x : EuclideanSpace ℂ (Fin n),
      ‖x‖ = 1 ∧ quadratic (sampleSum X Ω) x ≤ (m : ℝ) * κ)
    (fun Ω => traceExp ((-t) • sampleSum X Ω))
    (q := -t * ((m : ℝ) * κ)) (b := -2 * (m : ℝ) / (5 * n)) (D := n)
    (fun Ω => traceExp_nonneg
      ((sampleSum_isHermitian X (fun k => (hX k).isHermitian) Ω).smul
        (isSelfAdjoint_iff.mpr (star_trivial (-t)))))
    (by
      intro Ω hΩ
      obtain ⟨x, hx, hq⟩ := hΩ
      calc
        _ ≤ Real.exp (quadratic ((-t) • sampleSum X Ω) x) := by
          rw [TraceExponential.quadratic_real_smul]
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left hq (by linarith)
        _ ≤ _ := exp_quadratic_le_traceExp
          ((sampleSum_isHermitian X (fun k => (hX k).isHermitian) Ω).smul
            (isSelfAdjoint_iff.mpr (star_trivial (-t)))) x hx)
    hmoment
  have htk : t * κ = 1 / (15 * n) := greedyLaplaceParameter_mul_threshold hn hη
  have he : -2 * (m : ℝ) / (5 * n) - (-t * ((m : ℝ) * κ)) =
      -(m : ℝ) / (3 * n) := by
    calc
      _ = -2 * (m : ℝ) / (5 * n) + (m : ℝ) * (t * κ) := by ring
      _ = _ := by rw [htk]; ring
  simpa only [he] using h

/-- The lower-tail event gives the homogeneous quadratic lower bound on the
sample mean. The normalization argument includes every nonzero vector. -/
theorem sampleMean_greedy_lower_bound_probability {N n m : ℕ}
    (hn : 0 < n) (hm : 1 ≤ m) (hmN : m ≤ N)
    (X : Fin N → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ k, (X k).PosSemidef) {η : ℝ} (hη : 0 < η)
    (hiid : finiteAverage (fun ω : Fin m → Fin N =>
      traceExp ((-greedyLaplaceParameter n η) • ∑ i, X (ω i))) ≤
      (n : ℝ) * greedyCycleDecay n ^ m) :
    1 - (n : ℝ) * Real.exp (-(m : ℝ) / (3 * n)) ≤
      probability (fun Ω : Sample N m => ∀ x : EuclideanSpace ℂ (Fin n),
        greedySamplingThreshold n η * ‖x‖ ^ 2 ≤ quadratic (sampleMean X Ω) x) := by
  classical
  letI : Nonempty (Sample N m) := sample_nonempty hmN
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let κ := greedySamplingThreshold n η
  let L : Sample N m → Prop := fun Ω => ∃ x : EuclideanSpace ℂ (Fin n),
    ‖x‖ = 1 ∧ quadratic (sampleSum X Ω) x ≤ (m : ℝ) * κ
  have hL := sampleSum_greedy_lower_tail hn hmN X hX hη hiid
  have hgood := probability_mono (P := fun Ω : Sample N m => ¬ L Ω)
    (Q := fun Ω : Sample N m => ∀ x : EuclideanSpace ℂ (Fin n),
      κ * ‖x‖ ^ 2 ≤ quadratic (sampleMean X Ω) x) (by
    intro Ω hΩ x
    by_cases hx : x = 0
    · simp [hx]
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y := (‖x‖⁻¹ : ℂ) • x
    have hy : ‖y‖ = 1 := norm_smul_inv_norm hx
    have hlow : (m : ℝ) * κ < quadratic (sampleSum X Ω) y :=
      lt_of_not_ge (fun hq => hΩ ⟨y, hy, hq⟩)
    have hmean : quadratic (sampleMean X Ω) x =
        (m : ℝ)⁻¹ * quadratic (sampleSum X Ω) x := by
      simpa only [sampleMean, Complex.ofReal_inv, Complex.ofReal_natCast] using
        quadratic_smul_matrix (sampleSum X Ω) (m : ℝ)⁻¹ x
    have hyq : quadratic (sampleSum X Ω) y =
        ‖x‖⁻¹ ^ 2 * quadratic (sampleSum X Ω) x := by
      simpa only [y, ← Complex.ofReal_inv] using
        quadratic_real_smul (sampleSum X Ω) ‖x‖⁻¹ x
    rw [hyq] at hlow
    have hmul := mul_le_mul_of_nonneg_right hlow.le (sq_nonneg ‖x‖)
    have hcancel : (‖x‖⁻¹ ^ 2 * quadratic (sampleSum X Ω) x) * ‖x‖ ^ 2 =
        quadratic (sampleSum X Ω) x := by field_simp
    rw [hcancel] at hmul
    rw [hmean, mul_comm (m : ℝ)⁻¹]
    apply (le_mul_inv_iff₀ hmpos).mpr
    nlinarith)
  rw [probability_not] at hgood
  change probability L ≤ _ at hL
  linarith

/-- The explicit sample budget reduces the exponential failure probability to
epsilon. This is the only use of the requested failure probability. -/
theorem greedy_failure_probability_le {n m : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε)
    (hsample : 3 * (n : ℝ) * Real.log ((n : ℝ) / ε) ≤ (m : ℝ)) :
    (n : ℝ) * Real.exp (-(m : ℝ) / (3 * n)) ≤ ε := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : Real.log ((n : ℝ) / ε) ≤ (m : ℝ) / (3 * n) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have he : Real.exp (-Real.log ((n : ℝ) / ε)) = ε / (n : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (div_pos hn' hε)]
    field_simp
  calc
    _ ≤ (n : ℝ) * Real.exp (-Real.log ((n : ℝ) / ε)) := by
      apply mul_le_mul_of_nonneg_left _ hn'.le
      apply Real.exp_le_exp.mpr
      simpa only [neg_div] using neg_le_neg hl
    _ = ε := by rw [he]; field_simp

theorem sampleMean_greedy_lower_bound_probability_of_sample_budget {N n m : ℕ}
    (hn : 0 < n) (hm : 1 ≤ m) (hmN : m ≤ N)
    (X : Fin N → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ k, (X k).PosSemidef) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hiid : finiteAverage (fun ω : Fin m → Fin N =>
      traceExp ((-greedyLaplaceParameter n η) • ∑ i, X (ω i))) ≤
      (n : ℝ) * greedyCycleDecay n ^ m)
    (hsample : 3 * (n : ℝ) * Real.log ((n : ℝ) / ε) ≤ (m : ℝ)) :
    1 - ε ≤ probability (fun Ω : Sample N m => ∀ x : EuclideanSpace ℂ (Fin n),
      greedySamplingThreshold n η * ‖x‖ ^ 2 ≤ quadratic (sampleMean X Ω) x) :=
  (sub_le_sub_left (greedy_failure_probability_le hn hε hsample) 1).trans
    (sampleMean_greedy_lower_bound_probability hn hm hmN X hX hη hiid)

end

end LeanNumDetect.FiniteMatrixSampling
