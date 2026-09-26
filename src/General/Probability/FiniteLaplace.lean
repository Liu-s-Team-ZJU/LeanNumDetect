import General.Probability.FiniteMatrixSampling
import General.Probability.FiniteAverage

/-!
Finite counting versions of Markov's inequality and the scalar optimization in
the matrix Laplace method. The test functions and their exponential-moment
bounds are explicit hypotheses; this file assumes no matrix concentration result.
-/

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

/-- Every event has finite counting probability at most one. -/
theorem probability_le_one {α : Type*} [Fintype α] [Nonempty α] (P : α → Prop) :
    probability P ≤ 1 := by
  classical
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold probability
  apply (div_le_iff₀ hc).2
  simp only [one_mul]
  exact_mod_cast Finset.card_le_card (Finset.filter_subset P Finset.univ)

/-- Markov's inequality for a nonnegative test function detecting an event. -/
theorem probability_le_finiteAverage_div {α : Type*} [Fintype α]
    (P : α → Prop) (f : α → ℝ) {c : ℝ} (hc : 0 < c)
    (hf : ∀ ω, 0 ≤ f ω) (hdetect : ∀ ω, P ω → c ≤ f ω) :
    probability P ≤ finiteAverage f / c := by
  classical
  have hsum : c * ((Finset.univ.filter P).card : ℝ) ≤ ∑ ω, f ω := by
    calc
      c * ((Finset.univ.filter P).card : ℝ) =
          ∑ ω ∈ Finset.univ.filter P, c := by simp [mul_comm]
      _ ≤ ∑ ω ∈ Finset.univ.filter P, f ω := by
        apply Finset.sum_le_sum
        intro ω hω
        exact hdetect ω (Finset.mem_filter.mp hω).2
      _ ≤ ∑ ω, f ω := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset P Finset.univ) (by intro ω _ _; exact hf ω)
  unfold probability finiteAverage
  simp only [smul_eq_mul]
  apply (le_div_iff₀ hc).2
  have h := mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card α) : (0 : ℝ) ≤ Fintype.card α))
  convert h using 1
  ring

/-- Finite Laplace bound from a nonnegative test function and its mean. -/
theorem probability_le_exponential_moment {α : Type*} [Fintype α]
    (P : α → Prop) (f : α → ℝ) {q b D : ℝ}
    (hf : ∀ ω, 0 ≤ f ω) (hdetect : ∀ ω, P ω → Real.exp q ≤ f ω)
    (hmoment : finiteAverage f ≤ D * Real.exp b) :
    probability P ≤ D * Real.exp (b - q) := by
  calc
    probability P ≤ finiteAverage f / Real.exp q :=
      probability_le_finiteAverage_div P f (Real.exp_pos _) hf hdetect
    _ ≤ (D * Real.exp b) / Real.exp q :=
      div_le_div_of_nonneg_right hmoment (Real.exp_pos _).le
    _ = D * Real.exp (b - q) := by rw [Real.exp_sub, mul_div_assoc]

/-- Optimizing the lower-tail exponential-moment bound gives the exact
Chernoff factor, including the endpoint `δ = 0`. -/
theorem lower_chernoff_of_finite_laplace {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) {D m R l δ : ℝ} (hD : 1 ≤ D) (hR : 0 < R)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (test : ℝ → α → ℝ)
    (htest : ∀ θ, 0 < θ → ∀ ω, 0 ≤ test θ ω)
    (hdetect : ∀ θ, 0 < θ → ∀ ω, P ω →
      Real.exp (-θ * ((1 - δ) * m * l)) ≤ test θ ω)
    (hmoment : ∀ θ, 0 < θ → finiteAverage (test θ) ≤
      D * Real.exp (m * (Real.exp (-θ * R) - 1) * l / R)) :
    probability P ≤ D *
      (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (m * l / R) := by
  by_cases hδ : δ = 0
  · subst δ
    simpa using (probability_le_one P).trans hD
  have hδpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδ)
  have hp : 0 < 1 - δ := sub_pos.mpr hδ1
  let θ := -Real.log (1 - δ) / R
  have hθ : 0 < θ := div_pos (neg_pos.mpr (Real.log_neg hp (by linarith))) hR
  have hθR : -θ * R = Real.log (1 - δ) := by
    dsimp [θ]
    field_simp
  have hexp : Real.exp (-θ * R) = 1 - δ := by rw [hθR, Real.exp_log hp]
  have hopt : Real.exp (m * (Real.exp (-θ * R) - 1) * l / R -
      (-θ * ((1 - δ) * m * l))) =
      (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (m * l / R) := by
    rw [hexp, Real.rpow_def_of_pos
      (div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hp _)),
      Real.log_div (Real.exp_ne_zero _) (ne_of_gt (Real.rpow_pos_of_pos hp _)),
      Real.log_exp, Real.log_rpow hp]
    congr 1
    dsimp [θ]
    ring
  simpa only [hopt] using probability_le_exponential_moment P (test θ)
    (htest θ hθ) (hdetect θ hθ) (hmoment θ hθ)

/-- Optimizing the upper-tail exponential-moment bound gives the exact
Chernoff factor for every `δ ≥ 0`, including `δ = 0`. -/
theorem upper_chernoff_of_finite_laplace {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) {D m R u δ : ℝ} (hD : 1 ≤ D) (hR : 0 < R)
    (hδ : 0 ≤ δ) (test : ℝ → α → ℝ)
    (htest : ∀ θ, 0 < θ → ∀ ω, 0 ≤ test θ ω)
    (hdetect : ∀ θ, 0 < θ → ∀ ω, P ω →
      Real.exp (θ * ((1 + δ) * m * u)) ≤ test θ ω)
    (hmoment : ∀ θ, 0 < θ → finiteAverage (test θ) ≤
      D * Real.exp (m * (Real.exp (θ * R) - 1) * u / R)) :
    probability P ≤ D *
      (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (m * u / R) := by
  by_cases hδzero : δ = 0
  · subst δ
    simpa using (probability_le_one P).trans hD
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδzero)
  have hp : 0 < 1 + δ := by positivity
  let θ := Real.log (1 + δ) / R
  have hθ : 0 < θ := div_pos (Real.log_pos (by linarith)) hR
  have hθR : θ * R = Real.log (1 + δ) := by
    dsimp [θ]
    field_simp
  have hexp : Real.exp (θ * R) = 1 + δ := by rw [hθR, Real.exp_log hp]
  have hopt : Real.exp (m * (Real.exp (θ * R) - 1) * u / R -
      θ * ((1 + δ) * m * u)) =
      (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (m * u / R) := by
    rw [hexp, Real.rpow_def_of_pos
      (div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hp _)),
      Real.log_div (Real.exp_ne_zero _) (ne_of_gt (Real.rpow_pos_of_pos hp _)),
      Real.log_exp, Real.log_rpow hp]
    congr 1
    dsimp [θ]
    ring
  simpa only [hopt] using probability_le_exponential_moment P (test θ)
    (htest θ hθ) (hdetect θ hθ) (hmoment θ hθ)

end LeanNumDetect.FiniteMatrixSampling
