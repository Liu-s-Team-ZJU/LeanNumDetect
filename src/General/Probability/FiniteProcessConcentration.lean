import General.Probability.FiniteExponentialEntropy
import General.Probability.HerbstBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Differentiation of finite weighted moment-generating functions and the
variance-sensitive differential inequality for product-space suprema. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteEntropy

noncomputable def exponentialMoment {α : Type*} [Fintype α]
    (q Z : α → ℝ) (θ : ℝ) : ℝ := weightedMean q (fun a => Real.exp (θ * Z a))

noncomputable def exponentialMomentDerivative {α : Type*} [Fintype α]
    (q Z : α → ℝ) (θ : ℝ) : ℝ := weightedMean q (fun a => Z a * Real.exp (θ * Z a))

noncomputable def logExponentialMoment {α : Type*} [Fintype α]
    (q Z : α → ℝ) (θ : ℝ) : ℝ := Real.log (exponentialMoment q Z θ)

theorem exponentialMoment_pos {α : Type*} [Fintype α] (q Z : α → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) (θ : ℝ) :
    0 < exponentialMoment q Z θ :=
  weightedMean_pos q _ hq hqs (fun _ => Real.exp_pos _)

theorem hasDerivAt_exponentialMoment {α : Type*} [Fintype α]
    (q Z : α → ℝ) (θ : ℝ) :
    HasDerivAt (exponentialMoment q Z) (exponentialMomentDerivative q Z θ) θ := by
  have hsingle (a : α) : HasDerivAt (fun t : ℝ => q a * Real.exp (t * Z a))
      (q a * (Z a * Real.exp (θ * Z a))) θ := by
    convert (((hasDerivAt_id θ).mul_const (Z a)).exp.const_mul (q a)) using 1 <;>
      first | rfl | simp only [id_eq, mul_comm, mul_assoc, one_mul]
  change HasDerivAt (fun t => ∑ a, q a * Real.exp (t * Z a))
    (∑ a, q a * (Z a * Real.exp (θ * Z a))) θ
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => hsingle a)

theorem hasDerivAt_logExponentialMoment {α : Type*} [Fintype α]
    (q Z : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) (θ : ℝ) :
    HasDerivAt (logExponentialMoment q Z)
      (exponentialMomentDerivative q Z θ / exponentialMoment q Z θ) θ :=
  (hasDerivAt_exponentialMoment q Z θ).log (exponentialMoment_pos q Z hq hqs θ).ne'

theorem exponentialMoment_zero {α : Type*} [Fintype α] (q Z : α → ℝ)
    (hqs : ∑ a, q a = 1) : exponentialMoment q Z 0 = 1 := by
  simp only [exponentialMoment, zero_mul, Real.exp_zero, weightedMean_const q hqs 1]

theorem logExponentialMoment_zero {α : Type*} [Fintype α] (q Z : α → ℝ)
    (hqs : ∑ a, q a = 1) : logExponentialMoment q Z 0 = 0 := by
  rw [logExponentialMoment, exponentialMoment_zero q Z hqs, Real.log_one]

theorem hasDerivAt_logExponentialMoment_zero {α : Type*} [Fintype α]
    (q Z : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) :
    HasDerivAt (logExponentialMoment q Z) (weightedMean q Z) 0 := by
  have h := hasDerivAt_logExponentialMoment q Z hq hqs 0
  simpa only [exponentialMoment_zero q Z hqs, exponentialMomentDerivative,
    zero_mul, Real.exp_zero, mul_one, div_one] using h

theorem entropy_exponentialMoment_eq {α : Type*} [Fintype α]
    (q Z : α → ℝ) (θ : ℝ) :
    entropy q (fun a => Real.exp (θ * Z a)) =
      θ * exponentialMomentDerivative q Z θ -
        exponentialMoment q Z θ * logExponentialMoment q Z θ := by
  have hfun : (fun a => Real.exp (θ * Z a) * Real.log (Real.exp (θ * Z a))) =
      (fun a => θ * (Z a * Real.exp (θ * Z a))) := by
    funext a
    rw [Real.log_exp]
    ring
  unfold entropy
  rw [hfun, weightedMean_mul]
  rfl

/-- The exact differential inequality used by the scalar Herbst comparison.
The scale is the row envelope `p` rather than its square. -/
theorem logExponentialMoment_product_differential {α : Type*} [Fintype α]
    (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    {m : ℕ} (Z : (Fin m → α) → ℝ) {p b : ℝ}
    (hvariance : ∀ x, positiveReplacementVariance q Z x ≤ p * Z x + b)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    θ * (1 - p * θ) * (exponentialMomentDerivative (productWeight q) Z θ /
      exponentialMoment (productWeight q) Z θ) -
        logExponentialMoment (productWeight q) Z θ ≤ b * θ^2 := by
  have h := entropy_product_exp_le_linearVariance q hq hqs Z hvariance θ hθ
  rw [entropy_exponentialMoment_eq] at h
  have hM := exponentialMoment_pos (productWeight q) Z
    (productWeight_nonneg q hq) (productWeight_sum q hqs m) θ
  change θ * exponentialMomentDerivative (productWeight q) Z θ -
    exponentialMoment (productWeight q) Z θ * logExponentialMoment (productWeight q) Z θ ≤
    θ^2 * (p * exponentialMomentDerivative (productWeight q) Z θ +
      b * exponentialMoment (productWeight q) Z θ) at h
  have heq : θ * (1 - p * θ) * (exponentialMomentDerivative (productWeight q) Z θ /
      exponentialMoment (productWeight q) Z θ) - logExponentialMoment (productWeight q) Z θ =
      (θ * (1 - p * θ) * exponentialMomentDerivative (productWeight q) Z θ -
        exponentialMoment (productWeight q) Z θ * logExponentialMoment (productWeight q) Z θ) /
          exponentialMoment (productWeight q) Z θ := by
    field_simp [hM.ne']
  rw [heq]
  apply (div_le_iff₀ hM).mpr
  nlinarith [h]

noncomputable def weightedProbability {α : Type*} [Fintype α]
    (q : α → ℝ) (P : α → Prop) : ℝ := by
  classical
  exact weightedMean q (fun a => if P a then 1 else 0)

/-- Laplace's elementary tail inequality for a finite weighted law. -/
theorem weightedProbability_le_exponentialMoment {α : Type*} [Fintype α]
    (q Z : α → ℝ) (hq : ∀ a, 0 ≤ q a) {θ : ℝ} (hθ : 0 ≤ θ) (r : ℝ) :
    weightedProbability q (fun a => r ≤ Z a) ≤
      Real.exp (-θ * r) * exponentialMoment q Z θ := by
  classical
  have hpoint (a : α) : (if r ≤ Z a then (1 : ℝ) else 0) ≤ Real.exp (θ * (Z a - r)) := by
    split_ifs with ha
    · have he := Real.exp_le_exp.mpr (mul_nonneg hθ (sub_nonneg.mpr ha))
      simpa only [Real.exp_zero] using he
    · exact Real.exp_nonneg _
  have h := weightedMean_mono hq hpoint
  change weightedProbability q (fun a => r ≤ Z a) ≤ _ at h
  have hfun : (fun a => Real.exp (θ * (Z a - r))) =
      (fun a => Real.exp (-θ * r) * Real.exp (θ * Z a)) := by
    funext a
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun, weightedMean_mul] at h
  exact h

/-- A subgamma moment bound gives a variance-sensitive tail. The conservative
denominator also includes the case of zero variance parameter. -/
theorem weightedProbability_tail_of_subgamma {α : Type*} [Fintype α]
    (q Z : α → ℝ) (hq : ∀ a, 0 ≤ q a) {p v a : ℝ}
    (hp : 0 < p) (hv : 0 ≤ v)
    (hmoment : ∀ θ ∈ Set.Ioo 0 (1 / p), exponentialMoment q Z θ ≤
      Real.exp (θ * a + v * θ^2 / (1 - p * θ))) {u : ℝ} (hu : 0 < u) :
    weightedProbability q (fun x => a + u ≤ Z x) ≤
      Real.exp (-u^2 / (4 * (v + p * u))) := by
  let θ := u / (2 * (v + p * u))
  have hden : 0 < v + p * u := add_pos_of_nonneg_of_pos hv (mul_pos hp hu)
  have hθ : 0 < θ := div_pos hu (mul_pos (by norm_num) hden)
  have hpθ : p * θ ≤ 1 / 2 := by
    dsimp [θ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (mul_pos (by norm_num) hden)).mpr
    nlinarith
  have hθp : θ < 1 / p := (lt_div_iff₀ hp).mpr (by nlinarith [hpθ])
  have h1 : 0 < 1 - p * θ := by linarith
  have htail := weightedProbability_le_exponentialMoment q Z hq hθ.le (a + u)
  have hmgf := mul_le_mul_of_nonneg_left (hmoment θ ⟨hθ, hθp⟩)
    (Real.exp_nonneg (-θ * (a + u)))
  have heq : Real.exp (-θ * (a + u)) *
      Real.exp (θ * a + v * θ^2 / (1 - p * θ)) =
      Real.exp (v * θ^2 / (1 - p * θ) - θ * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at hmgf
  have hvterm : v * θ^2 / (1 - p * θ) ≤ θ * u / 2 := by
    apply (div_le_iff₀ h1).mpr
    have hθeq : θ * (2 * (v + p * u)) = u := by
      dsimp [θ]
      exact div_mul_cancel₀ u (ne_of_gt (mul_pos (by norm_num) hden))
    have hvθ : v * θ ≤ u / 2 - p * θ * u := by nlinarith [hθeq]
    have hmul := mul_le_mul_of_nonneg_right hvθ hθ.le
    have hpos : 0 ≤ p * θ^2 * u := mul_nonneg (mul_nonneg hp.le (sq_nonneg θ)) hu.le
    nlinarith [hmul, hpos]
  calc
    _ ≤ Real.exp (v * θ^2 / (1 - p * θ) - θ * u) := htail.trans hmgf
    _ ≤ Real.exp (-(θ * u) / 2) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      congr 1
      dsimp [θ]
      field_simp [hden.ne']
      norm_num

/-- A linear replacement variance bound gives a subgamma exponential moment
under a finite weighted independent product law. -/
theorem exponentialMoment_product_le_linearVariance {α : Type*} [Fintype α]
    (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    {m : ℕ} (Z : (Fin m → α) → ℝ) {p b : ℝ} (hp : 0 < p)
    (hvariance : ∀ x, positiveReplacementVariance q Z x ≤ p * Z x + b)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (1 / p)) :
    exponentialMoment (productWeight q) Z θ ≤
      Real.exp (θ * weightedMean (productWeight q) Z +
        (p * weightedMean (productWeight q) Z + b) * θ^2 / (1 - p * θ)) := by
  have hprod := productWeight_nonneg q hq (m := m)
  have hprods := productWeight_sum q hqs m
  have hbound := HerbstBounds.herbst_logMoment_bound
    (logExponentialMoment (productWeight q) Z)
    (fun t => exponentialMomentDerivative (productWeight q) Z t /
      exponentialMoment (productWeight q) Z t) hp
    (logExponentialMoment_zero (productWeight q) Z hprods)
    (hasDerivAt_logExponentialMoment_zero (productWeight q) Z hprod hprods)
    (fun t _ => hasDerivAt_logExponentialMoment (productWeight q) Z hprod hprods t)
    (fun t ht => logExponentialMoment_product_differential q hq hqs Z hvariance t ht.1.le)
    θ ⟨hθ.1.le, hθ.2⟩
  have he := Real.exp_le_exp.mpr hbound
  rw [logExponentialMoment, Real.exp_log (exponentialMoment_pos (productWeight q) Z hprod hprods θ)] at he
  exact he

/-- Variance-sensitive concentration around the expectation for a finite
weighted independent product law. -/
theorem weightedProbability_product_tail_linearVariance {α : Type*} [Fintype α]
    (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    {m : ℕ} (Z : (Fin m → α) → ℝ) {p b : ℝ} (hp : 0 < p)
    (hvariance : ∀ x, positiveReplacementVariance q Z x ≤ p * Z x + b)
    (hv : 0 ≤ p * weightedMean (productWeight q) Z + b) {u : ℝ} (hu : 0 < u) :
    weightedProbability (productWeight q)
      (fun x => weightedMean (productWeight q) Z + u ≤ Z x) ≤
      Real.exp (-u^2 / (4 * (p * weightedMean (productWeight q) Z + b + p * u))) :=
  weightedProbability_tail_of_subgamma (productWeight q) Z (productWeight_nonneg q hq)
    hp hv (fun _ ht => exponentialMoment_product_le_linearVariance q hq hqs Z hp hvariance ht) hu

end LeanNumDetect.FiniteEntropy
