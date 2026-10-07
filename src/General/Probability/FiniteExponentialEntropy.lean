import General.Probability.FiniteEntropy
import General.Probability.FiniteProductReplacement
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Exponential replacement-entropy inequalities for finite independent
weighted laws. These are proved from the finite entropy tensorization
inequality and the scalar tangent inequality for the exponential. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteEntropy

theorem weightedMean_add {α : Type*} [Fintype α] (q f g : α → ℝ) :
    weightedMean q (fun a => f a + g a) = weightedMean q f + weightedMean q g := by
  simp only [weightedMean, mul_add, Finset.sum_add_distrib]

theorem weighted_covariance_symmetrization {α : Type*} [Fintype α]
    (q u v : α → ℝ) (hqs : ∑ a, q a = 1) :
    weightedMean q (fun a => weightedMean q (fun b => (u a - u b) * (v a - v b))) =
      2 * (weightedMean q (fun a => u a * v a) - weightedMean q u * weightedMean q v) := by
  have hinner (a : α) :
      weightedMean q (fun b => (u a - u b) * (v a - v b)) =
        u a * v a - u a * weightedMean q v - weightedMean q u * v a +
          weightedMean q (fun b => u b * v b) := by
    have heq : (fun b => (u a - u b) * (v a - v b)) =
        (fun b => (u a * v a - u a * v b - u b * v a) + u b * v b) := by
      funext b
      ring
    rw [heq, weightedMean_add, weightedMean_sub, weightedMean_sub,
      weightedMean_const q hqs, weightedMean_mul, weightedMean_mul_right]
  simp_rw [hinner]
  rw [weightedMean_add, weightedMean_sub, weightedMean_sub,
    weightedMean_mul_right, weightedMean_mul,
    weightedMean_const q hqs]
  ring

theorem exp_difference_le_tangent (a b : ℝ) :
    Real.exp b - Real.exp a ≤ Real.exp b * (b - a) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a - b)) (Real.exp_nonneg b)
  rw [← Real.exp_add] at h
  have heq : b + (a - b) = a := by ring
  rw [heq] at h
  nlinarith

theorem exponential_pair_variance_bound (a b θ : ℝ) (hθ : 0 ≤ θ) :
    (Real.exp (θ * a) - Real.exp (θ * b)) * (θ * a - θ * b) ≤
      θ ^ 2 * (Real.exp (θ * a) * (max (a - b) 0)^2 +
        Real.exp (θ * b) * (max (b - a) 0)^2) := by
  by_cases hab : b ≤ a
  · rw [max_eq_left (sub_nonneg.mpr hab), max_eq_right (sub_nonpos.mpr hab)]
    have hd : 0 ≤ θ * a - θ * b := by nlinarith
    have h := mul_le_mul_of_nonneg_right (exp_difference_le_tangent (θ * b) (θ * a)) hd
    convert h using 1 <;> first | rfl | ring
  · have hba := le_of_lt (lt_of_not_ge hab)
    rw [max_eq_right (sub_nonpos.mpr hba), max_eq_left (sub_nonneg.mpr hba)]
    have hd : 0 ≤ θ * b - θ * a := by nlinarith
    have h := mul_le_mul_of_nonneg_right (exp_difference_le_tangent (θ * a) (θ * b)) hd
    convert h using 1 <;> first | rfl | ring

/-- The entropy of an exponential is bounded by its positive replacement
variance. This is the one-coordinate modified logarithmic Sobolev inequality. -/
theorem entropy_exp_le_positive_replacement {α : Type*} [Fintype α]
    (q z : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    entropy q (fun a => Real.exp (θ * z a)) ≤
      θ ^ 2 * weightedMean q (fun a => Real.exp (θ * z a) *
        weightedMean q (fun b => (max (z a - z b) 0)^2)) := by
  let u := fun a => Real.exp (θ * z a)
  let v := fun a => θ * z a
  have hu (a : α) : 0 < u a := Real.exp_pos _
  have hU : 0 < weightedMean q u := weightedMean_pos q u hq hqs hu
  have hjensen := convexOn_exp.map_sum_le (t := Finset.univ) (w := q) (p := v)
    (fun a _ => hq a) hqs (fun _ _ => Set.mem_univ _)
  change Real.exp (weightedMean q v) ≤ weightedMean q u at hjensen
  have hlog : weightedMean q v ≤ Real.log (weightedMean q u) :=
    (Real.le_log_iff_exp_le hU).mpr hjensen
  have hentropy : entropy q u ≤ weightedMean q (fun a => u a * v a) -
      weightedMean q u * weightedMean q v := by
    dsimp [entropy]
    simp only [u, Real.log_exp]
    have hmul := mul_le_mul_of_nonneg_left hlog hU.le
    change _ ≤ weightedMean q (fun a => u a * v a) - weightedMean q u * weightedMean q v
    linarith
  have hpairs := weightedMean_mono hq (fun a => weightedMean_mono hq
    (fun b => exponential_pair_variance_bound (z a) (z b) θ hθ))
  have hpairleft : weightedMean q (fun a => weightedMean q (fun b =>
      (Real.exp (θ * z a) - Real.exp (θ * z b)) * (θ * z a - θ * z b))) =
      2 * (weightedMean q (fun a => u a * v a) - weightedMean q u * weightedMean q v) :=
    weighted_covariance_symmetrization q u v hqs
  have hpairright : weightedMean q (fun a => weightedMean q (fun b =>
      θ ^ 2 * (Real.exp (θ * z a) * (max (z a - z b) 0)^2 +
        Real.exp (θ * z b) * (max (z b - z a) 0)^2))) =
      2 * θ ^ 2 * weightedMean q (fun a => Real.exp (θ * z a) *
        weightedMean q (fun b => (max (z a - z b) 0)^2)) := by
    simp_rw [weightedMean_mul, weightedMean_add]
    have hfirst : weightedMean q (fun a => weightedMean q (fun b =>
        Real.exp (θ * z a) * (max (z a - z b) 0)^2)) =
        weightedMean q (fun a => Real.exp (θ * z a) *
          weightedMean q (fun b => (max (z a - z b) 0)^2)) := by
      congr 1
      funext a
      exact weightedMean_mul q _ _
    have hswap := weightedMean_comm q q
      (fun a b => Real.exp (θ * z b) * (max (z b - z a) 0)^2)
    simp_rw [weightedMean_mul] at hswap
    rw [hfirst, hswap]
    ring
  rw [hpairleft, hpairright] at hpairs
  change entropy q u ≤ _
  linarith

noncomputable def positiveReplacementVariance {α : Type*} [Fintype α]
    (q : α → ℝ) {m : ℕ} (Z : (Fin m → α) → ℝ) (x : Fin m → α) : ℝ :=
  ∑ i, weightedMean q (fun y => (max (Z x - Z (Function.update x i y)) 0)^2)

/-- The modified logarithmic Sobolev inequality on a finite weighted product
space, expressed through the one-sided replacement variance. -/
theorem entropy_product_exp_le_replacementVariance {α : Type*} [Fintype α]
    (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    {m : ℕ} (Z : (Fin m → α) → ℝ) (θ : ℝ) (hθ : 0 ≤ θ) :
    entropy (productWeight q) (fun x => Real.exp (θ * Z x)) ≤
      θ^2 * weightedMean (productWeight q)
        (fun x => Real.exp (θ * Z x) * positiveReplacementVariance q Z x) := by
  have htensor := entropy_product_tensorization q hq hqs m
    (fun x => Real.exp (θ * Z x)) (fun _ => Real.exp_pos _)
  have hupdate (x : Fin m → α) (i : Fin m) (y y' : α) :
      Function.update (Function.update x i y) i y' = Function.update x i y' := by
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk]
  have hcoordinate (i : Fin m) :
      weightedMean (productWeight q) (fun x =>
        entropy q (fun y => Real.exp (θ * Z (Function.update x i y)))) ≤
      θ^2 * weightedMean (productWeight q) (fun x => Real.exp (θ * Z x) *
        weightedMean q (fun y => (max (Z x - Z (Function.update x i y)) 0)^2)) := by
    let φ := fun x : Fin m → α => Real.exp (θ * Z x) *
      weightedMean q (fun y => (max (Z x - Z (Function.update x i y)) 0)^2)
    have hpoint (x : Fin m → α) :
        entropy q (fun y => Real.exp (θ * Z (Function.update x i y))) ≤
        θ^2 * weightedMean q (fun y => φ (Function.update x i y)) := by
      have h := entropy_exp_le_positive_replacement q
        (fun y => Z (Function.update x i y)) hq hqs θ hθ
      simpa only [φ, hupdate] using h
    calc
      _ ≤ weightedMean (productWeight q) (fun x =>
          θ^2 * weightedMean q (fun y => φ (Function.update x i y))) :=
        weightedMean_mono (productWeight_nonneg q hq) hpoint
      _ = θ^2 * weightedMean (productWeight q) φ := by
        rw [weightedMean_mul, weightedMean_coordinate_refresh q hqs i φ]
      _ = _ := rfl
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
    hcoordinate i)
  have h := htensor.trans hsum
  have hright : (∑ i, θ^2 * weightedMean (productWeight q) (fun x =>
      Real.exp (θ * Z x) * weightedMean q
        (fun y => (max (Z x - Z (Function.update x i y)) 0)^2))) =
      θ^2 * weightedMean (productWeight q)
        (fun x => Real.exp (θ * Z x) * positiveReplacementVariance q Z x) := by
    rw [← Finset.mul_sum, ← weightedMean_sum]
    congr 2
    funext x
    exact (Finset.mul_sum _ _ _).symm
  rw [hright] at h
  exact h

/-- A variance proxy affine in the empirical supremum gives the exact
variance-sensitive exponential entropy inequality needed by Herbst's method. -/
theorem entropy_product_exp_le_linearVariance {α : Type*} [Fintype α]
    (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    {m : ℕ} (Z : (Fin m → α) → ℝ) {p b : ℝ}
    (hvariance : ∀ x, positiveReplacementVariance q Z x ≤ p * Z x + b)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    entropy (productWeight q) (fun x => Real.exp (θ * Z x)) ≤
      θ^2 * (p * weightedMean (productWeight q) (fun x => Z x * Real.exp (θ * Z x)) +
        b * weightedMean (productWeight q) (fun x => Real.exp (θ * Z x))) := by
  have h := entropy_product_exp_le_replacementVariance q hq hqs Z θ hθ
  have hb := weightedMean_mono (productWeight_nonneg q hq) (fun x =>
    mul_le_mul_of_nonneg_left (hvariance x) (Real.exp_nonneg (θ * Z x)))
  have hscaled := mul_le_mul_of_nonneg_left hb (sq_nonneg θ)
  have ht := h.trans hscaled
  have heq : weightedMean (productWeight q) (fun x =>
      Real.exp (θ * Z x) * (p * Z x + b)) =
      p * weightedMean (productWeight q) (fun x => Z x * Real.exp (θ * Z x)) +
        b * weightedMean (productWeight q) (fun x => Real.exp (θ * Z x)) := by
    have hfun : (fun x => Real.exp (θ * Z x) * (p * Z x + b)) =
        (fun x => p * (Z x * Real.exp (θ * Z x)) + b * Real.exp (θ * Z x)) := by
      funext x
      ring
    rw [hfun, weightedMean_add, weightedMean_mul, weightedMean_mul]
  rw [heq] at ht
  exact ht

end LeanNumDetect.FiniteEntropy
