import General.Probability.FiniteAverage
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Entropy of strictly positive functions under finite weighted probability
laws. The variational bound gives the convexity of entropy, which is the
basic ingredient in product-space entropy tensorization. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteEntropy

noncomputable def weightedMean {α : Type*} [Fintype α]
    (q f : α → ℝ) : ℝ := ∑ a, q a * f a

noncomputable def entropy {α : Type*} [Fintype α]
    (q f : α → ℝ) : ℝ :=
  weightedMean q (fun a => f a * Real.log (f a)) -
    weightedMean q f * Real.log (weightedMean q f)

theorem weightedMean_pos {α : Type*} [Fintype α] (q f : α → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) (hf : ∀ a, 0 < f a) :
    0 < weightedMean q f := by
  classical
  have hex : ∃ a, 0 < q a := by
    by_contra h
    push Not at h
    have hz : ∀ a, q a = 0 := fun a => le_antisymm (h a) (hq a)
    simp only [hz, Finset.sum_const_zero] at hqs
    norm_num at hqs
  obtain ⟨a, ha⟩ := hex
  exact (mul_pos ha (hf a)).trans_le (Finset.single_le_sum
    (fun b _ => mul_nonneg (hq b) (hf b).le) (Finset.mem_univ a))

theorem weightedMean_mono {α : Type*} [Fintype α] {q f g : α → ℝ}
    (hq : ∀ a, 0 ≤ q a) (h : ∀ a, f a ≤ g a) :
    weightedMean q f ≤ weightedMean q g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hq a)

theorem weightedMean_const {α : Type*} [Fintype α] (q : α → ℝ)
    (hqs : ∑ a, q a = 1) (c : ℝ) : weightedMean q (fun _ => c) = c := by
  rw [weightedMean, ← Finset.sum_mul, hqs, one_mul]

theorem weightedMean_mul {α : Type*} [Fintype α] (q f : α → ℝ) (c : ℝ) :
    weightedMean q (fun a => c * f a) = c * weightedMean q f := by
  simp only [weightedMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem weightedMean_sum {α J : Type*} [Fintype α] [Fintype J]
    (q : α → ℝ) (f : J → α → ℝ) :
    weightedMean q (fun a => ∑ j, f j a) = ∑ j, weightedMean q (f j) := by
  simp only [weightedMean, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem weightedMean_sub {α : Type*} [Fintype α] (q f g : α → ℝ) :
    weightedMean q (fun a => f a - g a) = weightedMean q f - weightedMean q g := by
  simp only [weightedMean, mul_sub, Finset.sum_sub_distrib]

theorem weightedMean_mul_right {α : Type*} [Fintype α] (q f : α → ℝ) (c : ℝ) :
    weightedMean q (fun a => f a * c) = weightedMean q f * c := by
  simp only [weightedMean, Finset.sum_mul, mul_assoc]

theorem weightedMean_comm {α J : Type*} [Fintype α] [Fintype J]
    (q : α → ℝ) (r : J → ℝ) (f : J → α → ℝ) :
    weightedMean r (fun j => weightedMean q (f j)) =
      weightedMean q (fun a => weightedMean r (fun j => f j a)) := by
  simp only [weightedMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Gibbs' variational inequality for entropy, with a freely chosen positive
comparison function. Equality holds when the comparison function is `f`. -/
theorem entropy_variational_bound {α : Type*} [Fintype α] (q f v : α → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    (hf : ∀ a, 0 < f a) (hv : ∀ a, 0 < v a) :
    weightedMean q (fun a => f a * Real.log (v a)) -
      weightedMean q f * Real.log (weightedMean q v) ≤ entropy q f := by
  let F := weightedMean q f
  let V := weightedMean q v
  have hF : 0 < F := weightedMean_pos q f hq hqs hf
  have hV : 0 < V := weightedMean_pos q v hq hqs hv
  have hpoint (a : α) :
      q a * f a * (Real.log (v a) + Real.log F - Real.log (f a) - Real.log V) ≤
        q a * (v a * F / V - f a) := by
    have hratio : 0 < v a * F / (f a * V) := div_pos (mul_pos (hv a) hF)
      (mul_pos (hf a) hV)
    have hlog := Real.log_le_sub_one_of_pos hratio
    have hlogeq : Real.log (v a * F / (f a * V)) =
        Real.log (v a) + Real.log F - Real.log (f a) - Real.log V := by
      rw [Real.log_div (mul_ne_zero (hv a).ne' hF.ne')
        (mul_ne_zero (hf a).ne' hV.ne'),
        Real.log_mul (hv a).ne' hF.ne', Real.log_mul (hf a).ne' hV.ne']
      ring
    rw [hlogeq] at hlog
    calc
      _ ≤ q a * f a * (v a * F / (f a * V) - 1) :=
        mul_le_mul_of_nonneg_left hlog (mul_nonneg (hq a) (hf a).le)
      _ = _ := by field_simp [(hf a).ne', hV.ne']
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  have hright : (∑ a, q a * (v a * F / V - f a)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    have ht : (∑ a, q a * (v a * F / V)) = V * F / V := by
      change _ = (∑ a, q a * v a) * F / V
      simp only [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [ht]
    change V * F / V - F = 0
    field_simp [hV.ne']
    ring
  rw [hright] at hsum
  have hleft : (∑ a, q a * f a *
      (Real.log (v a) + Real.log F - Real.log (f a) - Real.log V)) =
      weightedMean q (fun a => f a * Real.log (v a)) + F * Real.log F -
        weightedMean q (fun a => f a * Real.log (f a)) - F * Real.log V := by
    simp only [weightedMean, F, mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
  rw [hleft] at hsum
  dsimp [entropy]
  change weightedMean q (fun a => f a * Real.log (v a)) - F * Real.log V ≤ _
  change _ ≤ weightedMean q (fun a => f a * Real.log (f a)) - F * Real.log F
  linarith

theorem entropy_nonneg {α : Type*} [Fintype α] (q f : α → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) (hf : ∀ a, 0 < f a) :
    0 ≤ entropy q f := by
  have h := entropy_variational_bound q f (fun _ => 1) hq hqs hf (by intro; norm_num)
  rw [weightedMean_const q hqs 1] at h
  simpa [weightedMean] using h

/-- Entropy is convex as a functional of the positive density. This weighted
Jensen inequality is the form needed for product-space tensorization. -/
theorem entropy_weightedMean_le {α J : Type*} [Fintype α] [Fintype J]
    (q : α → ℝ) (r : J → ℝ) (f : J → α → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    (hr : ∀ j, 0 ≤ r j) (hrs : ∑ j, r j = 1) (hf : ∀ j a, 0 < f j a) :
    entropy q (fun a => weightedMean r (fun j => f j a)) ≤
      weightedMean r (fun j => entropy q (f j)) := by
  let F := fun a => weightedMean r (fun j => f j a)
  have hF (a : α) : 0 < F a := weightedMean_pos r (fun j => f j a) hr hrs (fun j => hf j a)
  have hbound := weightedMean_mono hr (fun j =>
    entropy_variational_bound q (f j) F hq hqs (hf j) hF)
  have hexact : weightedMean r (fun j =>
      weightedMean q (fun a => f j a * Real.log (F a)) -
        weightedMean q (f j) * Real.log (weightedMean q F)) = entropy q F := by
    rw [weightedMean_sub, weightedMean_mul_right, weightedMean_comm q r f,
      weightedMean_comm q r (fun j a => f j a * Real.log (F a))]
    change weightedMean q (fun a => weightedMean r (fun j => f j a * Real.log (F a))) -
      weightedMean q F * Real.log (weightedMean q F) = entropy q F
    simp only [weightedMean_mul_right]
    rfl
  rw [hexact] at hbound
  exact hbound

noncomputable def productWeight {α : Type*} (q : α → ℝ) {m : ℕ}
    (x : Fin m → α) : ℝ := ∏ i, q (x i)

theorem productWeight_nonneg {α : Type*} (q : α → ℝ) (hq : ∀ a, 0 ≤ q a)
    {m : ℕ} (x : Fin m → α) : 0 ≤ productWeight q x :=
  Finset.prod_nonneg fun i _ => hq (x i)

theorem productWeight_sum {α : Type*} [Fintype α] (q : α → ℝ)
    (hqs : ∑ a, q a = 1) (m : ℕ) :
    ∑ x : Fin m → α, productWeight q x = 1 := by
  unfold productWeight
  rw [← Fintype.prod_sum]
  simp [hqs]

theorem weightedMean_product_succ {α : Type*} [Fintype α] (q : α → ℝ)
    {m : ℕ} (f : (Fin (m + 1) → α) → ℝ) :
    weightedMean (productWeight q) f =
      weightedMean q (fun a => weightedMean (productWeight q) (fun x => f (Fin.cons a x))) := by
  let e := Fin.consEquiv (fun _ : Fin (m + 1) => α)
  unfold weightedMean
  rw [← e.sum_comp (fun x => productWeight q x * f x), Fintype.sum_prod_type]
  simp only [e, Fin.consEquiv_apply, productWeight, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.mul_sum, mul_assoc]
  rfl

theorem entropy_product_succ_eq {α : Type*} [Fintype α] (q : α → ℝ)
    {m : ℕ} (f : (Fin (m + 1) → α) → ℝ) :
    entropy (productWeight q) f =
      weightedMean (productWeight q) (fun x : Fin m → α => entropy q (fun a => f (Fin.cons a x))) +
      entropy (productWeight q) (fun x : Fin m → α => weightedMean q (fun a => f (Fin.cons a x))) := by
  unfold entropy
  rw [weightedMean_product_succ,
    weightedMean_product_succ]
  rw [weightedMean_comm (productWeight q) q (fun a x => f (Fin.cons a x)),
    weightedMean_comm (productWeight q) q (fun a x => f (Fin.cons a x) * Real.log (f (Fin.cons a x)))]
  rw [weightedMean_sub]
  ring

/-- Entropy subadditivity for two factors; induction gives the full product
tensorization inequality. -/
theorem entropy_product_succ_le {α : Type*} [Fintype α] (q : α → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1)
    {m : ℕ} (f : (Fin (m + 1) → α) → ℝ) (hf : ∀ x, 0 < f x) :
    entropy (productWeight q) f ≤
      weightedMean (productWeight q) (fun x : Fin m → α => entropy q (fun a => f (Fin.cons a x))) +
      weightedMean q (fun a => entropy (productWeight q) (fun x : Fin m → α => f (Fin.cons a x))) := by
  rw [entropy_product_succ_eq]
  exact add_le_add (le_refl _) (entropy_weightedMean_le (productWeight q) q
    (fun (a : α) (x : Fin m → α) => f (Fin.cons a x))
    (productWeight_nonneg q hq) (productWeight_sum q hqs m) hq hqs (fun a x => hf _))

theorem update_cons_zero {α : Type*} {m : ℕ} (a y : α) (x : Fin m → α) :
    Function.update (Fin.cons a x : Fin (m + 1) → α) 0 y = Fin.cons y x := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

theorem update_cons_succ {α : Type*} {m : ℕ} (a y : α) (x : Fin m → α) (i : Fin m) :
    Function.update (Fin.cons a x : Fin (m + 1) → α) i.succ y =
      Fin.cons a (Function.update x i y) := by
  funext k
  cases k using Fin.cases with
  | zero => simp [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
  | succ k =>
    by_cases hk : k = i
    · subst k
      simp
    · simp [hk]

theorem weightedMean_coordinateEntropy_zero {α : Type*} [Fintype α]
    (q : α → ℝ) (hqs : ∑ a, q a = 1) {m : ℕ}
    (f : (Fin (m + 1) → α) → ℝ) :
    weightedMean (productWeight q) (fun x => entropy q (fun y => f (Function.update x 0 y))) =
      weightedMean (productWeight q) (fun x : Fin m → α => entropy q (fun y => f (Fin.cons y x))) := by
  rw [weightedMean_product_succ]
  simp only [update_cons_zero]
  exact weightedMean_const q hqs _

theorem weightedMean_coordinateEntropy_succ {α : Type*} [Fintype α]
    (q : α → ℝ) {m : ℕ} (f : (Fin (m + 1) → α) → ℝ) (i : Fin m) :
    weightedMean (productWeight q) (fun x => entropy q (fun y => f (Function.update x i.succ y))) =
      weightedMean q (fun a => weightedMean (productWeight q)
        (fun x : Fin m → α => entropy q (fun y => f (Fin.cons a (Function.update x i y))))) := by
  rw [weightedMean_product_succ]
  simp only [update_cons_succ]

/-- Tensorization of entropy over an arbitrary finite weighted independent
product law. This statement is an inequality for explicit finite sums and
does not import an external concentration theorem. -/
theorem entropy_product_tensorization {α : Type*} [Fintype α]
    (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hqs : ∑ a, q a = 1) (m : ℕ)
    (f : (Fin m → α) → ℝ) (hf : ∀ x, 0 < f x) :
    entropy (productWeight q) f ≤
      ∑ i, weightedMean (productWeight q) (fun x => entropy q (fun y => f (Function.update x i y))) := by
  induction m with
  | zero =>
    simp [entropy, weightedMean, productWeight]
  | succ m ih =>
    have hstep := entropy_product_succ_le q hq hqs f hf
    have hrest := weightedMean_mono hq (fun a => ih
      (fun x : Fin m → α => f (Fin.cons a x)) (fun x => hf _))
    have htotal := hstep.trans (add_le_add (le_refl _) hrest)
    rw [weightedMean_sum] at htotal
    rw [Fin.sum_univ_succ, weightedMean_coordinateEntropy_zero q hqs]
    simpa only [weightedMean_coordinateEntropy_succ] using htotal

end LeanNumDetect.FiniteEntropy
