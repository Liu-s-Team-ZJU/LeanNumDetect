import General.Fourier.ExponentialCompanion
import General.Fourier.PolynomialEvaluationBounds
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Explicit companion-generator perturbation bounds in the maximum row-sum
operator norm. All bounds are uniform through repeated roots. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators Matrix.Norms.Operator NNReal
open Matrix Set

namespace LeanNumDetect.QuantitativeCompanionBounds
open ExponentialCompanion PolynomialEvaluationBounds
noncomputable section

/-- The total coefficient mass of the annihilating polynomial, including
its monic leading coefficient. -/
theorem rootPolynomial_coefficient_mass_le {s : ℕ} (frequency : Fin s → ℂ)
    {r : ℝ} (_hr : 0 ≤ r) (hfrequency : ‖frequency‖ ≤ r) :
    ∑ k ∈ Finset.range (s + 1), ‖(rootPolynomial frequency).coeff k‖ ≤ (1 + r) ^ s := by
  have hcoeff (k : ℕ) (hk : k ≤ s) :
      ‖(rootPolynomial frequency).coeff k‖ ≤
        ∑ T ∈ (Finset.univ : Finset (Fin s)).powersetCard (s - k),
          ∏ _i ∈ T, r := by
    have heq : rootPolynomial frequency =
        ∏ i : Fin s, (Polynomial.X + Polynomial.C (-frequency i)) := by
      simp only [rootPolynomial, sub_eq_add_neg, map_neg Polynomial.C]
    rw [heq, Finset.prod_X_add_C_coeff Finset.univ (fun i => -frequency i) (by simpa)]
    simp only [Finset.card_univ, Fintype.card_fin]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro T hT
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro i hi
    simpa only [norm_neg] using (norm_le_pi_norm frequency i).trans hfrequency
  calc
    _ ≤ ∑ k ∈ Finset.range (s + 1),
        ∑ T ∈ (Finset.univ : Finset (Fin s)).powersetCard (s - k), ∏ _i ∈ T, r := by
      exact Finset.sum_le_sum fun k hk => hcoeff k (by simpa using Finset.mem_range.mp hk)
    _ = ∑ T ∈ (Finset.univ : Finset (Fin s)).powerset, ∏ _i ∈ T, r := by
      have hrefl := Finset.sum_range_reflect
        (fun k => ∑ T ∈ (Finset.univ : Finset (Fin s)).powersetCard k, ∏ _i ∈ T, r)
        (s + 1)
      simp only [Nat.add_sub_cancel] at hrefl
      rw [hrefl, Finset.sum_powerset]
      simp
    _ = (1 + r) ^ s := by
      rw [← Finset.prod_one_add]
      simp

theorem rootPolynomial_lower_coefficient_mass_le {s : ℕ} (frequency : Fin s → ℂ)
    {r : ℝ} (hr : 0 ≤ r) (hfrequency : ‖frequency‖ ≤ r) :
    ∑ j : Fin s, ‖(rootPolynomial frequency).coeff j.val‖ ≤ (1 + r) ^ s - 1 := by
  have h := rootPolynomial_coefficient_mass_le frequency hr hfrequency
  rw [Finset.sum_range_succ, rootPolynomial_coeff_degree, norm_one,
    ← Fin.sum_univ_eq_sum_range] at h
  linarith

theorem rootPolynomial_lower_coefficient_mass_linear {s : ℕ} (hs : 0 < s)
    (frequency : Fin s → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hradius : r ≤ 1 / (2 * (s : ℝ))) (hfrequency : ‖frequency‖ ≤ r) :
    ∑ j : Fin s, ‖(rootPolynomial frequency).coeff j.val‖ ≤ 2 * (s : ℝ) * r := by
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hsr : (s : ℝ) * r ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (s : ℝ))).mp hradius
    nlinarith
  have hpow : (1 + r) ^ s ≤ Real.exp ((s : ℝ) * r) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    simpa only [add_comm] using Real.add_one_le_exp r
  have hexp := Real.abs_exp_sub_one_le (x := (s : ℝ) * r)
    (by rw [abs_of_nonneg (by positivity)]; linarith)
  have hexp' := (le_abs_self (Real.exp ((s : ℝ) * r) - 1)).trans hexp
  rw [abs_of_nonneg (by positivity)] at hexp'
  exact (rootPolynomial_lower_coefficient_mass_le frequency hr hfrequency).trans
    (by nlinarith)

theorem matrix_norm_le_of_row_sums {s : ℕ} (A : Matrix (Fin s) (Fin s) ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ C) : ‖A‖ ≤ C := by
  rw [Matrix.linfty_opNorm_def]
  have hrow' : ∀ i, (∑ j, ‖A i j‖₊) ≤ (⟨C, hC⟩ : ℝ≥0) := by
    intro i
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_sum]
    change (∑ j, ‖A i j‖) ≤ C
    exact hrow i
  exact_mod_cast Finset.sup_le (fun i _ => hrow' i)

theorem generator_sub_shift_norm_le {s : ℕ} (hs : 0 < s)
    (frequency : Fin s → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hradius : r ≤ 1 / (2 * (s : ℝ))) (hfrequency : ‖frequency‖ ≤ r) :
    ‖generator frequency - jetShift s‖ ≤ 2 * (s : ℝ) * r := by
  apply matrix_norm_le_of_row_sums _ (by positivity)
  intro i
  by_cases hi : i.val + 1 < s
  · simp [generator, jetShift, hi]
    positivity
  · have hj (j : Fin s) : ¬j.val = i.val + 1 := by omega
    simpa only [Matrix.sub_apply, generator, if_neg hi, jetShift, hj, if_false,
      sub_zero, norm_neg] using
      rootPolynomial_lower_coefficient_mass_linear hs frequency hr hradius hfrequency

/-- The maximum row-sum norm is at most one, including in dimension one. -/
theorem generator_norm_le_one {s : ℕ} (hs : 0 < s)
    (frequency : Fin s → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hradius : r ≤ 1 / (2 * (s : ℝ))) (hfrequency : ‖frequency‖ ≤ r) :
    ‖generator frequency‖ ≤ 1 := by
  apply matrix_norm_le_of_row_sums _ zero_le_one
  intro i
  by_cases hi : i.val + 1 < s
  · let next : Fin s := ⟨i.val + 1, hi⟩
    have heq (j : Fin s) : j.val = i.val + 1 ↔ j = next :=
      ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp [generator, hi, heq, apply_ite]
  · have hmass := rootPolynomial_lower_coefficient_mass_linear hs frequency hr hradius hfrequency
    have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (s : ℝ))).mp hradius
    simpa only [generator, if_neg hi, norm_neg] using hmass.trans (by nlinarith)

theorem generator_pow_initial_rows {s : ℕ} (frequency : Fin s → ℂ)
    (k : ℕ) (i j : Fin s) (h : i.val + k < s) :
    (generator frequency ^ k) i j = if j.val = i.val + k then 1 else 0 := by
  induction k generalizing i with
  | zero => simp [Matrix.one_apply, Fin.ext_iff, eq_comm]
  | succ k ih =>
    have hi : i.val + 1 < s := by omega
    let next : Fin s := ⟨i.val + 1, hi⟩
    have heq (a : Fin s) : a.val = i.val + 1 ↔ a = next :=
      ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    rw [pow_succ', Matrix.mul_apply]
    simp only [generator, if_pos hi, heq, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ih next (by dsimp [next]; omega)]
    congr 2
    dsimp [next]
    omega

theorem generator_pow_firstRow_eq_shift {s : ℕ} (hs : 0 < s)
    (frequency : Fin s → ℂ) (k : ℕ) (hk : k < s) (j : Fin s) :
    (generator frequency ^ k) ⟨0, hs⟩ j = (jetShift s ^ k) ⟨0, hs⟩ j := by
  rw [generator_pow_initial_rows frequency k _ _ (by simpa), jetShift_pow]

theorem jetShift_pow_eq_zero {s : ℕ} (k : ℕ) (hk : s ≤ k) :
    jetShift s ^ k = 0 := by
  ext i j
  rw [jetShift_pow]
  have hj : ¬j.val = i.val + k := by omega
  simp [hj]

theorem generator_pow_firstRow_tail {s : ℕ} (hs : 0 < s)
    (frequency : Fin s → ℂ) (k : ℕ) (j : Fin s) :
    (generator frequency ^ (s + k)) ⟨0, hs⟩ j =
      ∑ a : Fin s, -(rootPolynomial frequency).coeff a.val *
        (generator frequency ^ k) a j := by
  have hsp : s = (s - 1) + 1 := by omega
  have hfirst (a : Fin s) :
      (generator frequency ^ s) ⟨0, hs⟩ a = -(rootPolynomial frequency).coeff a.val := by
    rw [show generator frequency ^ s = generator frequency ^ (s - 1) * generator frequency by
      rw [← pow_succ]; congr 1, Matrix.mul_apply]
    simp_rw [generator_pow_initial_rows frequency (s - 1) ⟨0, hs⟩ _ (by simp; omega)]
    let last : Fin s := ⟨s - 1, by omega⟩
    have heq (i : Fin s) : i.val = 0 + (s - 1) ↔ i = last :=
      ⟨fun h => Fin.ext (by simpa [last] using h), fun h => by simp [h, last]⟩
    simp only [heq, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    simp [generator, last, show ¬s - 1 + 1 < s by omega]
  rw [pow_add, Matrix.mul_apply]
  simp only [hfirst]

theorem generator_pow_firstRow_tail_mulVec_bound {s : ℕ} (hs : 0 < s)
    (frequency a : Fin s → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hradius : r ≤ 1 / (2 * (s : ℝ))) (hfrequency : ‖frequency‖ ≤ r) (k : ℕ) :
    ‖(generator frequency ^ (s + k)).mulVec a ⟨0, hs⟩‖ ≤
      2 * (s : ℝ) * r * ‖a‖ := by
  letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  have heq : (generator frequency ^ (s + k)).mulVec a ⟨0, hs⟩ =
      ∑ i : Fin s, -(rootPolynomial frequency).coeff i.val *
        ((generator frequency ^ k).mulVec a i) := by
    simp only [Matrix.mulVec, dotProduct, generator_pow_firstRow_tail hs]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, mul_assoc]
  have hpow : ‖generator frequency ^ k‖ ≤ 1 := by
    exact (norm_pow_le _ _).trans (by
      simpa using pow_le_pow_left₀ (norm_nonneg _) (generator_norm_le_one hs frequency hr hradius hfrequency) k)
  have hvec : ‖(generator frequency ^ k).mulVec a‖ ≤ ‖a‖ := by
    exact (Matrix.linfty_opNorm_mulVec _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right hpow (norm_nonneg a))
  rw [heq]
  calc
    _ ≤ ∑ i : Fin s, ‖-(rootPolynomial frequency).coeff i.val *
        ((generator frequency ^ k).mulVec a i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin s, ‖(rootPolynomial frequency).coeff i.val‖ * ‖a‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, norm_neg]
      exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ i).trans hvec) (norm_nonneg _)
    _ = (∑ i : Fin s, ‖(rootPolynomial frequency).coeff i.val‖) * ‖a‖ :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * (s : ℝ) * r * ‖a‖ := by
      exact mul_le_mul_of_nonneg_right
        (rootPolynomial_lower_coefficient_mass_linear hs frequency hr hradius hfrequency)
        (norm_nonneg _)

def firstRowFunctional {s : ℕ} (hs : 0 < s) (a : Fin s → ℂ) :
    Matrix (Fin s) (Fin s) ℂ →ₗ[ℂ] ℂ where
  toFun A := A.mulVec a ⟨0, hs⟩
  map_add' A B := by simp [Matrix.add_mulVec]
  map_smul' c A := by simp [Matrix.smul_mulVec]

/-- A scalar factorial tail is bounded using `(k+j)! ≥ k! j!`. -/
theorem factorial_tail_bound (k : ℕ) :
    ∑' j : ℕ, ((k + j).factorial : ℝ)⁻¹ ≤ Real.exp 1 / (k.factorial : ℝ) := by
  have hbase : Summable (fun j : ℕ => (j.factorial : ℝ)⁻¹) := by
    simpa using NormedSpace.expSeries_summable' (𝕂 := ℝ) (1 : ℝ)
  have hmajor : Summable (fun j : ℕ => (k.factorial : ℝ)⁻¹ * (j.factorial : ℝ)⁻¹) :=
    hbase.mul_left _
  have hterm (j : ℕ) : ((k + j).factorial : ℝ)⁻¹ ≤
      (k.factorial : ℝ)⁻¹ * (j.factorial : ℝ)⁻¹ := by
    rw [← _root_.mul_inv_rev, mul_comm (j.factorial : ℝ) (k.factorial : ℝ)]
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (k + j))
      (Nat.factorial_mul_factorial_dvd_factorial_add k j)
  have htail : Summable (fun j : ℕ => ((k + j).factorial : ℝ)⁻¹) :=
    hmajor.of_nonneg_of_le (fun _ => by positivity) hterm
  calc
    _ ≤ ∑' j : ℕ, (k.factorial : ℝ)⁻¹ * (j.factorial : ℝ)⁻¹ :=
      Summable.tsum_le_tsum hterm htail hmajor
    _ = Real.exp 1 / (k.factorial : ℝ) := by
      rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
      simp only [one_pow, smul_eq_mul, mul_one, div_eq_mul_inv, mul_comm]

theorem factorial_tail_bound_rational (k : ℕ) (hk : 0 < k) :
    ∑' j : ℕ, ((k + j).factorial : ℝ)⁻¹ ≤
      ((k : ℝ) + 1) / ((k : ℝ) * (k.factorial : ℝ)) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  let q : ℝ := ((k : ℝ) + 1)⁻¹
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    dsimp [q]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hgeo : Summable (fun j : ℕ => q ^ j) := summable_geometric_of_norm_lt_one hq1
  have hmajor := hgeo.mul_left (k.factorial : ℝ)⁻¹
  have hterm (j : ℕ) : ((k + j).factorial : ℝ)⁻¹ ≤ (k.factorial : ℝ)⁻¹ * q ^ j := by
    have hfac : (k.factorial : ℝ) * ((k : ℝ) + 1) ^ j ≤ ((k + j).factorial : ℝ) := by
      exact_mod_cast (Nat.factorial_mul_pow_le_factorial (m := k) (n := j))
    calc
      _ ≤ ((k.factorial : ℝ) * ((k : ℝ) + 1) ^ j)⁻¹ := inv_anti₀ (by positivity) hfac
      _ = _ := by simp only [q, _root_.mul_inv_rev, inv_pow]; ring
  have htail := hmajor.of_nonneg_of_le (fun _ => by positivity) hterm
  calc
    _ ≤ ∑' j, (k.factorial : ℝ)⁻¹ * q ^ j := Summable.tsum_le_tsum hterm htail hmajor
    _ = (k.factorial : ℝ)⁻¹ * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq1]
    _ = _ := by
      dsimp [q]
      field_simp [ne_of_gt hkR]
      ring

theorem norm_tsum_factorial_of_initial_zero_rational (f : ℕ → ℂ) (hf : Summable f)
    (k : ℕ) (hk : 0 < k) {D : ℝ} (hD : 0 ≤ D)
    (hzero : ∀ n < k, f n = 0)
    (hbound : ∀ j, ‖f (j + k)‖ ≤ D * ((k + j).factorial : ℝ)⁻¹) :
    ‖∑' n, f n‖ ≤ D * ((k : ℝ) + 1) / ((k : ℝ) * (k.factorial : ℝ)) := by
  have hsum : ∑ n ∈ Finset.range k, f n = 0 :=
    Finset.sum_eq_zero fun n hn => hzero n (Finset.mem_range.mp hn)
  have heq := hf.sum_add_tsum_nat_add k
  rw [hsum, zero_add] at heq
  have hbase : Summable (fun j : ℕ => (j.factorial : ℝ)⁻¹) := by
    simpa using NormedSpace.expSeries_summable' (𝕂 := ℝ) (1 : ℝ)
  have htail : Summable (fun j : ℕ => ((k + j).factorial : ℝ)⁻¹) :=
    hbase.comp_injective (i := fun j : ℕ => k + j) (fun _ _ h => Nat.add_left_cancel h)
  have hmajor := htail.mul_left D
  have hnorm := hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  rw [← heq]
  calc
    _ ≤ ∑' j, ‖f (j + k)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j, D * ((k + j).factorial : ℝ)⁻¹ :=
      Summable.tsum_le_tsum hbound hnorm hmajor
    _ = D * (∑' j, ((k + j).factorial : ℝ)⁻¹) := tsum_mul_left
    _ ≤ D * (((k : ℝ) + 1) / ((k : ℝ) * (k.factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left (factorial_tail_bound_rational k hk) hD
    _ = _ := by ring

/-- Summing a series which vanishes below `k` and has a uniform numerator
bound retains the factorial gain of the first nonzero term. -/
theorem norm_tsum_factorial_of_initial_zero (f : ℕ → ℂ) (hf : Summable f)
    (k : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hzero : ∀ n < k, f n = 0)
    (hbound : ∀ j, ‖f (j + k)‖ ≤ D * ((k + j).factorial : ℝ)⁻¹) :
    ‖∑' n, f n‖ ≤ D * Real.exp 1 / (k.factorial : ℝ) := by
  have hsum : ∑ n ∈ Finset.range k, f n = 0 :=
    Finset.sum_eq_zero fun n hn => hzero n (Finset.mem_range.mp hn)
  have heq := hf.sum_add_tsum_nat_add k
  rw [hsum, zero_add] at heq
  have hbase : Summable (fun j : ℕ => (j.factorial : ℝ)⁻¹) := by
    simpa using NormedSpace.expSeries_summable' (𝕂 := ℝ) (1 : ℝ)
  have htail : Summable (fun j : ℕ => ((k + j).factorial : ℝ)⁻¹) := by
    exact hbase.comp_injective (i := fun j : ℕ => k + j) (fun _ _ h => Nat.add_left_cancel h)
  have hmajor := htail.mul_left D
  have hnorm := hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  rw [← heq]
  calc
    _ ≤ ∑' j, ‖f (j + k)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j, D * ((k + j).factorial : ℝ)⁻¹ :=
      Summable.tsum_le_tsum hbound hnorm hmajor
    _ = D * (∑' j, ((k + j).factorial : ℝ)⁻¹) := tsum_mul_left
    _ ≤ D * (Real.exp 1 / (k.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (factorial_tail_bound k) hD
    _ = _ := by ring

theorem norm_pow_sub_pow_le {E : Type*} [NormedRing E] [NormOneClass E]
    (A B : E) {K : ℝ} (hK : 0 ≤ K) (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ K) :
    ∀ n : ℕ, ‖A ^ (n + 1) - B ^ (n + 1)‖ ≤
      (n + 1 : ℝ) * K ^ n * ‖A - B‖ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : ‖A ^ (n + 1)‖ ≤ K ^ (n + 1) :=
      (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hA _)
    have hid : A ^ (n + 1 + 1) - B ^ (n + 1 + 1) =
        A ^ (n + 1) * (A - B) + (A ^ (n + 1) - B ^ (n + 1)) * B := by
      simp only [pow_succ, mul_sub, sub_mul]
      noncomm_ring
    rw [hid]
    calc
      _ ≤ ‖A ^ (n + 1)‖ * ‖A - B‖ +
          ‖A ^ (n + 1) - B ^ (n + 1)‖ * ‖B‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ K ^ (n + 1) * ‖A - B‖ +
          ((n + 1 : ℝ) * K ^ n * ‖A - B‖) * K := by gcongr
      _ = ((n + 1 : ℕ) + 1 : ℝ) * K ^ (n + 1) * ‖A - B‖ := by
        push_cast
        rw [pow_succ]
        ring

theorem norm_exp_le_exp {s : ℕ} (hs : 0 < s)
    (A : Matrix (Fin s) (Fin s) ℂ) :
    ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  have hnorm := NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) A
  have hreal := NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖A‖
  rw [NormedSpace.exp_eq_tsum ℂ, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  apply (norm_tsum_le_tsum_norm hnorm).trans
  apply Summable.tsum_le_tsum _ hnorm hreal
  intro n
  simp only [norm_smul, norm_inv, Complex.norm_natCast, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le A n) (by positivity)

theorem norm_exp_sub_exp_le {s : ℕ} (hs : 0 < s)
    (A B : Matrix (Fin s) (Fin s) ℂ) {K : ℝ}
    (hK : 0 ≤ K) (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ K) :
    ‖NormedSpace.exp A - NormedSpace.exp B‖ ≤ ‖A - B‖ * Real.exp K := by
  letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  let f := fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (A ^ n - B ^ n)
  have hf : Summable f := by
    simpa only [f, smul_sub] using
      (NormedSpace.expSeries_summable' (𝕂 := ℂ) A).sub
        (NormedSpace.expSeries_summable' (𝕂 := ℂ) B)
  have heq : NormedSpace.exp A - NormedSpace.exp B = ∑' n, f (n + 1) := by
    rw [NormedSpace.exp_eq_tsum ℂ,
      ← (NormedSpace.expSeries_summable' (𝕂 := ℂ) A).tsum_sub
        (NormedSpace.expSeries_summable' (𝕂 := ℂ) B)]
    simp_rw [← smul_sub]
    change (∑' n, f n) = _
    rw [hf.tsum_eq_zero_add]
    simp [f]
  have hg : Summable (fun n : ℕ => ‖A - B‖ * ((n.factorial : ℝ)⁻¹ * K ^ n)) :=
    (NormedSpace.expSeries_summable' (𝕂 := ℝ) K).mul_left ‖A - B‖
  have hterm (n : ℕ) : ‖f (n + 1)‖ ≤
      ‖A - B‖ * ((n.factorial : ℝ)⁻¹ * K ^ n) := by
    dsimp [f]
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ ((n + 1).factorial : ℝ)⁻¹ *
          ((n + 1 : ℝ) * K ^ n * ‖A - B‖) :=
        mul_le_mul_of_nonneg_left (norm_pow_sub_pow_le A B hK hA hB n) (by positivity)
      _ = _ := by
        rw [Nat.factorial_succ, Nat.cast_mul]
        have hn : (n + 1 : ℝ) ≠ 0 := by positivity
        have hf : (n.factorial : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
  have hnf : Summable (fun n => ‖f (n + 1)‖) :=
    hg.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  rw [heq]
  calc
    _ ≤ ∑' n, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hnf
    _ ≤ ∑' n, ‖A - B‖ * ((n.factorial : ℝ)⁻¹ * K ^ n) :=
      Summable.tsum_le_tsum hterm hnf hg
    _ = ‖A - B‖ * Real.exp K := by
      rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
      rfl

theorem firstRow_power_error_initial_zero {s : ℕ} (hs : 0 < s)
    (frequency a : Fin s → ℂ) (n : ℕ) (hn : n < s) :
    (generator frequency ^ n - jetShift s ^ n).mulVec a ⟨0, hs⟩ = 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply,
    generator_pow_firstRow_eq_shift hs frequency n hn, sub_self, zero_mul, Finset.sum_const_zero]

theorem firstRow_power_error_tail_bound {s : ℕ} (hs : 0 < s)
    (frequency a : Fin s → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hradius : r ≤ 1 / (2 * (s : ℝ))) (hfrequency : ‖frequency‖ ≤ r) (j : ℕ) :
    ‖(generator frequency ^ (s + j) - jetShift s ^ (s + j)).mulVec a ⟨0, hs⟩‖ ≤
      2 * (s : ℝ) * r * ‖a‖ := by
  rw [jetShift_pow_eq_zero _ (by omega), sub_zero]
  exact generator_pow_firstRow_tail_mulVec_bound hs frequency a hr hradius hfrequency j

/-- Direct signal-level approximation, without the dimension loss of
entrywise estimates. The factorial gain comes from the first `s` powers. -/
theorem companion_signal_error_bound {s : ℕ} (hs : 0 < s)
    (frequency a : Fin s → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hradius : r ≤ 1 / (2 * (s : ℝ))) (hfrequency : ‖frequency‖ ≤ r)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(NormedSpace.exp ((t : ℂ) • generator frequency)).mulVec a ⟨0, hs⟩ -
      jetPolynomialSignal a t‖ ≤
        (2 * ((s : ℝ) + 1) * r / (s.factorial : ℝ)) * ‖a‖ := by
  let L := (firstRowFunctional hs a).toContinuousLinearMap
  let F := fun n : ℕ => (n.factorial : ℂ)⁻¹ •
    (((t : ℂ) • generator frequency) ^ n - ((t : ℂ) • jetShift s) ^ n)
  have hF : Summable F := by
    simpa only [F, smul_sub] using
      (NormedSpace.expSeries_summable' (𝕂 := ℂ) ((t : ℂ) • generator frequency)).sub
        (NormedSpace.expSeries_summable' (𝕂 := ℂ) ((t : ℂ) • jetShift s))
  let f := fun n : ℕ => L (F n)
  have hf : Summable f := hF.map L L.continuous
  have heq (n : ℕ) : f n = (n.factorial : ℂ)⁻¹ * (t : ℂ) ^ n *
      (generator frequency ^ n - jetShift s ^ n).mulVec a ⟨0, hs⟩ := by
    change ((F n).mulVec a ⟨0, hs⟩) = _
    simp only [F, smul_pow,
      ← smul_sub, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hnormt : ‖(t : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hzero : ∀ n < s, f n = 0 := by
    intro n hn
    rw [heq, firstRow_power_error_initial_zero hs frequency a n hn, mul_zero]
  have hbound (j : ℕ) : ‖f (j + s)‖ ≤
      (2 * (s : ℝ) * r * ‖a‖) * ((s + j).factorial : ℝ)⁻¹ := by
    rw [heq, norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
    have ht_pow : ‖(t : ℂ)‖ ^ (j + s) ≤ 1 := by
      simpa using pow_le_pow_left₀ (norm_nonneg _) hnormt (j + s)
    have htail := firstRow_power_error_tail_bound hs frequency a hr hradius hfrequency j
    rw [Nat.add_comm j s]
    calc
      _ ≤ ((s + j).factorial : ℝ)⁻¹ * 1 * (2 * (s : ℝ) * r * ‖a‖) := by
        gcongr
        simpa only [Nat.add_comm] using ht_pow
      _ = _ := by ring
  have h := norm_tsum_factorial_of_initial_zero_rational f hf s hs (by positivity) hzero hbound
  have hsum := L.hasSum
    ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) • generator frequency)).sub
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) • jetShift s)))
  have hsum' : (∑' n, f n) =
      (NormedSpace.exp ((t : ℂ) • generator frequency)).mulVec a ⟨0, hs⟩ -
      jetPolynomialSignal a t := by
    have h := hsum.tsum_eq
    change (∑' n, L (((n.factorial : ℂ)⁻¹ • ((t : ℂ) • generator frequency) ^ n) -
      ((n.factorial : ℂ)⁻¹ • ((t : ℂ) • jetShift s) ^ n))) = _ at h
    simpa only [f, F, L, LinearMap.coe_toContinuousLinearMap',
      firstRowFunctional, LinearMap.coe_mk, AddHom.coe_mk, smul_sub,
      Matrix.sub_mulVec, Pi.sub_apply, ← generator_zero,
      zero_evolution_eq_jetPolynomial, jetPolynomialSignal] using h
  rw [hsum'] at h
  have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  convert h using 1
  field_simp

/-- The differentiated first-row approximation retains `(s-1)!`. -/
theorem companion_exp_derivative_error_bound {s : ℕ} (hs : 0 < s)
    (frequency a : Fin s → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hradius : r ≤ 1 / (2 * (s : ℝ))) (hfrequency : ‖frequency‖ ≤ r)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(NormedSpace.exp ((t : ℂ) • generator frequency) * generator frequency -
        NormedSpace.exp ((t : ℂ) • jetShift s) * jetShift s).mulVec a ⟨0, hs⟩‖ ≤
      (2 * (s : ℝ) * r * Real.exp 1 / ((s - 1).factorial : ℝ)) * ‖a‖ := by
  let L := (firstRowFunctional hs a).toContinuousLinearMap
  let F := fun n : ℕ => (n.factorial : ℂ)⁻¹ •
    (((t : ℂ) • generator frequency) ^ n * generator frequency -
      ((t : ℂ) • jetShift s) ^ n * jetShift s)
  have hsumF : HasSum F
      (NormedSpace.exp ((t : ℂ) • generator frequency) * generator frequency -
        NormedSpace.exp ((t : ℂ) • jetShift s) * jetShift s) := by
    simpa only [F, smul_sub, Matrix.smul_mul] using
      ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
        ((t : ℂ) • generator frequency)).mul_right (generator frequency)).sub
      ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
        ((t : ℂ) • jetShift s)).mul_right (jetShift s))
  let f := fun n : ℕ => L (F n)
  have hf : Summable f := hsumF.summable.map L L.continuous
  have heq (n : ℕ) : f n = (n.factorial : ℂ)⁻¹ * (t : ℂ) ^ n *
      (generator frequency ^ (n + 1) - jetShift s ^ (n + 1)).mulVec a ⟨0, hs⟩ := by
    change ((F n).mulVec a ⟨0, hs⟩) = _
    simp only [F, smul_pow,
      Matrix.smul_mul, ← smul_sub, ← pow_succ,
      Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hnormt : ‖(t : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hzero : ∀ n < s - 1, f n = 0 := by
    intro n hn
    rw [heq, firstRow_power_error_initial_zero hs frequency a (n + 1) (by omega), mul_zero]
  have hbound (j : ℕ) : ‖f (j + (s - 1))‖ ≤
      (2 * (s : ℝ) * r * ‖a‖) * (((s - 1) + j).factorial : ℝ)⁻¹ := by
    rw [heq, norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
    have ht_pow : ‖(t : ℂ)‖ ^ (j + (s - 1)) ≤ 1 := by
      simpa using pow_le_pow_left₀ (norm_nonneg _) hnormt _
    have hn : j + (s - 1) + 1 = s + j := by omega
    rw [hn]
    have htail := firstRow_power_error_tail_bound hs frequency a hr hradius hfrequency j
    rw [Nat.add_comm j (s - 1)]
    calc
      _ ≤ (((s - 1) + j).factorial : ℝ)⁻¹ * 1 * (2 * (s : ℝ) * r * ‖a‖) := by
        gcongr
        simpa only [Nat.add_comm] using ht_pow
      _ = _ := by ring
  have h := norm_tsum_factorial_of_initial_zero f hf (s - 1) (by positivity) hzero hbound
  have heqsum := (L.hasSum hsumF).tsum_eq
  change (∑' n, f n) = _ at heqsum
  rw [heqsum] at h
  change ‖(NormedSpace.exp ((t : ℂ) • generator frequency) * generator frequency -
      NormedSpace.exp ((t : ℂ) • jetShift s) * jetShift s).mulVec a ⟨0, hs⟩‖ ≤ _ at h
  convert h using 1
  ring

def companionSignal {s : ℕ} (hs : 0 < s) (frequency a : Fin s → ℂ) (t : ℝ) : ℂ :=
  (NormedSpace.exp ((t : ℂ) • generator frequency)).mulVec a ⟨0, hs⟩

theorem hasDerivAt_companionSignal {s : ℕ} (hs : 0 < s)
    (frequency a : Fin s → ℂ) (t : ℝ) :
    HasDerivAt (companionSignal hs frequency a)
      ((NormedSpace.exp ((t : ℂ) • generator frequency) * generator frequency).mulVec
        a ⟨0, hs⟩) t := by
  let L := (firstRowFunctional hs a).toContinuousLinearMap
  have hm := hasDerivAt_exp_smul_const (generator frequency) (t : ℂ)
  exact (L.hasFDerivAt.comp_hasDerivAt (t : ℂ) hm).comp_ofReal

theorem companionSignal_zero_eq_jetPolynomial {s : ℕ} (hs : 0 < s) (a : Fin s → ℂ) :
    companionSignal hs (0 : Fin s → ℂ) a = jetPolynomialSignal a := by
  funext t
  exact zero_evolution_eq_jetPolynomial hs a (t : ℂ)

theorem companion_derivative_error_bound {s : ℕ} (hs : 0 < s)
    (frequency a : Fin s → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hradius : r ≤ 1 / (2 * (s : ℝ))) (hfrequency : ‖frequency‖ ≤ r)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖deriv (companionSignal hs frequency a) t - deriv (jetPolynomialSignal a) t‖ ≤
      (2 * (s : ℝ) * r * Real.exp 1 / ((s - 1).factorial : ℝ)) * ‖a‖ := by
  rw [(hasDerivAt_companionSignal hs frequency a t).deriv,
    ← companionSignal_zero_eq_jetPolynomial hs a,
    (hasDerivAt_companionSignal hs (0 : Fin s → ℂ) a t).deriv, generator_zero,
    ← Pi.sub_apply, ← Matrix.sub_mulVec]
  exact companion_exp_derivative_error_bound hs frequency a hr hradius hfrequency t ht

end
end LeanNumDetect.QuantitativeCompanionBounds
