import General.Probability.FiniteSymmetrization
import General.Probability.FiniteScalarConcentration

/-! Exponential moments and finite maximal inequalities for symmetric
Bernoulli processes. These are elementary components of multiscale chaining,
with fully explicit finite laws and no concentration assumptions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

theorem finiteAverage_pi_product {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq ι]
    (f : ι → α → ℝ) :
    finiteAverage (fun ω : ι → α => ∏ i, f i (ω i)) =
      ∏ i, finiteAverage (f i) := by
  classical
  simp only [finiteAverage, smul_eq_mul, Fintype.card_pi, Nat.cast_prod]
  rw [← Fintype.prod_sum, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]

/-- A finite Bernoulli process has the exact Euclidean subgaussian variance
proxy `∑ a_i²`, without an ambient coordinate-count factor. -/
theorem finiteBernoulli_exp_sum_le {m : ℕ} (a : Fin m → ℝ) (θ : ℝ) :
    finiteAverage (fun σ : Fin m → Bool =>
      Real.exp (θ * ∑ i, finiteBernoulliSign (σ i) * a i)) ≤
      Real.exp (θ ^ 2 * (∑ i, a i ^ 2) / 2) := by
  have hsign : ∀ b, |finiteBernoulliSign b| ≤ 1 := by
    intro b
    cases b <;> norm_num [finiteBernoulliSign]
  have hzero : ∑ b : Bool, finiteBernoulliSign b = 0 := by
    simp [finiteBernoulliSign]
  have hsingle (i : Fin m) :
      finiteAverage (fun b : Bool => Real.exp (θ * (finiteBernoulliSign b * a i))) ≤
        Real.exp ((θ * a i) ^ 2 / 2) := by
    convert finiteAverage_exp_mul_le finiteBernoulliSign hsign hzero (θ * a i) using 1
    apply finiteAverage_congr
    intro b
    congr 1
    ring
  calc
    _ = ∏ i, finiteAverage (fun b : Bool =>
        Real.exp (θ * (finiteBernoulliSign b * a i))) := by
      simp_rw [Finset.mul_sum, Real.exp_sum]
      exact finiteAverage_pi_product (ι := Fin m) (α := Bool)
        (fun i b => Real.exp (θ * (finiteBernoulliSign b * a i)))
    _ ≤ ∏ i, Real.exp ((θ * a i) ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro i _
        have h := finiteAverage_mono (fun b : Bool =>
          Real.exp_nonneg (θ * (finiteBernoulliSign b * a i)))
        simpa only [finiteAverage_const] using h
      · intro i _
        exact hsingle i
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_div]

/-- Maximum absolute value over a finite, nonempty process index set. -/
noncomputable def finiteProcessAbsoluteMaximum {α J : Type*} [Fintype J]
    (Z : J → α → ℝ) (ω : α) : ℝ := sSup (Set.range fun j => |Z j ω|)

theorem abs_process_le_absoluteMaximum {α J : Type*} [Fintype J]
    (Z : J → α → ℝ) (j : J) (ω : α) :
    |Z j ω| ≤ finiteProcessAbsoluteMaximum Z ω :=
  le_csSup (Set.finite_range _).bddAbove ⟨j, rfl⟩

theorem finiteProcessAbsoluteMaximum_nonneg {α J : Type*}
    [Fintype J] [Nonempty J] (Z : J → α → ℝ) (ω : α) :
    0 ≤ finiteProcessAbsoluteMaximum Z ω :=
  (abs_nonneg (Z (Classical.choice inferInstance) ω)).trans
    (abs_process_le_absoluteMaximum Z _ ω)

theorem exp_absoluteMaximum_le_sum {α J : Type*} [Fintype J] [Nonempty J]
    (Z : J → α → ℝ) (ω : α) (θ : ℝ) :
    Real.exp (θ * finiteProcessAbsoluteMaximum Z ω) ≤
      ∑ j, (Real.exp (θ * Z j ω) + Real.exp (-(θ * Z j ω))) := by
  obtain ⟨j, hj⟩ := (Set.range_nonempty (fun j => |Z j ω|)).csSup_mem
    (Set.finite_range _)
  change Real.exp (θ * sSup (Set.range fun j => |Z j ω|)) ≤ _
  rw [← hj]
  have hone : Real.exp (θ * |Z j ω|) ≤
      Real.exp (θ * Z j ω) + Real.exp (-(θ * Z j ω)) := by
    by_cases hz : 0 ≤ Z j ω
    · rw [abs_of_nonneg hz]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_neg (lt_of_not_ge hz), mul_neg]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  have hsum : Real.exp (θ * Z j ω) + Real.exp (-(θ * Z j ω)) ≤
      ∑ l, (Real.exp (θ * Z l ω) + Real.exp (-(θ * Z l ω))) :=
    Finset.single_le_sum
      (fun l _ => add_nonneg (Real.exp_nonneg (θ * Z l ω))
        (Real.exp_nonneg (-(θ * Z l ω)))) (Finset.mem_univ j)
  exact hone.trans hsum

/-- The exponential maximal inequality for any finite nonempty process whose
positive and negative exponential moments share a common bound. -/
theorem finiteProcess_absoluteMaximum_exp_bound
    {α J : Type*} [Fintype α] [Fintype J] [Nonempty J]
    (Z : J → α → ℝ) (θ V : ℝ)
    (hplus : ∀ j, finiteAverage (fun ω => Real.exp (θ * Z j ω)) ≤ Real.exp V)
    (hminus : ∀ j, finiteAverage (fun ω => Real.exp (-(θ * Z j ω))) ≤ Real.exp V) :
    finiteAverage (fun ω => Real.exp (θ * finiteProcessAbsoluteMaximum Z ω)) ≤
      2 * (Fintype.card J : ℝ) * Real.exp V := by
  calc
    _ ≤ finiteAverage (fun ω =>
        ∑ j, (Real.exp (θ * Z j ω) + Real.exp (-(θ * Z j ω)))) :=
      finiteAverage_mono (fun ω => exp_absoluteMaximum_le_sum Z ω θ)
    _ = ∑ j, (finiteAverage (fun ω => Real.exp (θ * Z j ω)) +
        finiteAverage (fun ω => Real.exp (-(θ * Z j ω)))) := by
      rw [finiteAverage_sum]
      simp only [finiteAverage_add]
    _ ≤ ∑ _j : J, (Real.exp V + Real.exp V) :=
      Finset.sum_le_sum fun j _ => add_le_add (hplus j) (hminus j)
    _ = _ := by simp; ring

/-- The logarithmic expected-maximum estimate, with a freely chosen positive
Laplace parameter. This version is convenient at every chaining scale. -/
theorem finiteProcess_absoluteMaximum_expectation_bound
    {α J : Type*} [Fintype α] [Nonempty α] [Fintype J] [Nonempty J]
    (Z : J → α → ℝ) {θ V : ℝ} (hθ : 0 < θ)
    (hplus : ∀ j, finiteAverage (fun ω => Real.exp (θ * Z j ω)) ≤ Real.exp V)
    (hminus : ∀ j, finiteAverage (fun ω => Real.exp (-(θ * Z j ω))) ≤ Real.exp V) :
    finiteAverage (finiteProcessAbsoluteMaximum Z) ≤
      (Real.log (2 * (Fintype.card J : ℝ)) + V) / θ := by
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => Real.exp (θ * x)) := by
    simpa [Function.comp_def, smul_eq_mul] using
      convexOn_exp.comp_linearMap (θ • LinearMap.id (R := ℝ) (M := ℝ))
  have hexp := (convex_finiteAverage_le hconv (finiteProcessAbsoluteMaximum Z)).trans
    (finiteProcess_absoluteMaximum_exp_bound Z θ V hplus hminus)
  have hc : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  have hlog := (Real.le_log_iff_exp_le (by positivity :
    0 < 2 * (Fintype.card J : ℝ) * Real.exp V)).mpr hexp
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hlog
  exact (le_div_iff₀ hθ).mpr (by simpa only [mul_comm] using hlog)

/-- Bernoulli-process maximal inequality with its exact row-coefficient
Euclidean variance bound and logarithmic process-cardinality dependence. -/
theorem finiteBernoulli_absoluteMaximum_expectation_bound
    {J : Type*} [Fintype J] [Nonempty J] {m : ℕ}
    (a : J → Fin m → ℝ) {θ V : ℝ} (hθ : 0 < θ)
    (hvariance : ∀ j, ∑ i, a j i ^ 2 ≤ V) :
    finiteAverage (finiteProcessAbsoluteMaximum
      (fun j (σ : Fin m → Bool) => ∑ i, finiteBernoulliSign (σ i) * a j i)) ≤
      (Real.log (2 * (Fintype.card J : ℝ)) + θ ^ 2 * V / 2) / θ := by
  apply finiteProcess_absoluteMaximum_expectation_bound _ hθ
  · intro j
    exact (finiteBernoulli_exp_sum_le (a j) θ).trans
      (Real.exp_le_exp.mpr (by gcongr; exact hvariance j))
  · intro j
    have h := finiteBernoulli_exp_sum_le (a j) (-θ)
    simp only [neg_mul, neg_sq] at h
    exact h.trans (Real.exp_le_exp.mpr (by gcongr; exact hvariance j))

/-- Optimizing the Laplace parameter yields the usual square-root logarithmic
maximal inequality, including the zero-variance case. -/
theorem finiteBernoulli_absoluteMaximum_expectation_sqrt_bound
    {J : Type*} [Fintype J] [Nonempty J] {m : ℕ}
    (a : J → Fin m → ℝ) {V : ℝ}
    (hvariance : ∀ j, ∑ i, a j i ^ 2 ≤ V) :
    finiteAverage (finiteProcessAbsoluteMaximum
      (fun j (σ : Fin m → Bool) => ∑ i, finiteBernoulliSign (σ i) * a j i)) ≤
      Real.sqrt (2 * V * Real.log (2 * (Fintype.card J : ℝ))) := by
  classical
  have hV : 0 ≤ V := by
    exact (Finset.sum_nonneg fun i _ => sq_nonneg (a (Classical.choice inferInstance) i)).trans
      (hvariance (Classical.choice inferInstance))
  by_cases hzero : V = 0
  · have ha : ∀ j i, a j i = 0 := by
      intro j i
      have hi : a j i ^ 2 ≤ V :=
        (Finset.single_le_sum (fun l _ => sq_nonneg (a j l)) (Finset.mem_univ i)).trans
          (hvariance j)
      rw [hzero] at hi
      nlinarith [sq_nonneg (a j i)]
    simp only [ha, mul_zero, Finset.sum_const_zero, hzero, mul_zero,
      zero_mul, Real.sqrt_zero]
    change finiteAverage (fun _ : Fin m → Bool =>
      sSup (Set.range (fun _ : J => |(0 : ℝ)|))) ≤ 0
    simp [Set.range_const, finiteAverage_const]
  have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hzero)
  let L := Real.log (2 * (Fintype.card J : ℝ))
  have hc : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast Fintype.card_pos
  have hL : 0 < L := Real.log_pos (by nlinarith)
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.mpr hVpos
  have hsL : 0 < Real.sqrt (2 * L) := Real.sqrt_pos.mpr (by positivity)
  let θ := Real.sqrt (2 * L) / Real.sqrt V
  have hθ : 0 < θ := div_pos hsL hsV
  have hVsq := Real.sq_sqrt hV
  have hLsq := Real.sq_sqrt (show 0 ≤ 2 * L by positivity)
  have hparam : θ ^ 2 * V / 2 = L := by
    dsimp [θ]
    rw [div_pow, hLsq, hVsq]
    field_simp
  calc
    _ ≤ (L + θ ^ 2 * V / 2) / θ :=
      finiteBernoulli_absoluteMaximum_expectation_bound a hθ hvariance
    _ = Real.sqrt V * Real.sqrt (2 * L) := by
      rw [hparam]
      dsimp [θ]
      field_simp
      nlinarith [Real.sq_sqrt (show 0 ≤ L * 2 by positivity)]
    _ = _ := by
      rw [← Real.sqrt_mul hV]
      congr 1
      dsimp [L]
      ring

/-- A finite Bernoulli process satisfies a Gaussian maximum tail with only
the number of process indices in the prefactor. -/
theorem finiteBernoulli_absoluteMaximum_probability_le
    {J : Type*} [Fintype J] [Nonempty J] {m : ℕ}
    (a : J → Fin m → ℝ) {V u : ℝ} (hV : 0 < V) (hu : 0 < u)
    (hvariance : ∀ j, ∑ i, a j i ^ 2 ≤ V) :
    probability (fun σ : Fin m → Bool => u < finiteProcessAbsoluteMaximum
      (fun j σ => ∑ i, finiteBernoulliSign (σ i) * a j i) σ) ≤
      2 * (Fintype.card J : ℝ) * Real.exp (-(u ^ 2 / (2 * V))) := by
  let Z := fun j (σ : Fin m → Bool) => ∑ i, finiteBernoulliSign (σ i) * a j i
  let θ := u / V
  have hθ : 0 < θ := div_pos hu hV
  have hplus (j : J) : finiteAverage (fun σ => Real.exp (θ * Z j σ)) ≤
      Real.exp (θ ^ 2 * V / 2) :=
    (finiteBernoulli_exp_sum_le (a j) θ).trans
      (Real.exp_le_exp.mpr (by gcongr; exact hvariance j))
  have hminus (j : J) : finiteAverage (fun σ => Real.exp (-(θ * Z j σ))) ≤
      Real.exp (θ ^ 2 * V / 2) := by
    have h := finiteBernoulli_exp_sum_le (a j) (-θ)
    simp only [neg_mul, neg_sq] at h
    exact h.trans (Real.exp_le_exp.mpr (by gcongr; exact hvariance j))
  have h := probability_le_exponential_moment
    (fun σ => u < finiteProcessAbsoluteMaximum Z σ)
    (fun σ => Real.exp (θ * finiteProcessAbsoluteMaximum Z σ))
    (q := θ * u) (b := θ ^ 2 * V / 2) (D := 2 * (Fintype.card J : ℝ))
    (fun _ => Real.exp_nonneg _) (fun σ hσ =>
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ.le hθ.le))
    (finiteProcess_absoluteMaximum_exp_bound Z θ _ hplus hminus)
  convert h using 1
  congr 2
  dsimp [θ]
  field_simp
  ring

end LeanNumDetect.FiniteMatrixSampling
