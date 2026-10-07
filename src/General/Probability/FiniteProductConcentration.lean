import General.Probability.FiniteScalarConcentration

/-!
# Bounded differences on a finite Boolean product

Uniform finite averages, a two-point cosh inequality, and induction over the
number of coordinates prove the exact Hoeffding bounded-differences moment
and one-sided tail bounds. No concentration result is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling
noncomputable section

/-- Oscillation when a single Boolean coordinate is changed. -/
def CoordinateOscillationBound {m : ℕ}
    (F : (Fin m → Bool) → ℝ) (b : Fin m → ℝ) : Prop :=
  ∀ i x y, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ b i

/-- The uniform Boolean average is its two-point midpoint. -/
theorem finiteAverage_bool (f : Bool → ℝ) :
    finiteAverage f = (f false + f true) / 2 := by
  simp [finiteAverage]
  ring

/-- The absolute value of a finite average is bounded by the average of
absolute values. -/
theorem abs_finiteAverage_le {α : Type*} [Fintype α] (f : α → ℝ) :
    |finiteAverage f| ≤ finiteAverage (fun x => |f x|) := by
  have hc : 0 ≤ (Fintype.card α : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  simp only [finiteAverage, smul_eq_mul, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    hc

/-- A Boolean variable centered at its midpoint has variance proxy one
quarter of the square of its range length. -/
theorem finiteAverage_bool_exp_centered_le (f : Bool → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hrange : |f false - f true| ≤ b) (θ : ℝ) :
    finiteAverage (fun x => Real.exp (θ * (f x - finiteAverage f))) ≤
      Real.exp (θ ^ 2 * b ^ 2 / 8) := by
  have hfalse : f false - finiteAverage f = -(f true - f false) / 2 := by
    rw [finiteAverage_bool]
    ring
  have htrue : f true - finiteAverage f = (f true - f false) / 2 := by
    rw [finiteAverage_bool]
    ring
  have heq : finiteAverage (fun x => Real.exp (θ * (f x - finiteAverage f))) =
      Real.cosh (θ * (f true - f false) / 2) := by
    rw [finiteAverage_bool, hfalse, htrue, Real.cosh_eq]
    congr 1
    rw [show θ * (-(f true - f false) / 2) = -(θ * (f true - f false) / 2) by ring,
      show θ * ((f true - f false) / 2) = θ * (f true - f false) / 2 by ring]
    ring
  rw [heq]
  apply (Real.cosh_le_exp_half_sq _).trans
  apply Real.exp_le_exp.mpr
  have hsq : (f true - f false) ^ 2 ≤ b ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hb).2 hrange
    rw [sq_abs] at h
    nlinarith
  have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg θ)
  nlinarith

/-- The centered exponential moment for a function of independent uniform
Boolean coordinates with prescribed coordinate oscillations. -/
theorem finiteProduct_exp_centered_le {m : ℕ}
    (b : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i)
    (F : (Fin m → Bool) → ℝ) (hF : CoordinateOscillationBound F b) (θ : ℝ) :
    finiteAverage (fun x => Real.exp (θ * (F x - finiteAverage F))) ≤
      Real.exp (θ ^ 2 * (∑ i, b i ^ 2) / 8) := by
  induction m with
  | zero =>
    let x0 : Fin 0 → Bool := fun i => Fin.elim0 i
    have heq : F = fun _ => F x0 := funext fun _ => congrArg F (Subsingleton.elim _ _)
    rw [heq]
    simp
  | succ m ih =>
    let G : (Fin m → Bool) → ℝ := fun x => finiteAverage (fun t : Bool => F (Fin.cons t x))
    let bt : Fin m → ℝ := fun i => b i.succ
    have hG : CoordinateOscillationBound G bt := by
      intro i x y hxy
      have hpair (t : Bool) : |F (Fin.cons t x) - F (Fin.cons t y)| ≤ b i.succ := by
        apply hF i.succ
        intro j hj
        cases j using Fin.cases with
        | zero => simp
        | succ j =>
          simp only [Fin.cons_succ]
          apply hxy j
          intro he
          exact hj (congrArg Fin.succ he)
      have heq : G x - G y = finiteAverage
          (fun t : Bool => F (Fin.cons t x) - F (Fin.cons t y)) := by
        simp only [G, finiteAverage, smul_eq_mul, Finset.sum_sub_distrib, mul_sub]
      rw [heq]
      exact (abs_finiteAverage_le _).trans
        ((finiteAverage_mono hpair).trans_eq (finiteAverage_const _))
    have hmean : finiteAverage F = finiteAverage G := by
      rw [finiteAverage_fin_succ, finiteAverage_comm]
    have hsingle (x : Fin m → Bool) :
        finiteAverage (fun t : Bool => Real.exp (θ * (F (Fin.cons t x) - G x))) ≤
          Real.exp (θ ^ 2 * b 0 ^ 2 / 8) := by
      apply finiteAverage_bool_exp_centered_le _ _ (hb 0) _ θ
      apply hF 0
      intro j hj
      cases j using Fin.cases with
      | zero => exact False.elim (hj rfl)
      | succ j => simp
    rw [finiteAverage_fin_succ, finiteAverage_comm]
    calc
      _ ≤ finiteAverage (fun x : Fin m → Bool =>
          Real.exp (θ * (G x - finiteAverage F)) * Real.exp (θ ^ 2 * b 0 ^ 2 / 8)) := by
        apply finiteAverage_mono
        intro x
        have heq : finiteAverage (fun t : Bool =>
            Real.exp (θ * (F (Fin.cons t x) - finiteAverage F))) =
            Real.exp (θ * (G x - finiteAverage F)) *
              finiteAverage (fun t : Bool => Real.exp (θ * (F (Fin.cons t x) - G x))) := by
          change _ = Real.exp (θ * (G x - finiteAverage F)) •
            finiteAverage (fun t : Bool => Real.exp (θ * (F (Fin.cons t x) - G x)))
          rw [← finiteAverage_smul]
          apply finiteAverage_congr
          intro t
          simp only [smul_eq_mul]
          rw [← Real.exp_add]
          congr 1
          ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left (hsingle x) (Real.exp_nonneg _)
      _ = Real.exp (θ ^ 2 * b 0 ^ 2 / 8) *
          finiteAverage (fun x : Fin m → Bool => Real.exp (θ * (G x - finiteAverage G))) := by
        rw [hmean]
        simpa only [smul_eq_mul, mul_comm] using finiteAverage_smul
          (Real.exp (θ ^ 2 * b 0 ^ 2 / 8))
          (fun x : Fin m → Bool => Real.exp (θ * (G x - finiteAverage G)))
      _ ≤ Real.exp (θ ^ 2 * b 0 ^ 2 / 8) *
          Real.exp (θ ^ 2 * (∑ i : Fin m, b i.succ ^ 2) / 8) := by
        exact mul_le_mul_of_nonneg_left (ih bt (fun i => hb i.succ) G hG)
          (Real.exp_nonneg _)
      _ = _ := by
        rw [← Real.exp_add, Fin.sum_univ_succ]
        congr 1
        ring

/-- One-sided bounded-differences tail under the explicit uniform finite law. -/
theorem finiteProduct_upper_probability_le {m : ℕ}
    (b : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i)
    (F : (Fin m → Bool) → ℝ) (hF : CoordinateOscillationBound F b)
    {u : ℝ} (hu : 0 < u) (hvariance : 0 < ∑ i, b i ^ 2) :
    probability (fun x => u < F x - finiteAverage F) ≤
      Real.exp (-2 * u ^ 2 / (∑ i, b i ^ 2)) := by
  let S : ℝ := ∑ i, b i ^ 2
  let θ : ℝ := 4 * u / S
  have hS : 0 < S := hvariance
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hmoment := finiteProduct_exp_centered_le b hb F hF θ
  have h := probability_le_exponential_moment
    (fun x => u < F x - finiteAverage F)
    (fun x => Real.exp (θ * (F x - finiteAverage F)))
    (q := θ * u) (b := θ ^ 2 * S / 8) (D := 1)
    (fun _ => Real.exp_nonneg _) (fun x hx => by
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_left hx.le hθ.le)) (by simpa only [one_mul] using hmoment)
  have heq : θ ^ 2 * S / 8 - θ * u = -2 * u ^ 2 / S := by
    dsimp [θ]
    field_simp
    ring
  simpa only [one_mul, heq] using h

/-- A larger positive variance budget also controls the tail. This formulation
covers the degenerate zero-oscillation case without a separate case split. -/
theorem finiteProduct_upper_probability_le_of_variance_bound {m : ℕ}
    (b : Fin m → ℝ) (hb : ∀ i, 0 ≤ b i)
    (F : (Fin m → Bool) → ℝ) (hF : CoordinateOscillationBound F b)
    {u V : ℝ} (hu : 0 < u) (hV : 0 < V) (hvariance : (∑ i, b i ^ 2) ≤ V) :
    probability (fun x => u < F x - finiteAverage F) ≤ Real.exp (-2 * u ^ 2 / V) := by
  let θ : ℝ := 4 * u / V
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hmoment : finiteAverage (fun x => Real.exp (θ * (F x - finiteAverage F))) ≤
      Real.exp (θ ^ 2 * V / 8) := by
    apply (finiteProduct_exp_centered_le b hb F hF θ).trans
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hvariance (sq_nonneg θ)) (by norm_num)
  have h := probability_le_exponential_moment
    (fun x => u < F x - finiteAverage F)
    (fun x => Real.exp (θ * (F x - finiteAverage F)))
    (q := θ * u) (b := θ ^ 2 * V / 8) (D := 1)
    (fun _ => Real.exp_nonneg _) (fun x hx => by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hx.le hθ.le) (by simpa only [one_mul] using hmoment)
  have heq : θ ^ 2 * V / 8 - θ * u = -2 * u ^ 2 / V := by
    dsimp [θ]
    field_simp
    ring
  simpa only [one_mul, heq] using h

end
end LeanNumDetect.FiniteMatrixSampling
