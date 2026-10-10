import General.MatrixAnalysis.CappedWeightMap

/-! A finite monotone covariance iteration produces bounded row weights once
its determinant has a quantitative floor. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.CappedWeightIteration

open FiniteMatrixSampling
noncomputable section

def cappedGramSequence {N d : ℕ} (f : Fin N → EuclideanSpace ℂ (Fin d))
    (R : ℝ) : ℕ → Matrix (Fin d) (Fin d) ℂ
  | 0 => 1
  | k+1 => cappedGram f R (cappedGramSequence f R k)

@[simp] theorem cappedGramSequence_zero {N d : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin d)) (R : ℝ) : cappedGramSequence f R 0 = 1 := rfl

@[simp] theorem cappedGramSequence_succ {N d : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin d)) (R : ℝ) (k : ℕ) :
    cappedGramSequence f R (k+1) = cappedGram f R (cappedGramSequence f R k) := rfl

theorem cappedGramSequence_posDef {N d : ℕ} (hN : 0 < N)
    (f : Fin N → EuclideanSpace ℂ (Fin d)) {R : ℝ} (hR : 0 < R)
    (hfull : mean (framePopulation f) = 1) (k : ℕ) : (cappedGramSequence f R k).PosDef := by
  induction k with
  | zero => exact Matrix.PosDef.one
  | succ k ih =>
    exact cappedGram_posDef hN f hR ih (by rw [hfull]; exact Matrix.PosDef.one)

theorem cappedGramSequence_step_le {N d : ℕ} (hN : 0 < N)
    (f : Fin N → EuclideanSpace ℂ (Fin d)) {R : ℝ} (hR : 0 < R)
    (hfull : mean (framePopulation f) = 1) (k : ℕ)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadratic (cappedGramSequence f R (k+1)) x ≤ quadratic (cappedGramSequence f R k) x := by
  induction k generalizing x with
  | zero =>
    have h := cappedGram_le_full f hR (Matrix.PosDef.one : (1 : Matrix (Fin d) (Fin d) ℂ).PosDef) x
    simpa only [hfull, cappedGramSequence] using h
  | succ k ih =>
    exact cappedGram_monotone f hR (cappedGramSequence_posDef hN f hR hfull (k+1))
      (cappedGramSequence_posDef hN f hR hfull k) ih x

theorem cappedGramSequence_le_identity {N d : ℕ} (hN : 0 < N)
    (f : Fin N → EuclideanSpace ℂ (Fin d)) {R : ℝ} (hR : 0 < R)
    (hfull : mean (framePopulation f) = 1) (k : ℕ)
    (x : EuclideanSpace ℂ (Fin d)) : quadratic (cappedGramSequence f R k) x ≤ ‖x‖^2 := by
  induction k with
  | zero => simp
  | succ k ih => exact (cappedGramSequence_step_le hN f hR hfull k x).trans ih

theorem cappedEntropy_initial_bound {N d : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin d)) {R : ℝ} (hR : 0 < R)
    (hfull : mean (framePopulation f) = 1) :
    Real.log (realDet (1 : Matrix (Fin d) (Fin d) ℂ)) + (N : ℝ)⁻¹ *
      ∑ k, cappedEntropy R (quadratic (1 : Matrix (Fin d) (Fin d) ℂ)⁻¹ (f k)) ≤ (d : ℝ) := by
  have hpop : weightedPopulation (framePopulation f) (fun _ => (1 : ℝ)) = framePopulation f := by
    funext k
    simp [weightedPopulation]
  have ht := trace_mul_weightedMean f (fun _ => (1 : ℝ)) (1 : Matrix (Fin d) (Fin d) ℂ)
  rw [hpop, hfull, Matrix.one_mul] at ht
  simp only [Matrix.trace_one, Fintype.card_fin, Complex.natCast_re, one_mul] at ht
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
    (fun k _ => cappedEntropy_le hR (quadratic_nonneg Matrix.PosSemidef.one (f k)))
  have h := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg N))
  simpa only [realDet, Matrix.det_one, Complex.one_re, Real.log_one, zero_add,
    inv_one, ← ht] using h

theorem cappedGramSequence_entropy_bound {N d : ℕ} (hN : 0 < N)
    (f : Fin N → EuclideanSpace ℂ (Fin d)) {R : ℝ} (hR : 0 < R)
    (hfull : mean (framePopulation f) = 1) (k : ℕ) :
    Real.log (realDet (cappedGramSequence f R k)) + (N : ℝ)⁻¹ *
      ∑ j, cappedEntropy R (quadratic (cappedGramSequence f R k)⁻¹ (f j)) ≤ (d : ℝ) := by
  induction k with
  | zero => exact cappedEntropy_initial_bound f hR hfull
  | succ k ih =>
    exact (cappedGram_entropy_descent hN f hR (cappedGramSequence_posDef hN f hR hfull k)
      (by rw [hfull]; exact Matrix.PosDef.one)).trans ih

/-- The finite update has no limiting or minimizer assumption. A deterministic
entropy estimate supplies the determinant floor in the application. -/
theorem exists_capped_weights_of_determinant_floor {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Fin N → EuclideanSpace ℂ (Fin d)) (hfull : mean (framePopulation f) = 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hdet : ∀ k, δ ≤ realDet (cappedGramSequence f ((12/5 : ℝ)*d) k)) :
    ∃ w : Fin N → ℝ, (∀ k, 0 < w k ∧ w k ≤ 1) ∧
      (mean (weightedPopulation (framePopulation f) w)).PosDef ∧
      (∀ x : EuclideanSpace ℂ (Fin d), δ*‖x‖^2 ≤
        quadratic (mean (weightedPopulation (framePopulation f) w)) x) ∧
      (∀ k (x : EuclideanSpace ℂ (Fin d)),
        quadratic (weightedPopulation (framePopulation f) w k) x ≤
          (5/2 : ℝ)*d*quadratic (mean (weightedPopulation (framePopulation f) w)) x) := by
  have hR : (0 : ℝ) < (12/5 : ℝ)*d := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  let p := fun k => realDet (cappedGramSequence f ((12/5 : ℝ)*d) k)
  let good := fun k => ∀ x : EuclideanSpace ℂ (Fin d),
    (24/25 : ℝ)*quadratic (cappedGramSequence f ((12/5 : ℝ)*d) k) x ≤
      quadratic (cappedGramSequence f ((12/5 : ℝ)*d) (k+1)) x
  have hdrop (k : ℕ) (hk : ¬ good k) : p (k+1) ≤ (24/25 : ℝ)*p k := by
    exact (realDet_drop_of_not_relative_lower
      (cappedGramSequence_posDef hN f hR hfull k)
      (cappedGramSequence_posDef hN f hR hfull (k+1))
      (cappedGramSequence_step_le hN f hR hfull k) hk).le
  obtain ⟨k, hk⟩ := exists_nondescending_step p good (by norm_num) (by norm_num) hδ
    (by simp [p, realDet]) hdet hdrop
  let G := cappedGramSequence f ((12/5 : ℝ)*d) k
  let B := cappedGramSequence f ((12/5 : ℝ)*d) (k+1)
  have hG : G.PosDef := cappedGramSequence_posDef hN f hR hfull k
  have hB : B.PosDef := cappedGramSequence_posDef hN f hR hfull (k+1)
  refine ⟨frameMetricWeight f ((12/5 : ℝ)*d) G, fun j => frameMetricWeight_bounds f hR hG j,
    hB, ?_, ?_⟩
  · intro x
    exact quadratic_lower_of_realDet_lower hB
      (cappedGramSequence_le_identity hN f hR hfull (k+1)) (hdet (k+1)) x
  · intro j x
    have hl := capped_row_bound f hR hG j x
    have hh := hk x
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ (5/2 : ℝ)*d by positivity)
    apply hl.trans
    change ((12/5 : ℝ)*(d : ℝ))*quadratic G x ≤ (5/2 : ℝ)*d*quadratic B x
    change (5/2 : ℝ)*d*((24/25 : ℝ)*quadratic G x) ≤ (5/2 : ℝ)*d*quadratic B x at hmul
    nlinarith

end
end LeanNumDetect.CappedWeightIteration
