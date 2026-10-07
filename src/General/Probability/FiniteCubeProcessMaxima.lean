import General.Probability.FiniteProductConcentration
import General.Probability.FiniteProcessSecondMoments

/-!
# Second moments for finite families of Boolean-cube functions

The coordinate oscillations and the individual means control the squared
maximum over a finite family. In applications each member is itself a
supremum over an arbitrary coefficient class; only the deterministic
oscillation and mean estimates are needed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

/-- The squared maximum of a finite family is bounded by its uniform mean
budget and a logarithmic-cardinality bounded-differences term. -/
theorem finiteCube_absoluteMaximum_square_expectation_le
    {J : Type*} [Fintype J] [Nonempty J] {m : ℕ}
    (F : J → (Fin m → Bool) → ℝ) (b : J → Fin m → ℝ)
    (hb : ∀ j i, 0 ≤ b j i)
    (hF : ∀ j, CoordinateOscillationBound (F j) (b j))
    {B V : ℝ} (hV : 0 < V)
    (hmean : ∀ j, |finiteAverage (F j)| ≤ B)
    (hvariance : ∀ j, ∑ i, b j i ^ 2 ≤ 4 * V) :
    finiteAverage (fun σ : Fin m → Bool => finiteProcessAbsoluteMaximum F σ ^ 2) ≤
      2 * B ^ 2 + 40 * V * Real.log (2 * (Fintype.card J : ℝ)) := by
  let Z := fun j (σ : Fin m → Bool) => F j σ - finiteAverage (F j)
  have hplus (θ : ℝ) (j : J) : finiteAverage (fun σ : Fin m → Bool =>
      Real.exp (θ * Z j σ)) ≤ Real.exp (θ ^ 2 * V / 2) := by
    apply (finiteProduct_exp_centered_le (b j) (hb j) (F j) (hF j) θ).trans
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (hvariance j) (sq_nonneg θ)
    nlinarith
  have hminus (θ : ℝ) (j : J) : finiteAverage (fun σ : Fin m → Bool =>
      Real.exp (-(θ * Z j σ))) ≤ Real.exp (θ ^ 2 * V / 2) := by
    simpa only [neg_mul, neg_sq] using hplus (-θ) j
  have hcenter := finiteProcess_absoluteMaximum_square_expectation_le Z hV hplus hminus
  have hB : 0 ≤ B := (abs_nonneg _).trans (hmean (Classical.choice inferInstance))
  have hpoint (σ : Fin m → Bool) : finiteProcessAbsoluteMaximum F σ ^ 2 ≤
      2 * B ^ 2 + 2 * finiteProcessAbsoluteMaximum Z σ ^ 2 := by
    have hmax : finiteProcessAbsoluteMaximum F σ ≤ B + finiteProcessAbsoluteMaximum Z σ := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨j, rfl⟩
      dsimp only
      calc
        |F j σ| = |Z j σ + finiteAverage (F j)| := by dsimp [Z]; congr 1; ring
        _ ≤ |Z j σ| + |finiteAverage (F j)| := abs_add_le _ _
        _ ≤ finiteProcessAbsoluteMaximum Z σ + B :=
          add_le_add (abs_process_le_absoluteMaximum Z j σ) (hmean j)
        _ = _ := add_comm _ _
    have hsq := pow_le_pow_left₀ (finiteProcessAbsoluteMaximum_nonneg F σ) hmax 2
    nlinarith [sq_nonneg (B - finiteProcessAbsoluteMaximum Z σ)]
  calc
    _ ≤ finiteAverage (fun σ : Fin m → Bool =>
        2 * B ^ 2 + 2 * finiteProcessAbsoluteMaximum Z σ ^ 2) := finiteAverage_mono hpoint
    _ = 2 * B ^ 2 + 2 * finiteAverage (fun σ : Fin m → Bool =>
        finiteProcessAbsoluteMaximum Z σ ^ 2) := by
      rw [finiteAverage_add, finiteAverage_const]
      change (2 * B ^ 2 + finiteAverage (fun σ : Fin m → Bool =>
        (2 : ℝ) • finiteProcessAbsoluteMaximum Z σ ^ 2)) = _
      rw [finiteAverage_smul]
      rfl
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hcenter (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith

end LeanNumDetect.FiniteMatrixSampling
