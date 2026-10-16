import MultiTuran.Preliminaries.SegmentedGrid
import Mathlib.Tactic

/-! Exact cancellation of the geometric and scalar factors in the restriction
argument. Every volume and minimum length is the literal segmented-grid
quantity. -/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.SegmentedGrid
noncomputable section

variable {d : ℕ} (G : SegmentedGrid d)

/-- The long-block factor written as a quotient of products of square roots. -/
theorem rhoL_eq_prod_sqrt_div_sqrt_boxVolume :
    G.rhoL = (∏ q, Real.sqrt (G.coordinateMinLength q : ℝ)) /
      Real.sqrt G.boxVolume := by
  unfold rhoL
  rw [Real.sqrt_div (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))]
  rw [Real.sqrt_prod Finset.univ (fun _ _ => Nat.cast_nonneg _)]

/-- The product Nikolskii coefficient and the article's normalized restriction
factor cancel exactly, with no enlargement of a numerical constant. -/
theorem scaledRestriction_normalization {n : ℕ} (hn : 0 < n) :
    Real.sqrt G.boxVolume *
        (∏ q, Real.pi * (n : ℝ) / (2 * Real.sqrt (G.coordinateMinLength q : ℝ))) *
      ((2 / (Real.pi * (n : ℝ))) ^ d * G.rhoL) = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hpi : Real.pi * (n : ℝ) ≠ 0 := mul_ne_zero Real.pi_ne_zero hn0
  have hbox : Real.sqrt G.boxVolume ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 G.boxVolume_pos)
  have hprod : (∏ q, Real.sqrt (G.coordinateMinLength q : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q _
    apply ne_of_gt
    apply Real.sqrt_pos.2
    exact_mod_cast G.coordinateMinLength_pos q
  have hc : (∏ q, Real.pi * (n : ℝ) /
      (2 * Real.sqrt (G.coordinateMinLength q : ℝ))) =
      (Real.pi * (n : ℝ) / 2)^d /
        (∏ q, Real.sqrt (G.coordinateMinLength q : ℝ)) := by
    calc
      _ = ∏ q, (Real.pi * (n : ℝ) / 2) /
          Real.sqrt (G.coordinateMinLength q : ℝ) := by
        apply Finset.prod_congr rfl
        intro q _
        rw [div_div]
      _ = _ := by
        rw [Finset.prod_div_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hinv : (Real.pi * (n : ℝ) / 2)^d *
      (2 / (Real.pi * (n : ℝ)))^d = 1 := by
    rw [← mul_pow]
    have he : (Real.pi * (n : ℝ) / 2) * (2 / (Real.pi * (n : ℝ))) = 1 := by
      field_simp
    rw [he, one_pow]
  rw [hc, rhoL_eq_prod_sqrt_div_sqrt_boxVolume]
  calc
    _ = (Real.pi * (n : ℝ) / 2)^d * (2 / (Real.pi * (n : ℝ)))^d := by
      field_simp
    _ = 1 := hinv

/-- The filling-ratio power in the article is precisely the inverse of the
corresponding Turan loss. -/
theorem fillingRatio_pow_mul_inverse (CT : ℝ) (hCT : 0 < CT) (k : ℕ) :
    ((CT * (d : ℝ) / G.fillingRatio)^k) *
      ((G.fillingRatio / (CT * (d : ℝ)))^k) = 1 := by
  have hdim : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.dimension_pos)
  have hden : CT * (d : ℝ) ≠ 0 := mul_ne_zero (ne_of_gt hCT) hdim
  have hratio : G.fillingRatio ≠ 0 := ne_of_gt G.fillingRatio_pos
  rw [← mul_pow, div_mul_div_cancel₀ hratio, div_self hden, one_pow]

end
end LeanNumDetect.MultiTuran.SegmentedGrid
