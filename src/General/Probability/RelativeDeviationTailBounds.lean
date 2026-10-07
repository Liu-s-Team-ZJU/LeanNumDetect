import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Scalar conversion from concentration around the expected supremum to the
relative population-energy threshold. The constants are independent of the
row envelope and the population energy. -/

set_option autoImplicit false

namespace LeanNumDetect.RelativeDeviationTailBounds

theorem expected_plus_increment_le_relative_threshold {E a δ S : ℝ}
    (hE : E ≤ a * δ * (1 + S)) :
    E + (4 * a + 8) * δ * (1 + S) ≤ (5 * a + 8) * δ * (1 + S) := by
  nlinarith [hE]

/-- An expected supremum at scale `a δ (1+S)` and a linear-envelope subgamma
tail imply the exact exponent `δ² m / p`. -/
theorem relative_deviation_tail_exponent_le {E a δ S p m : ℝ}
    (hE0 : 0 ≤ E) (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hS : 0 ≤ S) (hp : 0 < p) (hm : 0 ≤ m) (hE : E ≤ a * δ * (1 + S)) :
    Real.exp (-(m * ((4 * a + 8) * δ * (1 + S))^2) /
      (4 * p * (E + S + (4 * a + 8) * δ * (1 + S)))) ≤
      Real.exp (-(δ^2 * m / p)) := by
  let u := (4 * a + 8) * δ * (1 + S)
  have hcoef : 0 < 4 * a + 8 := by linarith
  have hone : 0 < 1 + S := by linarith
  have hu : 0 < u := mul_pos (mul_pos hcoef hδ) hone
  have hden : 0 < E + S + u := add_pos_of_nonneg_of_pos (add_nonneg hE0 hS) hu
  have hsum : E + S + u ≤ (5 * a + 9) * (1 + S) := by
    have hfirst := expected_plus_increment_le_relative_threshold hE
    have hδterm : (5 * a + 8) * δ * (1 + S) ≤ (5 * a + 8) * (1 + S) := by
      have hmul := mul_le_mul_of_nonneg_left hδ1 (by positivity : 0 ≤ 5 * a + 8)
      have hmul' := mul_le_mul_of_nonneg_right hmul hone.le
      simpa only [mul_one] using hmul'
    dsimp [u]
    nlinarith [hfirst, hδterm]
  have hc : 4 * (5 * a + 9) ≤ (4 * a + 8)^2 := by nlinarith [ha]
  have hs : 1 + S ≤ (1 + S)^2 := by nlinarith [hS]
  have hsquare : 4 * δ^2 * (E + S + u) ≤ u^2 := by
    calc
      _ ≤ 4 * δ^2 * ((5 * a + 9) * (1 + S)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = δ^2 * (4 * (5 * a + 9) * (1 + S)) := by ring
      _ ≤ δ^2 * ((4 * a + 8)^2 * (1 + S)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hone.le) (sq_nonneg δ)
      _ ≤ δ^2 * ((4 * a + 8)^2 * (1 + S)^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) (sq_nonneg δ)
      _ = u^2 := by dsimp [u]; ring
  have hratio : δ^2 ≤ u^2 / (4 * (E + S + u)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hden)).mpr
    nlinarith [hsquare]
  have hscale := mul_le_mul_of_nonneg_left hratio (div_nonneg hm hp.le)
  apply Real.exp_le_exp.mpr
  change -(m * u^2) / (4 * p * (E + S + u)) ≤ _
  have hleft : -(m * u^2) / (4 * p * (E + S + u)) =
      -(m / p * (u^2 / (4 * (E + S + u)))) := by
    field_simp [hp.ne', hden.ne']
  have hright : -(δ^2 * m / p) = -(m / p * δ^2) := by ring
  rw [hleft, hright]
  exact neg_le_neg hscale

end LeanNumDetect.RelativeDeviationTailBounds
