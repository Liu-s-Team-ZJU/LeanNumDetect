import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # Effective-degree cancellation in a local zero product

At the distance of the first omitted zero, the first `d` factors contribute
exactly `r^d`. This cancels the same power in the local disk-growth lower
bound, leaving a uniform lower bound for the remaining product. All quantities
here are finite real products; no zero-counting theorem is assumed implicitly.
-/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran
noncomputable section

/-- The local growth power is the effective degree, even when more zeros are
present. All distances are strictly positive because applications omit the
finite zero set before integration. -/
theorem zeroProduct_tail_lower_of_scale_growth (d k : ℕ)
    (a : Fin (d+(k+1)) → ℝ) (hpos : ∀ i, 0 < a i)
    (hmono : Monotone a) (hupper : ∀ i, a i ≤ 1) (H : ℝ)
    (hgrowth : ∀ r : ℝ, 0 < r → r ≤ 1 →
      Real.exp (-H) * r^d ≤ ∏ i, (r+a i)) :
    Real.exp (-H)/(2 : ℝ)^(d+(k+1)) ≤
      ∏ i : Fin (k+1), a (i.natAdd d) := by
  let pivot : Fin (d+(k+1)) := ⟨d, by omega⟩
  let r : ℝ := a pivot
  have hr : 0 < r := hpos pivot
  have hr1 : r ≤ 1 := hupper pivot
  have hfirst (i : Fin d) : a (i.castAdd (k+1)) ≤ r := by
    apply hmono
    change i.val ≤ d
    omega
  have htail (i : Fin (k+1)) : r ≤ a (i.natAdd d) := by
    apply hmono
    change d ≤ d+i.val
    omega
  have hfirstprod : (∏ i : Fin d, (r+a (i.castAdd (k+1)))) ≤ (2*r)^d := by
    calc
      _ ≤ ∏ _i : Fin d, (2*r) := Finset.prod_le_prod
        (fun i _ => by linarith [hpos (i.castAdd (k+1))])
        (fun i _ => by linarith [hfirst i])
      _ = _ := by simp
  have htailprod : (∏ i : Fin (k+1), (r+a (i.natAdd d))) ≤
      (2 : ℝ)^(k+1) * ∏ i : Fin (k+1), a (i.natAdd d) := by
    calc
      _ ≤ ∏ i : Fin (k+1), (2*a (i.natAdd d)) := Finset.prod_le_prod
        (fun i _ => by linarith [hpos (i.natAdd d)])
        (fun i _ => by linarith [htail i])
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hprod : (∏ i, (r+a i)) ≤ (2 : ℝ)^(d+(k+1)) * r^d *
      (∏ i : Fin (k+1), a (i.natAdd d)) := by
    rw [Fin.prod_univ_add]
    calc
      _ ≤ (2*r)^d * ((2 : ℝ)^(k+1) * ∏ i : Fin (k+1), a (i.natAdd d)) :=
        mul_le_mul hfirstprod htailprod
          (Finset.prod_nonneg fun i _ => by linarith [hpos (i.natAdd d)]) (by positivity)
      _ = _ := by rw [mul_pow,pow_add]; ring
  have h := (hgrowth r hr hr1).trans hprod
  have hc : Real.exp (-H) ≤ (2 : ℝ)^(d+(k+1)) *
      (∏ i : Fin (k+1), a (i.natAdd d)) := by
    apply (mul_le_mul_iff_of_pos_right (pow_pos hr d)).mp
    convert h using 1 <;> ring
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^(d+(k+1)))).2
  simpa only [mul_comm] using hc

/-- Restoring the selected factors gives a lower bound for the full local
product by any lower bound on a product of its `d` nearest factors. -/
theorem zeroProduct_lower_of_scale_growth (d k : ℕ)
    (a : Fin (d+(k+1)) → ℝ) (hpos : ∀ i, 0 < a i)
    (hmono : Monotone a) (hupper : ∀ i, a i ≤ 1) (H : ℝ)
    (hgrowth : ∀ r : ℝ, 0 < r → r ≤ 1 →
      Real.exp (-H) * r^d ≤ ∏ i, (r+a i))
    {b : ℝ} (hb : b ≤ ∏ i : Fin d, a (i.castAdd (k+1))) :
    (Real.exp (-H)/(2 : ℝ)^(d+(k+1))) * b ≤ ∏ i, a i := by
  have htail := zeroProduct_tail_lower_of_scale_growth d k a hpos hmono hupper H hgrowth
  calc
    _ ≤ (Real.exp (-H)/(2 : ℝ)^(d+(k+1))) *
        (∏ i : Fin d, a (i.castAdd (k+1))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (∏ i : Fin (k+1), a (i.natAdd d)) *
        (∏ i : Fin d, a (i.castAdd (k+1))) :=
      mul_le_mul_of_nonneg_right htail (Finset.prod_nonneg fun i _ => (hpos _).le)
    _ = _ := by rw [Fin.prod_univ_add a]; ring

end
end LeanNumDetect.MultiTuran
