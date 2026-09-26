import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
The logarithmic sample count absorbs the two matrix-Chernoff tails.  This is the
scalar arithmetic in `lem:fixed-support-singular-values`; no probability or
matrix theorem is assumed here.
-/

set_option autoImplicit false

namespace LeanNumDetect.RandSamp

/-- A logarithmic sampling threshold makes the sum of the lower and upper
Chernoff failure bounds at most the requested failure probability. -/
theorem chernoff_failure_bound_of_sample_size
    {m d R a b δ η : ℝ}
    (hm : 0 ≤ m) (hd : 0 < d) (hR : 0 < R) (ha : 0 < a)
    (hab : a ≤ b) (hδ : 0 < δ) (hη : 0 < η)
    (hsample : 3 * R / (a * δ ^ 2) * Real.log (2 * d / η) ≤ m) :
    d * Real.exp (-(m * a * δ ^ 2) / (2 * R)) +
      d * Real.exp (-(m * b * δ ^ 2) / (3 * R)) ≤ η := by
  have hq : 0 < a * δ ^ 2 := by positivity
  have hs' : (3 * R * Real.log (2 * d / η)) / (a * δ ^ 2) ≤ m := by
    calc
      (3 * R * Real.log (2 * d / η)) / (a * δ ^ 2) =
          3 * R / (a * δ ^ 2) * Real.log (2 * d / η) := by ring
      _ ≤ m := hsample
  have hlog : Real.log (2 * d / η) ≤ (m * a * δ ^ 2) / (3 * R) := by
    apply (le_div_iff₀ (by positivity : 0 < 3 * R)).2
    have h := (div_le_iff₀ hq).1 hs'
    nlinarith
  have hnonneg : 0 ≤ m * a * δ ^ 2 := by positivity
  have hlower : Real.log (2 * d / η) ≤ (m * a * δ ^ 2) / (2 * R) := by
    apply hlog.trans
    gcongr
    linarith
  have hupper : Real.log (2 * d / η) ≤ (m * b * δ ^ 2) / (3 * R) := by
    apply hlog.trans
    gcongr
  have hexp : Real.exp (-Real.log (2 * d / η)) = η / (2 * d) := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    exact inv_div _ _
  have htailLower : Real.exp (-(m * a * δ ^ 2) / (2 * R)) ≤ η / (2 * d) := by
    rw [← hexp]
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hlower
  have htailUpper : Real.exp (-(m * b * δ ^ 2) / (3 * R)) ≤ η / (2 * d) := by
    rw [← hexp]
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hupper
  calc
    d * Real.exp (-(m * a * δ ^ 2) / (2 * R)) +
        d * Real.exp (-(m * b * δ ^ 2) / (3 * R))
        ≤ d * (η / (2 * d)) + d * (η / (2 * d)) := by gcongr
    _ = η := by field_simp; ring

/-- In the Fourier population, both the dimension and the uniform rank-one
row bound are the number of nodes. -/
theorem fourier_chernoff_failure_bound_of_sample_size
    {m s a b δ η : ℝ}
    (hm : 0 ≤ m) (hs : 0 < s) (ha : 0 < a) (hab : a ≤ b)
    (hδ : 0 < δ) (hη : 0 < η)
    (hsample : 3 * s / (a * δ ^ 2) * Real.log (2 * s / η) ≤ m) :
    s * Real.exp (-(m * a * δ ^ 2) / (2 * s)) +
      s * Real.exp (-(m * b * δ ^ 2) / (3 * s)) ≤ η :=
  chernoff_failure_bound_of_sample_size hm hs hs ha hab hδ hη hsample

end LeanNumDetect.RandSamp
