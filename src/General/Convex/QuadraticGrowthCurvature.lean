import Mathlib

/-! Quadratic growth forces positive second derivative at a zero. -/

set_option autoImplicit false
open Filter Set
open scoped ContDiff Topology

noncomputable section

namespace LeanNumDetect

/-- The quadratic Taylor polynomial at a zero with vanishing first derivative. -/
theorem taylor2_at_zero_of_value_deriv_zero
    (f : ℝ → ℝ) (hzero : f 0 = 0) (hderiv : deriv f 0 = 0)
    (t : ℝ) :
    taylorWithinEval f 2 univ 0 t = iteratedDeriv 2 f 0 * t ^ 2 / 2 := by
  rw [show (2:ℕ) = 1 + 1 by omega, taylorWithinEval_succ,
    taylorWithinEval_succ, taylor_within_zero_eval]
  simp only [iteratedDerivWithin_univ, iteratedDeriv_one, hzero, hderiv,
    sub_zero, zero_add, Nat.factorial_one, Nat.cast_one, mul_one]
  ring

/-- Quadratic growth along a line gives a lower bound on curvature at its zero. -/
theorem curvature_lower_of_quadratic_growth
    (f : ℝ → ℝ) (c : ℝ) (hf : ContDiff ℝ 2 f)
    (hzero : f 0 = 0) (hderiv : deriv f 0 = 0)
    (hgrowth : ∀ᶠ t in 𝓝[≠] (0:ℝ), c ^ 2 * t ^ 2 ≤ f t) :
    2 * c ^ 2 ≤ iteratedDeriv 2 f 0 := by
  have htaylor : Tendsto (fun t : ℝ =>
      (f t - iteratedDeriv 2 f 0 * t ^ 2 / 2) / t ^ 2)
      (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    have h := Real.taylor_tendsto convex_univ (mem_univ (0:ℝ)) hf.contDiffOn
    rw [nhdsWithin_univ] at h
    convert h.mono_left nhdsWithin_le_nhds using 1
    funext t
    rw [taylor2_at_zero_of_value_deriv_zero f hzero hderiv t]
    simp
  have hpoint : ∀ᶠ t in 𝓝[≠] (0:ℝ),
      c ^ 2 - iteratedDeriv 2 f 0 / 2 ≤
        (f t - iteratedDeriv 2 f 0 * t ^ 2 / 2) / t ^ 2 := by
    filter_upwards [hgrowth, self_mem_nhdsWithin] with t ht ht0
    have htne : t ≠ 0 := ht0
    have htpos : 0 < t ^ 2 := sq_pos_of_ne_zero htne
    apply (le_div_iff₀ htpos).2
    nlinarith [ht]
  have hlim : c ^ 2 - iteratedDeriv 2 f 0 / 2 ≤ 0 :=
    ge_of_tendsto htaylor hpoint
  linarith

end LeanNumDetect
