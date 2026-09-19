import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
set_option autoImplicit false
namespace LeanNumDetect

theorem finite_nodes_enclosing_diameter {q : ℕ} (hq : 0 < q) (x : Fin q → ℝ) :
    ∃ c : ℝ, ∀ j, x j ∈ Set.Icc c (c+Metric.diam (Set.range x)) := by
  classical
  letI : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  refine ⟨x i, fun j => ⟨hi j (Finset.mem_univ _), ?_⟩⟩
  have hh := Metric.dist_le_diam_of_mem (Set.finite_range x).isBounded
    (Set.mem_range_self j) (Set.mem_range_self i)
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hi j (Finset.mem_univ _)))] at hh
  linarith

theorem finite_nodes_diameter_zero {q : ℕ} (hq : 0 < q) (hq' : q ≤ 1) (x : Fin q → ℝ) :
    Metric.diam (Set.range x) = 0 := by
  have he : q = 1 := by omega
  subst q
  have hx : x = fun _ => x 0 := funext (fun j => congrArg x (Subsingleton.elim j 0))
  rw [hx, Set.range_const, Metric.diam_singleton]

theorem exists_periodic_gap_le_pi (x : ℝ) :
    ∃ p : ℤ, |x-2*Real.pi*p| ≤ Real.pi := by
  refine ⟨round (x/(2*Real.pi)), ?_⟩
  have hh := abs_sub_round (x/(2*Real.pi))
  have he : x-2*Real.pi*(round (x/(2*Real.pi)) : ℝ) =
      (2*Real.pi)*(x/(2*Real.pi)-(round (x/(2*Real.pi)) : ℝ)) := by field_simp
  rw [he, abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi)]
  nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*Real.pi by positivity)]

theorem periodic_separation_lt_half {x β : ℝ}
    (hsep : ∀ p : ℤ, 2*Real.pi*β < |x-2*Real.pi*p|) : β < 1/2 := by
  obtain ⟨p,hp⟩ := exists_periodic_gap_le_pi x
  have hh := (hsep p).trans_le hp
  nlinarith [Real.pi_pos]
end LeanNumDetect
