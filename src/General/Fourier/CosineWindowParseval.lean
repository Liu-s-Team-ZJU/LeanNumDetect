import General.Fourier.CosineWindowTransform
import General.Fourier.ShiftedParseval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace LeanNumDetect

theorem cosineWindow_le_one (s : ℕ) (eta x : ℝ) : cosineWindow s eta x ≤ 1 := by
  classical
  unfold cosineWindow
  by_cases hx : x ∈ Set.Icc (-eta / 2) (eta / 2)
  · rw [Set.indicator_of_mem hx]
    calc
      _ ≤ |Real.cos (Real.pi * x / eta) ^ (2 * s)| := le_abs_self _
      _ = |Real.cos (Real.pi * x / eta)| ^ (2 * s) := abs_pow _ _
      _ ≤ 1 := pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
  · simp only [Set.indicator_of_notMem hx, zero_le_one]

theorem translatedWindowSum_norm_le {q : ℕ} (s : ℕ) (eta : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ) (x : ℝ) :
    ‖translatedWindowSum s eta xi d x‖ ≤ ∑ h, ‖d h‖ := by
  unfold translatedWindowSum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro h _
  rw [norm_mul]
  have hn : ‖(cosineWindow s eta (x - xi h) : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cosineWindow_nonneg s eta (x - xi h))] using
      cosineWindow_le_one s eta (x - xi h)
  exact mul_le_of_le_one_right (norm_nonneg _) hn

theorem translatedWindowSum_memLp_interval {q : ℕ} (s : ℕ) (eta a b : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ) :
    MemLp (translatedWindowSum s eta xi d) 2 (volume.restrict (Set.Ioc a b)) := by
  apply MemLp.of_bound
    ((translatedWindowSum_integrable s eta xi d).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self) (∑ h, ‖d h‖)
  exact Filter.Eventually.of_forall (translatedWindowSum_norm_le s eta xi d)

/-- The first Parseval identity of the manuscript, for the actual window, arbitrary
coefficients, and every shifted integer grid. No Fourier identity is assumed. -/
theorem translatedWindowSum_parseval {q : ℕ} (s : ℕ) (eta lo hi shift : ℝ)
    (xi : Fin q → ℝ) (d : Fin q → ℂ)
    (hxi : ∀ h, lo ≤ xi h ∧ xi h ≤ hi)
    (hwidth : hi - lo + eta < 2 * Real.pi) :
    HasSum (fun k : ℤ => ‖windowTransform s eta ((k : ℝ) - shift)‖ ^ 2 *
      ‖exponentialSum xi d ((k : ℝ) - shift)‖ ^ 2)
      ((2 * Real.pi) * ∫ x : ℝ, ‖translatedWindowSum s eta xi d x‖ ^ 2) := by
  let a := (lo + hi) / 2 - Real.pi
  have hs (x : ℝ) (hx : x ∉ Set.Ioc a (a + 2 * Real.pi)) :
      translatedWindowSum s eta xi d x = 0 := by
    by_contra hn
    have hh := translatedWindowSum_support s eta lo hi xi d hxi hn
    apply hx
    dsimp [a]
    constructor <;> linarith [hh.1, hh.2]
  have hh := hasSum_angularTransform_of_support a shift (translatedWindowSum s eta xi d)
    (translatedWindowSum_memLp_interval s eta a (a + 2 * Real.pi) xi d) hs
  simpa only [translatedWindowSum_transform, norm_mul, mul_pow] using hh
end LeanNumDetect
