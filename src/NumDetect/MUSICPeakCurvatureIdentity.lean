import NumDetect.MUSICPeakQuadraticBounds
import NumDetect.MUSICPeakProjectionBridge

set_option autoImplicit false
open scoped InnerProductSpace RealInnerProductSpace
namespace LeanNumDetect
namespace NumDetect
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem iteratedDeriv_projected_normSq_two
    (T : E →L[ℝ] E) (a au auu : ℝ → E)
    (ha : ∀ t, HasDerivAt a (au t) t)
    (hau : ∀ t, HasDerivAt au (auu t) t)
    (t : ℝ) :
    iteratedDeriv 2 (fun s => ‖T (a s)‖ ^ 2) t =
      2 * ⟪T (a t), T (auu t)⟫_ℝ +
        2 * ⟪T (au t), T (au t)⟫_ℝ := by
  have hfirst : deriv (fun s => ‖T (a s)‖ ^ 2) =
      fun s => 2 * ⟪T (a s), T (au s)⟫_ℝ := by
    funext s
    exact (projected_normSq_hasDerivAt T a au (ha s)).deriv
  have hsecond : deriv (fun s => 2 * ⟪T (a s), T (au s)⟫_ℝ) =
      fun s => 2 * ⟪T (a s), T (auu s)⟫_ℝ +
        2 * ⟪T (au s), T (au s)⟫_ℝ := by
    funext s
    exact (projected_normSq_first_hasDerivAt T a au auu (ha s) (hau s)).deriv
  simp [iteratedDeriv_succ, hfirst, hsecond]

theorem iteratedDeriv_selfAdjoint_quadratic_two
    (D : E →L[ℝ] E)
    (hsa : ∀ z w, ⟪z, D w⟫_ℝ = ⟪D z, w⟫_ℝ)
    (a au auu : ℝ → E)
    (ha : ∀ t, HasDerivAt a (au t) t)
    (hau : ∀ t, HasDerivAt au (auu t) t)
    (t : ℝ) :
    iteratedDeriv 2 (fun s => ⟪a s, D (a s)⟫_ℝ) t =
      2 * ⟪a t, D (auu t)⟫_ℝ +
        2 * ⟪au t, D (au t)⟫_ℝ := by
  have hfirst : deriv (fun s => ⟪a s, D (a s)⟫_ℝ) =
      fun s => 2 * ⟪a s, D (au s)⟫_ℝ := by
    funext s
    exact (selfAdjoint_quadratic_first_hasDerivAt D hsa a au (ha s)).deriv
  have hsecond : deriv (fun s => 2 * ⟪a s, D (au s)⟫_ℝ) =
      fun s => 2 * ⟪a s, D (auu s)⟫_ℝ +
        2 * ⟪au s, D (au s)⟫_ℝ := by
    funext s
    exact (selfAdjoint_quadratic_second_hasDerivAt D a au auu (ha s) (hau s)).deriv
  simp [iteratedDeriv_succ, hfirst, hsecond]

end
end NumDetect
end LeanNumDetect
