import NumDetect.MUSICPeakCurvatureIdentity

set_option autoImplicit false
open scoped InnerProductSpace RealInnerProductSpace
namespace LeanNumDetect
namespace NumDetect
noncomputable section

variable {ι : Type*} [Fintype ι]
local instance realInnerProductSpace_projectorCurvature :
    InnerProductSpace ℝ (EuclideanSpace ℂ ι) :=
  InnerProductSpace.rclikeToReal ℂ _

/-- A projection difference bound controls the second derivative of its squared Fourier residual. -/
theorem starProjection_squaredCurvature_perturb_abs_le
    (Sσ S₀ : Submodule ℂ (EuclideanSpace ℂ ι))
    (a au auu : ℝ → EuclideanSpace ℂ ι)
    (ha : ∀ s, HasDerivAt a (au s) s)
    (hau : ∀ s, HasDerivAt au (auu s) s)
    (t p Ω : ℝ) (hp : 0 ≤ p) (hΩ : 0 ≤ Ω)
    (hσ : ContDiffAt ℝ 2 (fun s => ‖Sσ.starProjection (a s)‖ ^ 2) t)
    (h₀ : ContDiffAt ℝ 2 (fun s => ‖S₀.starProjection (a s)‖ ^ 2) t)
    (hproj : ∀ z : EuclideanSpace ℂ ι,
      ‖Sσ.starProjection z - S₀.starProjection z‖ ≤ p * ‖z‖)
    (haNorm : ‖a t‖ ≤ 1) (hauNorm : ‖au t‖ ≤ Ω)
    (hauuNorm : ‖auu t‖ ≤ Ω ^ 2) :
    |iteratedDeriv 2 (fun s => ‖Sσ.starProjection (a s)‖ ^ 2) t -
      iteratedDeriv 2 (fun s => ‖S₀.starProjection (a s)‖ ^ 2) t| ≤
      4 * p * Ω ^ 2 := by
  let D : (EuclideanSpace ℂ ι) →L[ℝ] (EuclideanSpace ℂ ι) :=
    Sσ.starProjection.restrictScalars ℝ - S₀.starProjection.restrictScalars ℝ
  have hD : ∀ z : EuclideanSpace ℂ ι, ‖D z‖ ≤ p * ‖z‖ := by
    intro z
    change ‖Sσ.starProjection z - S₀.starProjection z‖ ≤ p * ‖z‖
    exact hproj z
  have hsa : ∀ z w, ⟪z, D w⟫_ℝ = ⟪D z, w⟫_ℝ := by
    intro z w
    exact starProjection_difference_real_selfAdjoint Sσ S₀ z w
  have hfun : (fun s => ‖Sσ.starProjection (a s)‖ ^ 2 -
      ‖S₀.starProjection (a s)‖ ^ 2) =
      (fun s => ⟪a s, D (a s)⟫_ℝ) := by
    funext s
    exact starProjection_norm_sq_difference_eq_real_quadratic Sσ S₀ (a s)
  have hsub := iteratedDeriv_fun_sub hσ h₀
  have hid : iteratedDeriv 2 (fun s => ‖Sσ.starProjection (a s)‖ ^ 2) t -
      iteratedDeriv 2 (fun s => ‖S₀.starProjection (a s)‖ ^ 2) t =
      2 * ⟪a t, D (auu t)⟫_ℝ +
        2 * ⟪au t, D (au t)⟫_ℝ := by
    rw [← hsub, hfun]
    exact iteratedDeriv_selfAdjoint_quadratic_two D hsa a au auu ha hau t
  rw [hid]
  exact projected_hessian_perturb_abs_le D p Ω hp hΩ hD
    (a t) (au t) (auu t) haNorm hauNorm hauuNorm

end
end NumDetect
end LeanNumDetect
