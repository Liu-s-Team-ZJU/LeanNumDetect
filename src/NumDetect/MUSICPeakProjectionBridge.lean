import NumDetect.MUSICPeakRegularity

set_option autoImplicit false
open WithLp
open scoped InnerProductSpace RealInnerProductSpace
namespace LeanNumDetect
namespace NumDetect
noncomputable section

variable {ι : Type*} [Fintype ι]
local instance : InnerProductSpace ℝ (EuclideanSpace ℂ ι) :=
  InnerProductSpace.rclikeToReal ℂ _

theorem starProjection_real_selfAdjoint
    (S : Submodule ℂ (EuclideanSpace ℂ ι))
    (x y : EuclideanSpace ℂ ι) :
    ⟪x, (S.starProjection.restrictScalars ℝ) y⟫_ℝ =
      ⟪(S.starProjection.restrictScalars ℝ) x, y⟫_ℝ := by
  change ⟪x, S.starProjection y⟫_ℝ = ⟪S.starProjection x, y⟫_ℝ
  change RCLike.re ⟪x, S.starProjection y⟫_ℂ =
    RCLike.re ⟪S.starProjection x, y⟫_ℂ
  exact congrArg RCLike.re ((S.inner_starProjection_left_eq_right x y).symm)

theorem starProjection_norm_sq_eq_real_quadratic
    (S : Submodule ℂ (EuclideanSpace ℂ ι))
    (x : EuclideanSpace ℂ ι) :
    ‖S.starProjection x‖ ^ 2 =
      ⟪x, (S.starProjection.restrictScalars ℝ) x⟫_ℝ := by
  calc
    ‖S.starProjection x‖ ^ 2 =
        ⟪S.starProjection x, S.starProjection x⟫_ℝ :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ⟪x, S.starProjection (S.starProjection x)⟫_ℝ :=
      (starProjection_real_selfAdjoint S x (S.starProjection x)).symm
    _ = ⟪x, (S.starProjection.restrictScalars ℝ) x⟫_ℝ := by
      rw [S.starProjection_eq_self_iff.mpr (by simp)]
      rfl

theorem starProjection_difference_real_selfAdjoint
    (S₁ S₂ : Submodule ℂ (EuclideanSpace ℂ ι))
    (x y : EuclideanSpace ℂ ι) :
    ⟪x, ((S₁.starProjection.restrictScalars ℝ) -
        (S₂.starProjection.restrictScalars ℝ)) y⟫_ℝ =
      ⟪((S₁.starProjection.restrictScalars ℝ) -
        (S₂.starProjection.restrictScalars ℝ)) x, y⟫_ℝ := by
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right, inner_sub_left]
  rw [starProjection_real_selfAdjoint S₁ x y,
    starProjection_real_selfAdjoint S₂ x y]

theorem starProjection_norm_sq_difference_eq_real_quadratic
    (S₁ S₂ : Submodule ℂ (EuclideanSpace ℂ ι))
    (x : EuclideanSpace ℂ ι) :
    ‖S₁.starProjection x‖ ^ 2 - ‖S₂.starProjection x‖ ^ 2 =
      ⟪x, ((S₁.starProjection.restrictScalars ℝ) -
        (S₂.starProjection.restrictScalars ℝ)) x⟫_ℝ := by
  rw [starProjection_norm_sq_eq_real_quadratic,
    starProjection_norm_sq_eq_real_quadratic]
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right]

end
end NumDetect
end LeanNumDetect
