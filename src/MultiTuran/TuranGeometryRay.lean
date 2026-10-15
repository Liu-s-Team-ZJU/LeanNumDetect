import MultiTuran.Geometry
import General.Fourier.ExponentialSums
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Ray sections of convex bodies

The parameter on a ray is its actual length when the direction has norm one.
Compactness and convexity identify every positive ray section with `(0,R]`,
even when the initial point is on the boundary of the body.
-/

set_option autoImplicit false
open scoped BigOperators
open Set Metric

namespace LeanNumDetect.MultiTuran
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive parameters whose points on the ray lie in a given set. -/
def raySection (S : Set E) (x u : E) : Set ℝ :=
  {r | 0 < r ∧ x + r • u ∈ S}

/-- A compact convex body's section along a unit ray is a literal interval. -/
theorem exists_ray_radius {B : Set E} (hcompact : IsCompact B)
    (hconvex : Convex ℝ B) {x u : E} (hx : x ∈ B) (hu : ‖u‖ = 1) :
    ∃ R : ℝ, 0 ≤ R ∧ x + R • u ∈ B ∧
      raySection B x u = Ioc 0 R ∧
      ∀ r ∈ Icc (0 : ℝ) R, x + r • u ∈ B := by
  let K : Set ℝ := Ici 0 ∩ (fun r : ℝ => x + r • u) ⁻¹' B
  have hKclosed : IsClosed K :=
    isClosed_Ici.inter (hcompact.isClosed.preimage
      (continuous_const.add (continuous_id.smul continuous_const)))
  obtain ⟨D,hD⟩ := hcompact.isBounded.subset_closedBall x
  have hsub : K ⊆ Icc 0 D := by
    intro r hr
    refine ⟨hr.1,?_⟩
    have hr0 : 0 ≤ r := hr.1
    have h := hD hr.2
    change dist (x + r • u) x ≤ D at h
    simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr0, hu, mul_one] using h
  have hKcompact : IsCompact K := isCompact_Icc.of_isClosed_subset hKclosed hsub
  have hz : (0 : ℝ) ∈ K := by simp [K,hx]
  obtain ⟨R,hR,hmax⟩ := hKcompact.exists_isMaxOn ⟨0,hz⟩ continuous_id.continuousOn
  have hR0 : 0 ≤ R := hR.1
  have hBR : x + R • u ∈ B := hR.2
  have hsegment : ∀ r ∈ Icc (0 : ℝ) R, x + r • u ∈ B := by
    intro r hr
    by_cases hRzero : R = 0
    · have hrzero : r = 0 := by subst R; exact le_antisymm hr.2 hr.1
      simpa [hrzero] using hx
    · have hRpos : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hRzero)
      have ht : r/R ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hr.1 hR0, (div_le_one hRpos).2 hr.2⟩
      have h := hconvex.add_smul_mem hx hBR ht
      simpa only [smul_smul, div_mul_cancel₀ r hRzero] using h
  refine ⟨R,hR0,hBR,?_,hsegment⟩
  ext r
  constructor
  · intro hr
    exact ⟨hr.1,hmax ⟨hr.1.le,hr.2⟩⟩
  · intro hr
    exact ⟨hr.1,hsegment r ⟨hr.1.le,hr.2⟩⟩

/-- The restriction to an affine ray is still the same finite scalar
exponential sum, with explicit phase-shifted coefficients and frequencies. -/
theorem exponentialSum_ray {d n : ℕ} (Y : Fin n → Point d) (c : Fin n → ℂ)
    (x u : Point d) (r : ℝ) :
    exponentialSum Y c (x + r • u) =
      ExponentialSumEstimates.exponentialSum
        (fun j => ∑ q, u q * Y j q)
        (fun j => c j * Complex.exp
          (Complex.I * ((∑ q, x q * Y j q : ℝ) : ℂ))) r := by
  unfold exponentialSum ExponentialSumEstimates.exponentialSum
  apply Finset.sum_congr rfl
  intro j _
  have hsum : (∑ q, (x + r • u) q * Y j q) =
      (∑ q, x q * Y j q) + r * (∑ q, u q * Y j q) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
  rw [hsum]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

end
end LeanNumDetect.MultiTuran
