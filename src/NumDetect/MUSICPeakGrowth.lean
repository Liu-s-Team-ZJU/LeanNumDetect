import NumDetect.MUSICLocation
import NumDetect.MUSICPeakRegularity
import General.Convex.QuadraticGrowthCurvature

/-! Nearest-source geometry converts global residual growth to quadratic growth along source lines. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Set WithLp
open scoped Topology
namespace LeanNumDetect
namespace NumDetect
noncomputable section

/-- A point within half the source separation has the indicated nearest source. -/
theorem finiteSourceDistance_eq_dist_of_near
    {E : Type*} [PseudoMetricSpace E] {n : ℕ}
    (hn : 0 < n) (node : Fin n → E) (Δ : ℝ)
    (hsep : ∀ i k : Fin n, i ≠ k → Δ ≤ dist (node i) (node k))
    (j : Fin n) (y : E) (hy : dist y (node j) ≤ Δ / 2) :
    finiteSourceDistance hn node y = dist y (node j) := by
  apply le_antisymm
  · exact Finset.inf'_le _ (Finset.mem_univ j)
  · apply (Finset.le_inf'_iff (fin_univ_nonempty hn)
      (fun k => dist y (node k))).2
    intro k hk
    by_cases hkj : k = j
    · simp [hkj]
    · have hs := hsep j k (Ne.symm hkj)
      have htri := dist_triangle (node j) y (node k)
      rw [dist_comm (node j) y] at htri
      linarith

/-- Linear MUSIC residual growth implies quadratic squared-residual growth along every unit line through a source. -/
theorem residual_quadratic_growth_on_unit_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (hn : 0 < n) (node : Fin n → E) (R : E → ℝ)
    (K : Set E) (Δ c : ℝ) (hΔ : 0 < Δ) (hc : 0 ≤ c)
    (hsep : ∀ i k : Fin n, i ≠ k → Δ ≤ dist (node i) (node k))
    (j : Fin n) (hK : K ∈ 𝓝 (node j))
    (u : E) (hu : ‖u‖ = 1)
    (hgrowth : ∀ y ∈ K,
      c * min (Δ / 4) (finiteSourceDistance hn node y) ≤ R y) :
    ∀ᶠ t in 𝓝[≠] (0:ℝ),
      c ^ 2 * t ^ 2 ≤ R (node j + t • u) ^ 2 := by
  have hpath : Tendsto (fun t : ℝ => node j + t • u)
      (𝓝 (0:ℝ)) (𝓝 (node j)) := by
    convert (show Continuous (fun t : ℝ => node j + t • u) by fun_prop).tendsto 0 using 1
    simp
  have hKevent : ∀ᶠ t in 𝓝 (0:ℝ), node j + t • u ∈ K :=
    hpath.eventually hK
  have hsmall : ∀ᶠ t in 𝓝 (0:ℝ), |t| < Δ / 4 := by
    have hball : Metric.ball (0:ℝ) (Δ / 4) ∈ 𝓝 (0:ℝ) :=
      Metric.ball_mem_nhds 0 (by linarith)
    filter_upwards [hball] with t ht
    simpa [Metric.mem_ball, Real.dist_eq] using ht
  filter_upwards [hKevent.filter_mono nhdsWithin_le_nhds,
    hsmall.filter_mono nhdsWithin_le_nhds] with t htK htSmall
  have hdist : dist (node j + t • u) (node j) = |t| := by
    simp [dist_eq_norm, norm_smul, hu]
  have hnear : finiteSourceDistance hn node (node j + t • u) = |t| := by
    rw [finiteSourceDistance_eq_dist_of_near hn node Δ hsep j _]
    · exact hdist
    · rw [hdist]
      linarith
  have hbound := hgrowth (node j + t • u) htK
  rw [hnear, min_eq_right (by linarith : |t| ≤ Δ / 4)] at hbound
  have hsq := pow_le_pow_left₀ (mul_nonneg hc (abs_nonneg t)) hbound 2
  nlinarith [sq_abs t]

/-- Global linear growth supplies positive source curvature on every unit line. -/
theorem residual_source_curvature_on_unit_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (hn : 0 < n) (node : Fin n → E) (R : E → ℝ)
    (K : Set E) (Δ c : ℝ) (hΔ : 0 < Δ) (hc : 0 ≤ c)
    (hsep : ∀ i k : Fin n, i ≠ k → Δ ≤ dist (node i) (node k))
    (j : Fin n) (hK : K ∈ 𝓝 (node j))
    (u : E) (hu : ‖u‖ = 1)
    (hzero : R (node j) = 0)
    (hC2 : ContDiff ℝ 2 (fun t : ℝ => R (node j + t • u) ^ 2))
    (hgrowth : ∀ y ∈ K,
      c * min (Δ / 4) (finiteSourceDistance hn node y) ≤ R y) :
    2 * c ^ 2 ≤
      iteratedDeriv 2 (fun t : ℝ => R (node j + t • u) ^ 2) 0 := by
  let f : ℝ → ℝ := fun t => R (node j + t • u) ^ 2
  have hfzero : f 0 = 0 := by simp [f, hzero]
  have hlocal : IsLocalMin f 0 := by
    apply Filter.Eventually.of_forall
    intro t
    rw [hfzero]
    exact sq_nonneg _
  have hderiv : deriv f 0 = 0 := hlocal.deriv_eq_zero
  have hquad := residual_quadratic_growth_on_unit_line hn node R K Δ c
    hΔ hc hsep j hK u hu hgrowth
  exact curvature_lower_of_quadratic_growth f c hC2 hfzero hderiv hquad

/-- Source curvature for a finite Fourier MUSIC squared residual. -/
theorem finiteFourierMUSIC_source_curvature_on_unit_line
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (frequency : ι → Point d) (A : Matrix ι κ ℂ)
    (node : Fin n → EuclideanSpace ℝ (Fin d))
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (hn : 0 < n) (Δ c : ℝ) (hΔ : 0 < Δ) (hc : 0 ≤ c)
    (hsep : ∀ i k : Fin n, i ≠ k → Δ ≤ dist (node i) (node k))
    (j : Fin n) (hK : K ∈ 𝓝 (node j))
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    (hzero : rankNoiseSpaceCorrelation frequency A n (ofLp (node j)) = 0)
    (hgrowth : ∀ y ∈ K,
      c * min (Δ / 4) (finiteSourceDistance hn node y) ≤
        rankNoiseSpaceCorrelation frequency A n (ofLp y)) :
    2 * c ^ 2 ≤ iteratedDeriv 2
      (fun t : ℝ => rankNoiseSpaceCorrelation frequency A n
        (ofLp (node j + t • u)) ^ 2) 0 := by
  have hQ := rankNoiseSpaceCorrelation_sq_contDiff_two_euclidean
    frequency A n
  have hline : ContDiff ℝ 2
      (fun t : ℝ => rankNoiseSpaceCorrelation frequency A n
        (ofLp (node j + t • u)) ^ 2) :=
    hQ.comp (by fun_prop)
  exact residual_source_curvature_on_unit_line hn node
    (fun z => rankNoiseSpaceCorrelation frequency A n (ofLp z))
    K Δ c hΔ hc hsep j hK u hu hzero hline hgrowth

end
end NumDetect
end LeanNumDetect
