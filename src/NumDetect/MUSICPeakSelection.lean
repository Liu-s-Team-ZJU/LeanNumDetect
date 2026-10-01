import NumDetect.SegmentedMUSICLocation
import Mathlib.Analysis.Convex.Extrema

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Squaring a nonnegative residual preserves its local minima on the field of
view, including possible exact zeros. -/
theorem localMinOn_sq_iff_of_nonneg
    {α : Type*} [TopologicalSpace α]
    (Rσ : α → ℝ) (K : Set α) (x : α)
    (hx : x ∈ K) (hpos : ∀ y ∈ K, 0 ≤ Rσ y) :
    IsLocalMinOn (fun y => Rσ y ^ 2) K x ↔ IsLocalMinOn Rσ K x := by
  constructor
  · intro h
    change ∀ᶠ y in 𝓝[K] x, Rσ x ≤ Rσ y
    filter_upwards [h, self_mem_nhdsWithin] with y hymin hyK
    exact (sq_le_sq₀ (hpos x hx) (hpos y hyK)).mp hymin
  · intro h
    change ∀ᶠ y in 𝓝[K] x, Rσ x ^ 2 ≤ Rσ y ^ 2
    filter_upwards [h, self_mem_nhdsWithin] with y hymin hyK
    exact (sq_le_sq₀ (hpos x hx) (hpos y hyK)).mpr hymin

/-- An abstract continuous peak-selection result. The local curvature of the
noisy squared MUSIC residual enters through strict convexity on one closed
neighborhood per source. -/
theorem exists_top_local_minima_of_strictConvex
    {d n : ℕ}
    (node : Fin n → EuclideanSpace ℝ (Fin d))
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (Q : EuclideanSpace ℝ (Fin d) → ℝ) (r β : ℝ)
    (hr : 0 < r) (hK : IsCompact K)
    (hnodeK : ∀ i, node i ∈ K)
    (hsep : ∀ i j, i ≠ j → 2 * r < dist (node i) (node j))
    (hcont : ContinuousOn Q K)
    (hstrict : ∀ i, StrictConvexOn ℝ
      (K ∩ Metric.closedBall (node i) r) Q)
    (hlow : ∀ i, Q (node i) < β)
    (hboundary : ∀ i y, y ∈ K → dist y (node i) = r → β ≤ Q y)
    (hfar : ∀ y, y ∈ K →
      (∀ i, r ≤ dist y (node i)) → β ≤ Q y) :
    ∃ estimate : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, estimate i ∈ K ∧ dist (estimate i) (node i) < r ∧
        IsLocalMinOn Q K (estimate i) ∧
        Q (estimate i) ≤ Q (node i)) ∧
      Function.Injective estimate ∧
      (∀ y, y ∈ K → IsLocalMinOn Q K y →
        y ∉ Set.range estimate →
          ∀ i, Q (estimate i) < Q y) := by
  classical
  let U (i : Fin n) : Set (EuclideanSpace ℝ (Fin d)) :=
    K ∩ Metric.closedBall (node i) r
  have hUcompact (i : Fin n) : IsCompact (U i) :=
    hK.inter_right Metric.isClosed_closedBall
  have hUnonempty (i : Fin n) : (U i).Nonempty := by
    refine ⟨node i, hnodeK i, ?_⟩
    simpa only [Metric.mem_closedBall, dist_self] using hr.le
  have hUcont (i : Fin n) : ContinuousOn Q (U i) :=
    hcont.mono inter_subset_left
  have hmin (i : Fin n) : ∃ x ∈ U i, IsMinOn Q (U i) x := by
    obtain ⟨x, hx, hxmin⟩ :=
      (hUcompact i).exists_isMinOn (hUnonempty i) (hUcont i)
    exact ⟨x, hx, hxmin⟩
  choose estimate hestU hestMin using hmin
  have hestNear (i : Fin n) : dist (estimate i) (node i) < r := by
    have hle : dist (estimate i) (node i) ≤ r := (hestU i).2
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · have hval : Q (estimate i) ≤ Q (node i) :=
        hestMin i ⟨hnodeK i, by simp [hr.le]⟩
      have hb := hboundary i (estimate i) (hestU i).1 heq
      linarith [hlow i]
  have hestLocal (i : Fin n) : IsLocalMinOn Q K (estimate i) := by
    have hwithin : Metric.closedBall (node i) r ∈ 𝓝[K] (estimate i) :=
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds_of_mem
        (show estimate i ∈ Metric.ball (node i) r from by
          simpa only [Metric.mem_ball, dist_comm] using hestNear i))
    have hnhds : 𝓝[U i] (estimate i) = 𝓝[K] (estimate i) := by
      exact nhdsWithin_inter_of_mem' hwithin
    change IsMinFilter Q (𝓝[K] (estimate i)) (estimate i)
    rw [← hnhds]
    exact (hestMin i).localize
  have hestInj : Function.Injective estimate := by
    intro i j hij
    by_contra hne
    have hs := hsep i j hne
    have ht := dist_triangle (node i) (estimate i) (node j)
    have hleft : dist (node i) (estimate i) < r := by
      simpa only [dist_comm] using hestNear i
    have hright : dist (estimate i) (node j) < r := by
      rw [hij]
      exact hestNear j
    linarith
  refine ⟨estimate, (fun i => ⟨(hestU i).1, hestNear i, hestLocal i,
    hestMin i ⟨hnodeK i, by simp [hr.le]⟩⟩), hestInj, ?_⟩
  intro y hyK hyLocal hyNot i
  by_cases hnear : ∃ j, dist y (node j) < r
  · obtain ⟨j, hj⟩ := hnear
    have hyU : y ∈ U j := ⟨hyK, hj.le⟩
    have hlocalU : IsLocalMinOn Q (U j) y :=
      hyLocal.on_subset inter_subset_left
    have hglobalU : IsMinOn Q (U j) y :=
      IsMinOn.of_isLocalMinOn_of_convexOn hyU hlocalU (hstrict j).convexOn
    have heq : y = estimate j :=
      (hstrict j).eq_of_isMinOn hglobalU (hestMin j) hyU (hestU j)
    exact False.elim (hyNot ⟨j, heq.symm⟩)
  · have hfar' : β ≤ Q y := hfar y hyK (by
      intro j
      exact le_of_not_gt (fun hj => hnear ⟨j, hj⟩))
    have hval : Q (estimate i) ≤ Q (node i) :=
      hestMin i ⟨hnodeK i, by simp [hr.le]⟩
    linarith [hlow i]

/-- The usual linear-growth argument gives the location error for each
continuous local peak selected by minimizing the squared noisy residual in its
source neighborhood. -/
theorem top_local_minima_location_bound
    {α : Type*} [PseudoMetricSpace α] {n : ℕ}
    (node estimate : Fin n → α) (K : Set α)
    (R Rσ : α → ℝ) (r c ε : ℝ)
    (hc : 0 < c)
    (hnodeK : ∀ i, node i ∈ K)
    (hestK : ∀ i, estimate i ∈ K)
    (hnear : ∀ i, dist (estimate i) (node i) < r)
    (hzero : ∀ i, R (node i) = 0)
    (hpert : ∀ y ∈ K, |Rσ y - R y| ≤ ε)
    (hRσpos : ∀ y ∈ K, 0 ≤ Rσ y)
    (hminSquare : ∀ i, Rσ (estimate i) ^ 2 ≤ Rσ (node i) ^ 2)
    (hgrowthLocal : ∀ i y, y ∈ K → dist y (node i) < r →
      c * dist y (node i) ≤ R y) :
    ∀ i, dist (estimate i) (node i) ≤ 2 * ε / c := by
  intro i
  have hnoisyLe : Rσ (estimate i) ≤ Rσ (node i) :=
    (sq_le_sq₀ (hRσpos (estimate i) (hestK i))
      (hRσpos (node i) (hnodeK i))).mp (hminSquare i)
  have hnodeNoise := hpert (node i) (hnodeK i)
  rw [hzero i, sub_zero] at hnodeNoise
  have hestNoise := hpert (estimate i) (hestK i)
  have hreal : R (estimate i) ≤ 2 * ε := by
    have h₁ := (abs_le.mp hnodeNoise).2
    have h₂ := (abs_le.mp hestNoise).1
    linarith
  have hbound := hgrowthLocal i (estimate i) (hestK i) (hnear i)
  exact (le_div_iff₀ hc).2 (by nlinarith)

/-- Continuous selection of the `n` highest MUSIC peaks and its location
error, conditional on local strict convexity of the noisy squared residual and
the boundary/exterior value gap. -/
theorem exists_top_MUSIC_peaks_with_location_bound
    {d n : ℕ}
    (node : Fin n → EuclideanSpace ℝ (Fin d))
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (R Rσ : EuclideanSpace ℝ (Fin d) → ℝ) (r β c ε : ℝ)
    (hr : 0 < r) (hc : 0 < c)
    (hK : IsCompact K)
    (hnodeK : ∀ i, node i ∈ K)
    (hsep : ∀ i j, i ≠ j → 2 * r < dist (node i) (node j))
    (hcont : ContinuousOn (fun y => Rσ y ^ 2) K)
    (hstrict : ∀ i, StrictConvexOn ℝ
      (K ∩ Metric.closedBall (node i) r) (fun y => Rσ y ^ 2))
    (hlow : ∀ i, Rσ (node i) ^ 2 < β)
    (hboundary : ∀ i y, y ∈ K → dist y (node i) = r →
      β ≤ Rσ y ^ 2)
    (hfar : ∀ y, y ∈ K →
      (∀ i, r ≤ dist y (node i)) → β ≤ Rσ y ^ 2)
    (hzero : ∀ i, R (node i) = 0)
    (hpert : ∀ y ∈ K, |Rσ y - R y| ≤ ε)
    (hRσpos : ∀ y ∈ K, 0 ≤ Rσ y)
    (hgrowthLocal : ∀ i y, y ∈ K → dist y (node i) < r →
      c * dist y (node i) ≤ R y) :
    ∃ estimate : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, estimate i ∈ K ∧
        IsLocalMinOn (fun y => Rσ y ^ 2) K (estimate i) ∧
        dist (estimate i) (node i) ≤ 2 * ε / c) ∧
      Function.Injective estimate ∧
      (∀ y, y ∈ K → IsLocalMinOn (fun z => Rσ z ^ 2) K y →
        y ∉ Set.range estimate →
          ∀ i, Rσ (estimate i) ^ 2 < Rσ y ^ 2) := by
  obtain ⟨estimate, hest, hinj, htop⟩ :=
    exists_top_local_minima_of_strictConvex node K (fun y => Rσ y ^ 2)
      r β hr hK hnodeK hsep hcont hstrict hlow hboundary hfar
  have hloc := top_local_minima_location_bound node estimate K R Rσ
    r c ε hc hnodeK (fun i => (hest i).1)
    (fun i => (hest i).2.1) hzero hpert hRσpos
    (fun i => (hest i).2.2.2) hgrowthLocal
  exact ⟨estimate, (fun i => ⟨(hest i).1, (hest i).2.2.1, hloc i⟩),
    hinj, htop⟩

/-- The value gap and local growth needed by the peak-selection theorem follow
from a single global residual-growth inequality. Only the strict-convexity
step remains as a separate analytic hypothesis. -/
theorem exists_top_MUSIC_peaks_of_globalGrowth_and_strictConvex
    {d n : ℕ} (hn : 0 < n)
    (node : Fin n → EuclideanSpace ℝ (Fin d))
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (R Rσ : EuclideanSpace ℝ (Fin d) → ℝ)
    (Δ r c ε : ℝ)
    (hr : 0 < r) (hfour : 4 * r ≤ Δ) (hc : 0 < c)
    (hsmall : ε < c * r / 2)
    (hK : IsCompact K) (hnodeK : ∀ i, node i ∈ K)
    (hsep : ∀ i j, i ≠ j → Δ ≤ dist (node i) (node j))
    (hcont : ContinuousOn Rσ K)
    (hstrict : ∀ i, StrictConvexOn ℝ
      (K ∩ Metric.closedBall (node i) r) (fun y => Rσ y ^ 2))
    (hzero : ∀ i, R (node i) = 0)
    (hpert : ∀ y ∈ K, |Rσ y - R y| ≤ ε)
    (hRσpos : ∀ y ∈ K, 0 ≤ Rσ y)
    (hgrowth : ∀ y ∈ K,
      c * min (Δ / 4) (finiteSourceDistance hn node y) ≤ R y) :
    ∃ estimate : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, estimate i ∈ K ∧
        IsLocalMinOn (fun y => Rσ y ^ 2) K (estimate i) ∧
        dist (estimate i) (node i) ≤ 2 * ε / c) ∧
      Function.Injective estimate ∧
      (∀ y, y ∈ K → IsLocalMinOn (fun z => Rσ z ^ 2) K y →
        y ∉ Set.range estimate →
          ∀ i, Rσ (estimate i) ^ 2 < Rσ y ^ 2) := by
  have hΔ : 0 < Δ := by linarith
  have hsepR : ∀ i j, i ≠ j → 2 * r < dist (node i) (node j) := by
    intro i j hij
    have := hsep i j hij
    linarith
  have hεnonneg : 0 ≤ ε := by
    let i : Fin n := ⟨0, hn⟩
    exact (abs_nonneg _).trans (hpert (node i) (hnodeK i))
  have hthreshold : 0 < c * r - ε := by
    have hcr : 0 < c * r := mul_pos hc hr
    linarith
  have hnodeLow : ∀ i, Rσ (node i) ^ 2 < (c * r - ε) ^ 2 := by
    intro i
    have h := hpert (node i) (hnodeK i)
    rw [hzero i, sub_zero] at h
    have hleft : Rσ (node i) ≤ ε := (abs_le.mp h).2
    apply (sq_lt_sq₀ (hRσpos (node i) (hnodeK i)) hthreshold.le).2
    linarith
  have hdistanceAway (y : EuclideanSpace ℝ (Fin d))
      (haway : ∀ i, r ≤ dist y (node i)) :
      r ≤ finiteSourceDistance hn node y := by
    apply (Finset.le_inf'_iff (fin_univ_nonempty hn) _).2
    intro j _
    exact haway j
  have hresAway (y : EuclideanSpace ℝ (Fin d)) (hyK : y ∈ K)
      (haway : ∀ i, r ≤ dist y (node i)) :
      c * r - ε ≤ Rσ y := by
    have hdist := hdistanceAway y haway
    have hmin : r ≤ min (Δ / 4) (finiteSourceDistance hn node y) :=
      le_min (by linarith) hdist
    have hgrow := hgrowth y hyK
    have hnoise := hpert y hyK
    have hfirst := (abs_le.mp hnoise).1
    nlinarith [mul_le_mul_of_nonneg_left hmin hc.le]
  have hfarQ : ∀ y, y ∈ K →
      (∀ i, r ≤ dist y (node i)) →
      (c * r - ε) ^ 2 ≤ Rσ y ^ 2 := by
    intro y hyK haway
    exact (sq_le_sq₀ hthreshold.le (hRσpos y hyK)).2
      (hresAway y hyK haway)
  have hboundaryQ : ∀ i y, y ∈ K → dist y (node i) = r →
      (c * r - ε) ^ 2 ≤ Rσ y ^ 2 := by
    intro i y hyK hi
    apply hfarQ y hyK
    intro j
    by_cases hij : i = j
    · simpa [hij] using hi.ge
    · have hs := hsep i j hij
      have ht := dist_triangle (node i) y (node j)
      have hi' : dist (node i) y = r := by simpa only [dist_comm] using hi
      linarith
  have hnearDist (i : Fin n) (y : EuclideanSpace ℝ (Fin d))
      (hi : dist y (node i) < r) :
      finiteSourceDistance hn node y = dist y (node i) := by
    apply le_antisymm
    · exact Finset.inf'_le _ (Finset.mem_univ i)
    · apply (Finset.le_inf'_iff (fin_univ_nonempty hn) _).2
      intro j _
      by_cases hij : i = j
      · simp [hij]
      · have hs := hsep i j hij
        have ht := dist_triangle (node i) y (node j)
        have hi' : dist (node i) y < r := by simpa only [dist_comm] using hi
        linarith
  have hgrowthLocal : ∀ i y, y ∈ K → dist y (node i) < r →
      c * dist y (node i) ≤ R y := by
    intro i y hyK hi
    have hgrow := hgrowth y hyK
    rw [hnearDist i y hi, min_eq_right (by linarith)] at hgrow
    exact hgrow
  exact exists_top_MUSIC_peaks_with_location_bound node K R Rσ r
    ((c * r - ε) ^ 2) c ε hr hc hK hnodeK hsepR
    (hcont.pow 2) hstrict hnodeLow hboundaryQ hfarQ
    hzero hpert hRσpos hgrowthLocal

end
end NumDetect
end LeanNumDetect
