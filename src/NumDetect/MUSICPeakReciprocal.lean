import NumDetect.MUSICPeakSelection
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- The extended MUSIC imaging function. At a zero of the residual its value
is `∞`, matching the interpretation of an exact MUSIC peak. -/
def extendedMUSICImaging {α : Type*} (R : α → ℝ) (x : α) : ℝ≥0∞ :=
  (ENNReal.ofReal (R x))⁻¹

/-- On a field of view where the residual is nonnegative, local maxima of the
extended MUSIC imaging function are exactly local minima of the residual. -/
theorem isLocalMaxOn_extendedMUSICImaging_iff
    {α : Type*} [TopologicalSpace α]
    (R : α → ℝ) (K : Set α) (x : α)
    (hpos : ∀ y ∈ K, 0 ≤ R y) :
    IsLocalMaxOn (extendedMUSICImaging R) K x ↔ IsLocalMinOn R K x := by
  constructor
  · intro h
    change ∀ᶠ y in 𝓝[K] x, R x ≤ R y
    filter_upwards [h, self_mem_nhdsWithin] with y hymax hyK
    have hle : ENNReal.ofReal (R x) ≤ ENNReal.ofReal (R y) :=
      ENNReal.inv_le_inv.mp hymax
    exact (ENNReal.ofReal_le_ofReal_iff (hpos y hyK)).mp hle
  · intro h
    change ∀ᶠ y in 𝓝[K] x,
      extendedMUSICImaging R y ≤ extendedMUSICImaging R x
    filter_upwards [h] with y hymin
    exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hymin)

/-- Residual height and MUSIC peak height have opposite strict orders, even
when the residual at one point vanishes. -/
theorem extendedMUSICImaging_lt_iff_residual_gt
    {α : Type*} (R : α → ℝ) (x y : α)
    (hx : 0 ≤ R x) :
    extendedMUSICImaging R y < extendedMUSICImaging R x ↔ R x < R y := by
  unfold extendedMUSICImaging
  rw [ENNReal.inv_lt_inv]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx

/-- The top local minima of a nonnegative squared MUSIC residual are precisely
the top local peaks of its extended reciprocal imaging function. -/
theorem top_squaredResidual_minima_are_extendedMUSIC_peaks
    {α : Type*} [TopologicalSpace α] {n : ℕ}
    (R : α → ℝ) (K : Set α) (estimate : Fin n → α)
    (hpos : ∀ y ∈ K, 0 ≤ R y)
    (hestK : ∀ i, estimate i ∈ K)
    (hlocal : ∀ i,
      IsLocalMinOn (fun y => R y ^ 2) K (estimate i))
    (htop : ∀ y, y ∈ K →
      IsLocalMinOn (fun z => R z ^ 2) K y →
      y ∉ Set.range estimate → ∀ i, R (estimate i) ^ 2 < R y ^ 2) :
    (∀ i, IsLocalMaxOn (extendedMUSICImaging R) K (estimate i)) ∧
    (∀ y, y ∈ K →
      IsLocalMaxOn (extendedMUSICImaging R) K y →
      y ∉ Set.range estimate →
        ∀ i, extendedMUSICImaging R y <
          extendedMUSICImaging R (estimate i)) := by
  constructor
  · intro i
    rw [isLocalMaxOn_extendedMUSICImaging_iff R K _ hpos]
    exact (localMinOn_sq_iff_of_nonneg R K _ (hestK i) hpos).mp (hlocal i)
  · intro y hyK hyLocal hyNot i
    have hyMin : IsLocalMinOn (fun z => R z ^ 2) K y :=
      (localMinOn_sq_iff_of_nonneg R K y hyK hpos).mpr
        ((isLocalMaxOn_extendedMUSICImaging_iff R K y hpos).mp hyLocal)
    have hstrict := htop y hyK hyMin hyNot i
    have hresidual : R (estimate i) < R y :=
      (sq_lt_sq₀ (hpos (estimate i) (hestK i)) (hpos y hyK)).mp hstrict
    exact (extendedMUSICImaging_lt_iff_residual_gt R (estimate i) y
      (hpos (estimate i) (hestK i))).mpr hresidual

end
end NumDetect
end LeanNumDetect
