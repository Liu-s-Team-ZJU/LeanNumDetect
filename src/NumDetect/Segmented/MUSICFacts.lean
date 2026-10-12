import NumDetect.Segmented.Main
import NumDetect.Segmented.MatrixFacts
import NumDetect.Preliminaries.PeriodicGeometry

/-! Positivity and sample cardinality facts for segmented MUSIC stability. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Every factor in the explicit segmented MUSIC constant is positive. -/
theorem segmentedVandermondeLowerBound_pos
    {d n A nStar m r D : ℕ} {τ η β : ℝ}
    (μ : AtomicMeasure d n)
    (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hm : 1 ≤ m) (hD : m < D)
    (hβ : 1 / (2 * Real.log 2) < β)
    (hr : 2 * nStar ≤ r) :
    0 < segmentedVandermondeLowerBound d n nStar m r D β
      (periodicMinimumL1Separation μ.node hn) := by
  have hnStarTwo : 2 ≤ nStar := hclumps.1
  have hnStar : 0 < nStar := by omega
  have hrPos : 0 < r :=
    lt_of_lt_of_le (by omega : 0 < 2 * nStar) hr
  have hDPos : 0 < D := Nat.zero_lt_of_lt (hm.trans_lt hD)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβPos : 0 < β := (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
  have hexp : Real.exp (1 / (2 * β)) < 2 := by
    calc
      Real.exp (1 / (2 * β)) < Real.exp (Real.log 2) := by
        rw [Real.exp_lt_exp]
        apply (div_lt_iff₀ (by positivity : 0 < 2 * β)).2
        have h := (div_lt_iff₀
          (by positivity : 0 < 2 * Real.log 2)).1 hβ
        nlinarith
      _ = 2 := Real.exp_log (by norm_num)
  have hsep : 0 < periodicMinimumL1Separation μ.node hn :=
    periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
  unfold segmentedVandermondeLowerBound
  positivity

/-- The segmented row set has more than `n` samples under `d ≥ 1` and `m ≥ n`. -/
theorem sourceCount_lt_card_segmentedIndex
    {d n m r : ℕ} (hd : 1 ≤ d) (hmn : n ≤ m) :
    n < Fintype.card (SegmentedIndex d m r) := by
  let b := (r + 1) * (m + 1)
  have hmb : m < b := by
    dsimp [b]
    nlinarith
  have hb : 1 ≤ b := by
    have : 0 < b := by
      dsimp [b]
      exact Nat.mul_pos (Nat.succ_pos r) (Nat.succ_pos m)
    omega
  have hbpow : b ≤ b ^ d := by
    simpa only [pow_one] using pow_le_pow_right₀ hb hd
  have : n < b ^ d := (hmn.trans_lt hmb).trans_le hbpow
  simpa only [SegmentedIndex, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_prod] using this

end

end NumDetect
end LeanNumDetect
