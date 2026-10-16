import MultiTuran.Norming.ProductDiscretization
import MultiTuran.Norming.NormingConstants

/-! # Retaining every block while reserving room for a finite selector

The shortened grid has the same block starts and loses exactly `W` rows at
each right endpoint. Every selector shift remains in its original block.
Correspondence: the shortened product row set in `lem:restore`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

def shortenedGrid {d : ℕ} (G : SegmentedGrid d) (W : ℕ) : SegmentedGrid d where
  dimension_pos := G.dimension_pos
  blockCount := G.blockCount
  start := G.start
  length := fun q m => G.length q m - W
  start_zero := G.start_zero
  separated := by
    intro q i j hij
    have h := G.separated q i j hij
    have hs := Nat.sub_le (G.length q i) W
    omega

@[simp] theorem shortenedGrid_start {d : ℕ} (G : SegmentedGrid d) (W : ℕ)
    (q : Fin d) (m : G.Block q) :
    (shortenedGrid G W).start q m = G.start q m := rfl

@[simp] theorem shortenedGrid_length {d : ℕ} (G : SegmentedGrid d) (W : ℕ)
    (q : Fin d) (m : G.Block q) :
    (shortenedGrid G W).length q m = G.length q m - W := rfl

theorem width_le_blockLength {d : ℕ} (G : SegmentedGrid d) (W : ℕ)
    (hW : 2 * W < G.minThickLength) (q : Fin d) (m : G.Block q) :
    W ≤ G.length q m := by
  have h := (minThickLength_le_coordinateMinLength G q).trans
    (G.coordinateMinLength_le q m)
  unfold SegmentedGrid.thickLength at h
  omega

theorem shortenedGrid_thickLength_add {d : ℕ} (G : SegmentedGrid d) (W : ℕ)
    (hW : 2 * W < G.minThickLength) (q : Fin d) (m : G.Block q) :
    (shortenedGrid G W).thickLength q m + W = G.thickLength q m := by
  have h := width_le_blockLength G W hW q m
  simp only [SegmentedGrid.thickLength, shortenedGrid_length]
  omega

theorem shortenedGrid_half_thickLength {d : ℕ} (G : SegmentedGrid d) (W : ℕ)
    (hW : 2 * W < G.minThickLength) (q : Fin d) (m : G.Block q) :
    G.thickLength q m ≤ 2 * (shortenedGrid G W).thickLength q m := by
  have h := (minThickLength_le_coordinateMinLength G q).trans
    (G.coordinateMinLength_le q m)
  have he := shortenedGrid_thickLength_add G W hW q m
  omega

theorem shortenedGrid_coordinateRows_subset {d : ℕ} (G : SegmentedGrid d)
    (W : ℕ) (q : Fin d) :
    (shortenedGrid G W).coordinateRows q ⊆ G.coordinateRows q := by
  intro k hk
  obtain ⟨m, hm⟩ := ((shortenedGrid G W).mem_coordinateRows q k).mp hk
  obtain ⟨hlo, hhi⟩ := ((shortenedGrid G W).mem_blockRows q m k).mp hm
  apply (G.mem_coordinateRows q k).mpr
  refine ⟨m, (G.mem_blockRows q m k).mpr ⟨hlo, ?_⟩⟩
  change k ≤ G.start q m + (G.length q m - W) at hhi
  have hs := Nat.sub_le (G.length q m) W
  omega

theorem shortenedGrid_rowCount_le {d : ℕ} (G : SegmentedGrid d) (W : ℕ) :
    (shortenedGrid G W).rowCount ≤ G.rowCount := by
  apply Finset.prod_le_prod
  · intro q _
    exact Nat.zero_le _
  · intro q _
    exact Finset.card_le_card (shortenedGrid_coordinateRows_subset G W q)

theorem shortenedGrid_minThickLength_half {d : ℕ} (G : SegmentedGrid d) (W : ℕ)
    (hW : 2 * W < G.minThickLength) :
    G.minThickLength ≤ 2 * (shortenedGrid G W).minThickLength := by
  have hcoord (q : Fin d) : G.minThickLength ≤
      2 * (shortenedGrid G W).coordinateMinLength q := by
    obtain ⟨m, _, hm⟩ := Finset.exists_mem_eq_inf'
      (Finset.univ_nonempty : (Finset.univ : Finset (G.Block q)).Nonempty)
      ((shortenedGrid G W).thickLength q)
    have hmin := (minThickLength_le_coordinateMinLength G q).trans
      (G.coordinateMinLength_le q m)
    have hhalf := shortenedGrid_half_thickLength G W hW q m
    change (shortenedGrid G W).coordinateMinLength q =
      (shortenedGrid G W).thickLength q m at hm
    omega
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_inf'
    (show (Finset.univ : Finset (Fin d)).Nonempty from
      ⟨⟨0,G.dimension_pos⟩, Finset.mem_univ _⟩)
    (shortenedGrid G W).coordinateMinLength
  change (shortenedGrid G W).minThickLength =
    (shortenedGrid G W).coordinateMinLength q at hq
  rw [hq]
  exact hcoord q

/-- Each nonnegative selector shift stays inside the same original block. -/
def selectorRowShift {d : ℕ} (G : SegmentedGrid d) (W : ℕ)
    (hW : 2 * W < G.minThickLength) (u : Fin d → Fin (W + 1))
    (k : (shortenedGrid G W).Row) : G.Row := fun q =>
  ⟨(k q).val + (u q).val, by
    obtain ⟨m, hm⟩ := ((shortenedGrid G W).mem_coordinateRows q _).mp (k q).property
    obtain ⟨hlo,hhi⟩ := ((shortenedGrid G W).mem_blockRows q m _).mp hm
    have hlen := width_le_blockLength G W hW q m
    have hu := (u q).isLt
    apply (G.mem_coordinateRows q _).mpr
    refine ⟨m, (G.mem_blockRows q m _).mpr ⟨?_, ?_⟩⟩
    · change G.start q m ≤ (k q).val at hlo
      omega
    · change (k q).val ≤ G.start q m + (G.length q m - W) at hhi
      omega⟩

theorem selectorRowShift_injective {d : ℕ} (G : SegmentedGrid d) (W : ℕ)
    (hW : 2 * W < G.minThickLength) (u : Fin d → Fin (W + 1)) :
    Function.Injective (selectorRowShift G W hW u) := by
  intro k l h
  funext q
  apply Subtype.ext
  have hq := congrArg (fun z : G.Row => (z q).val) h
  change (k q).val + (u q).val = (l q).val + (u q).val at hq
  omega

@[simp] theorem selectorRowShift_rowPoint {d : ℕ} (G : SegmentedGrid d) (W : ℕ)
    (hW : 2 * W < G.minThickLength) (u : Fin d → Fin (W + 1))
    (k : (shortenedGrid G W).Row) (q : Fin d) :
    G.rowPoint (selectorRowShift G W hW u k) q =
      (shortenedGrid G W).rowPoint k q + (u q : ℕ) := by
  change (((k q).val + (u q).val : ℕ) : ℝ) = _
  push_cast
  rfl

end
end LeanNumDetect.MultiTuran.MultiClump
