import MultiTuran.MultiClump.GeneralProduct
import MultiTuran.MultiClump.RowShift
import MultiTuran.MultiClump.DistinctNodes

/-! # General product rows, an arbitrary enclosing box, and the actual largest clump

The measured rows may start at any common coordinate offset. The enclosing
box may be larger than their span. The proof constructs clump slots, derives
positive minimum separation from torus distinctness, and uses the actual
maximum fiber cardinality throughout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

/-- The complete product-row multi-clump theorem with the article's literal
largest clump size. All analytic, interpolation, and norming estimates are
proved; the public hypotheses are geometric and the displayed `B_d` threshold.
`H` supplies only the chosen enclosing-box dimensions. -/
theorem multiClumpProduct_minimumSingularValue_lower
    {d n A : ℕ} (G H : SegmentedGrid d) (Y : Fin n → Point d)
    (label : Fin n → Fin A) (offset : Point d)
    (houter : ∀ q, G.aperture q ≤ H.aperture q)
    (hd : 2 ≤ d) (hn : 2 ≤ n) (hsurj : Function.Surjective label)
    (hdistinct : ∀ i j, i ≠ j → 0 < torusLInfDistance (Y i) (Y j))
    {τ C_B : ℝ} (hτ : 0 < τ) (hτupper : τ ≤ Real.pi/(2*(d : ℝ)))
    (hC_B : 24 ≤ C_B)
    (hsame : ∀ i j, label i = label j → torusLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, label i ≠ label j →
      max τ (16*Real.pi*d*(largestClumpSize label : ℝ)^2/G.minThickLength) <
        torusLInfDistance (Y i) (Y j))
    (hN : max (16*n) (32*d^2*largestClumpSize label) ≤ H.minAperture)
    (hblock : multiClumpBlockConstant d C_B * G.rowCount *
      ((largestClumpSize label : ℝ)^(4*d+5)/(G.minThickLength : ℝ)^(d+1)+
        (largestClumpSize label : ℝ)^(4*d+1)*τ/(G.minThickLength : ℝ)^d) ≤ 1) :
    generalProductArrayLowerBound G H Y (largestClumpSize label) ≤
      matrixSingularValue (vandermondeMatrix (fun k : G.Row => G.rowPoint k+offset) Y) (n-1) := by
  have hn0 : 0 < n := by omega
  obtain ⟨C,hC⟩ := NumDetect.exists_clumpSlots (x := Y) label
    (clumpFiber_card_le_largestClumpSize label)
  have hsurjC : Function.Surjective C.label := by rw [hC]; exact hsurj
  have hsameC : ∀ i j, C.label i = C.label j → torusLInfDistance (Y i) (Y j) ≤ τ := by
    simpa only [hC] using hsame
  have hcrossC : ∀ i j, C.label i ≠ C.label j →
      max τ (16*Real.pi*d*(largestClumpSize label : ℝ)^2/G.minThickLength) <
        torusLInfDistance (Y i) (Y j) := by
    simpa only [hC] using hcross
  rw [generalizedVandermonde_rowShift_minimumSingularValue G Y hn0 offset]
  exact generalProductArrayLowerBound_le_minimumSingularValue G H Y C houter hd hn
    (largestClumpSize_pos label hn0) (largestClumpSize_le_sourceCount label) hsurjC
    hτ hτupper hC_B (nodeSeparation_pos_of_pairwise_torusDistance_pos Y hn hdistinct)
    hsameC hcrossC hN hblock

end
end LeanNumDetect.MultiTuran.MultiClump
