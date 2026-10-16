import MultiTuran.ConsecutiveWindow.CubeBounds
import MultiTuran.MultiClump.DistinctNodes

/-! # Literal unrestricted-clump full-aperture lemma

Correspondence: `lem:aperture`. The partition interface uses the actual
maximum fiber cardinality and imposes no within-clump diameter bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
open MultiClump
noncomputable section

theorem fullAperture_clump_minimumSingularValue_lower
    {d n A N : ℕ} (Y : Fin n → Point d) (label : Fin n → Fin A)
    (hd : 2 ≤ d) (hn : 2 ≤ n) (_hsurj : Function.Surjective label)
    (hpair : ∀ i j, i ≠ j → 0 < torusLInfDistance (Y i) (Y j))
    (hN : max (16*n) (32*d^2*largestClumpSize label) ≤ N)
    (hcross : ∀ i j, label i ≠ label j →
      16*Real.pi*d*largestClumpSize label/N < torusLInfDistance (Y i) (Y j)) :
    1/Real.sqrt ((n : ℝ)*8^largestClumpSize label) *
      ((N : ℝ)/(6*largestClumpSize label))^((d : ℝ)/2) *
      min 1 ((N : ℝ)*nodeSeparation Y/(8*Real.pi*largestClumpSize label))^
        (largestClumpSize label-1) ≤
      matrixSingularValue (fullCubeVandermonde 1 (fullApertureCubeSide N) Y) (n-1) := by
  obtain ⟨C,hC⟩ := NumDetect.exists_clumpSlots (x := Y) label
    (clumpFiber_card_le_largestClumpSize label)
  have hcrossC (i j : Fin n) (hij : C.label i ≠ C.label j) :
      16*Real.pi*d*largestClumpSize label/N < torusLInfDistance (Y i) (Y j) := by
    rw [hC] at hij
    exact hcross i j hij
  exact selected_fullAperture_unrestricted_clump_lower C hd hn
    (largestClumpSize_pos label (by omega)) (largestClumpSize_le_sourceCount label)
    hN hcrossC (nodeSeparation_pos_of_pairwise_torusDistance_pos Y hn hpair)
    (nodeSeparation_le_pair Y)

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
