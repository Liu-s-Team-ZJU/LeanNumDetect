import MultiTuran.ConsecutiveWindow.Norming
import MultiTuran.ConsecutiveWindow.BoundFormula
import MultiTuran.ConsecutiveWindow.CubeBounds
import MultiTuran.MultiClump.DistinctNodes
import MultiTuran.MultiClump.RowShift

/-! # The complete consecutive-window multi-clump theorem

Correspondence: `thm:main` of the supplement. Public partition statements
use the actual largest fiber cardinality. Chart, norming, interpolation,
and full-cube lower bounds are constructed within the proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
open MultiClump
noncomputable section

theorem consecutiveWindowProductArrayLowerBound_le_minimumSingularValue_of_slots
    {d n A nStar : ℕ} (G H : SegmentedGrid d) (Y : Fin n → Point d)
    (C : NumDetect.ClumpSlots (A := A) (nStar := nStar) Y)
    (houter : ∀ q, G.aperture q ≤ H.aperture q)
    (hd : 2 ≤ d) (hn : 2 ≤ n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hsep : 0 < nodeSeparation Y)
    (hblocks : ∀ q, n ≤ G.coordinateMinLength q)
    (hN : 10*nStar ≤ H.minAperture)
    (hcross : ∀ i j, C.label i ≠ C.label j →
      10*Real.pi*d*nStar/H.minAperture < torusLInfDistance (Y i) (Y j))
    (hθupper : nodeSeparation Y ≤ 5*Real.pi*nStar/H.minAperture) :
    consecutiveWindowProductArrayLowerBound G H Y nStar ≤
      matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  obtain ⟨center,winding,_hchart,hnorming⟩ :=
    exists_chart_continuousNorming G Y hn hblocks
  let Z := chartNodes Y center winding
  let C' : NumDetect.ClumpSlots (A := A) (nStar := nStar) Z :=
    {label := C.label,slot := C.slot,injective := C.injective}
  have hcrossZ (i j : Fin n) (hij : C'.label i ≠ C'.label j) :
      10*Real.pi*d*nStar/H.minAperture < torusLInfDistance (Z i) (Z j) := by
    simpa only [Z,torusLInfDistance_chartNodes] using hcross i j hij
  have hsepZ : 0 < nodeSeparation Z := by
    simpa only [Z,nodeSeparation_chartNodes] using hsep
  have hθupperZ : nodeSeparation Z ≤ 5*Real.pi*nStar/H.minAperture := by
    simpa only [Z,nodeSeparation_chartNodes] using hθupper
  have hcube := selected_multiClumpCubeLowerBound_le H Z C' hd hn hs hsize hN hcrossZ
    hsepZ hθupperZ
  have hN4 : 4 ≤ H.minAperture := by
    omega
  have hfull := (fullApertureCubeSide_properties hN4).2.1
  have hfinal := consecutiveWindowProductArrayLowerBound_le_of_norming_cube
    G H Z houter (by omega : 0 < n) hnorming hfull hcube
  simpa only [Z,consecutiveWindowProductArrayLowerBound_chartNodes,
    generalizedVandermonde_minimumSingularValue_chartNodes] using hfinal

/-- The complete partition theorem on the actual measured product and an
independently specified enclosing aperture. The partition has nonempty
fibers, and `largestClumpSize label` is precisely the article's `nStar`. -/
theorem consecutiveWindowProductArray_minimumSingularValue_lower
    {d n A : ℕ} (G H : SegmentedGrid d) (Y : Fin n → Point d)
    (label : Fin n → Fin A) (houter : ∀ q, G.aperture q ≤ H.aperture q)
    (hd : 2 ≤ d) (hn : 2 ≤ n) (_hsurj : Function.Surjective label)
    (hpair : ∀ i j, i ≠ j → 0 < torusLInfDistance (Y i) (Y j))
    (hblocks : ∀ q, n ≤ G.coordinateMinLength q)
    (hN : 10*largestClumpSize label ≤ H.minAperture)
    (hcross : ∀ i j, label i ≠ label j →
      10*Real.pi*d*largestClumpSize label/H.minAperture < torusLInfDistance (Y i) (Y j))
    (hθupper : nodeSeparation Y ≤ 5*Real.pi*largestClumpSize label/H.minAperture) :
    Real.sqrt (windowNormingConstant d n/((n : ℝ)*6^largestClumpSize label)) *
      (2/(Real.pi*n))^d * enclosingLongBlockFactor G H *
      (enclosingFillingRatio G H/(multidimensionalTuranConstant*d))^(n-1) *
      ((H.minAperture : ℝ)/(3*largestClumpSize label))^((d : ℝ)/2) *
      ((H.minAperture : ℝ)*nodeSeparation Y/(5*Real.pi*largestClumpSize label))^
        (largestClumpSize label-1) ≤
      matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  obtain ⟨C,hC⟩ := NumDetect.exists_clumpSlots (x := Y) label
    (clumpFiber_card_le_largestClumpSize label)
  have hcrossC (i j : Fin n) (hij : C.label i ≠ C.label j) :
      10*Real.pi*d*largestClumpSize label/H.minAperture < torusLInfDistance (Y i) (Y j) := by
    rw [hC] at hij
    exact hcross i j hij
  exact consecutiveWindowProductArrayLowerBound_le_minimumSingularValue_of_slots
    G H Y C houter hd hn (largestClumpSize_pos label (by omega))
    (largestClumpSize_le_sourceCount label)
    (nodeSeparation_pos_of_pairwise_torusDistance_pos Y hn hpair) hblocks hN hcrossC hθupper

/-- Literal same-aperture version of `thm:main`, including the original
long-block and filling-ratio factors. -/
theorem consecutiveWindowArray_minimumSingularValue_lower
    {d n A : ℕ} (G : SegmentedGrid d) (Y : Fin n → Point d)
    (label : Fin n → Fin A) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (hsurj : Function.Surjective label)
    (hpair : ∀ i j, i ≠ j → 0 < torusLInfDistance (Y i) (Y j))
    (hblocks : ∀ q, n ≤ G.coordinateMinLength q)
    (hN : 10*largestClumpSize label ≤ G.minAperture)
    (hcross : ∀ i j, label i ≠ label j →
      10*Real.pi*d*largestClumpSize label/G.minAperture < torusLInfDistance (Y i) (Y j))
    (hθupper : nodeSeparation Y ≤ 5*Real.pi*largestClumpSize label/G.minAperture) :
    Real.sqrt (windowNormingConstant d n/((n : ℝ)*6^largestClumpSize label)) *
      (2/(Real.pi*n))^d * G.rhoL *
      (G.fillingRatio/(multidimensionalTuranConstant*d))^(n-1) *
      ((G.minAperture : ℝ)/(3*largestClumpSize label))^((d : ℝ)/2) *
      ((G.minAperture : ℝ)*nodeSeparation Y/(5*Real.pi*largestClumpSize label))^
        (largestClumpSize label-1) ≤
      matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  simpa only [enclosingLongBlockFactor_self,enclosingFillingRatio_self] using
    consecutiveWindowProductArray_minimumSingularValue_lower G G Y label
      (fun _ => le_rfl) hd hn hsurj hpair hblocks hN hcross hθupper

/-- Actual blocks with arbitrary starting positions and an arbitrary
enclosing box. Normalizing the starts preserves every measured row and
the least singular value; all aperture factors use the supplied box. -/
theorem consecutiveWindowRawProduct_minimumSingularValue_lower
    {d n A : ℕ} (hd : 2 ≤ d) (hn : 2 ≤ n)
    (r : Fin d → ℕ) (a l : (q : Fin d) → Fin (r q+1) → ℕ)
    (hseparated : ∀ q (i j : Fin (r q+1)), i < j → a q i+l q i+1 ≤ a q j)
    (N : Fin d → ℕ) (hNpos : ∀ q, 0 < N q)
    (hlast : ∀ q, a q ⟨r q,by omega⟩+l q ⟨r q,by omega⟩+1 ≤ N q)
    (Y : Fin n → Point d) (label : Fin n → Fin A)
    (hsurj : Function.Surjective label)
    (hpair : ∀ i j, i ≠ j → 0 < torusLInfDistance (Y i) (Y j))
    (hblocks : ∀ q m, n-1 ≤ l q m)
    (hN : 10*largestClumpSize label ≤
      (enclosingBoxGrid (by omega : 0 < d) N hNpos).minAperture)
    (hcross : ∀ i j, label i ≠ label j →
      10*Real.pi*d*largestClumpSize label/
        (enclosingBoxGrid (by omega : 0 < d) N hNpos).minAperture <
          torusLInfDistance (Y i) (Y j))
    (hθupper : nodeSeparation Y ≤ 5*Real.pi*largestClumpSize label/
      (enclosingBoxGrid (by omega : 0 < d) N hNpos).minAperture) :
    let G := normalizedProductGrid (by omega : 0 < d) r a l hseparated
    let H := enclosingBoxGrid (by omega : 0 < d) N hNpos
    consecutiveWindowProductArrayLowerBound G H Y (largestClumpSize label) ≤
      matrixSingularValue (vandermondeMatrix
        (fun k : G.Row => G.rowPoint k + (fun q => (a q 0 : ℝ))) Y) (n-1) := by
  let G := normalizedProductGrid (by omega : 0 < d) r a l hseparated
  let H := enclosingBoxGrid (by omega : 0 < d) N hNpos
  have hlong (q : Fin d) : n ≤ G.coordinateMinLength q := by
    apply Finset.le_inf'
    intro m _
    change n ≤ l q m+1
    have h := hblocks q m
    omega
  have hbound := consecutiveWindowProductArray_minimumSingularValue_lower G H Y label
    (normalizedProductGrid_le_enclosingBoxGrid (by omega) r a l hseparated N hNpos hlast)
    hd hn hsurj hpair hlong hN hcross hθupper
  dsimp only
  rw [generalizedVandermonde_rowShift_minimumSingularValue G Y (by omega)]
  exact hbound

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
