import MultiTuran.MultiClump.LinearNorming
import MultiTuran.MultiClump.FullCube
import MultiTuran.MultiClump.Lifting
import MultiTuran.Turan

/-! # Multi-clump block sampling with the explicit Riemann condition

This is the unconditional public theorem corresponding to `thm:main` in
`notes/multiclump-block-bound-riemann.tex`. The only hypotheses concern the
original segmented grid, a finite partition, clump geometry, and the displayed
sampling threshold. Every analytic input is proved in the import chain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

/-- The factored lower bound for actual torus clumps and the original
measured matrix. Independent real lifts are constructed inside the proof.
The absolute Bernstein constant may be enlarged to at least 24. -/
theorem multiClumpArrayLowerBound_le_minimumSingularValue
    {d n A nStar : ℕ} (G : SegmentedGrid d) (Y : Fin n → Point d)
    (C : NumDetect.ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 2 ≤ d) (hn : 2 ≤ n) (hnStar : 0 < nStar) (hsize : nStar ≤ n)
    (hsurj : Function.Surjective C.label) {τ C_B : ℝ}
    (hτ : 0 < τ) (hτupper : τ ≤ Real.pi/(2*(d : ℝ)))
    (hC_B : 24 ≤ C_B)
    (hsep : 0 < nodeSeparation Y)
    (hsame : ∀ i j, C.label i = C.label j → torusLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j →
      max τ (16*Real.pi*d*(nStar : ℝ)/G.minThickLength) < torusLInfDistance (Y i) (Y j))
    (hN : max (16*n) (32*d^2*nStar) ≤ G.minAperture)
    (hblock : multiClumpBlockConstant d C_B * G.rowCount *
      ((nStar : ℝ)^(4*d+5)/(G.minThickLength : ℝ)^(d+1)+
        (nStar : ℝ)^(4*d+1)*τ/(G.minThickLength : ℝ)^d) ≤ 1) :
    multiClumpArrayLowerBound multidimensionalTuranConstant G Y nStar ≤
      matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  have hn0 : 0 < n := by omega
  have hNn : 16*n ≤ G.minAperture := (le_max_left _ _).trans hN
  have hN4 : 4 ≤ G.minAperture := by omega
  have hτdim : τ ≤ Real.pi/(2*(d : ℝ)) := hτupper
  obtain ⟨p,hp⟩ := exists_simultaneous_clump_lifts hn0 Y C.label hτ.le
    (clump_shortness_of_dimension_bound hd hτdim) hsame
  let Z := liftNodes Y p
  let C' : NumDetect.ClumpSlots (A := A) (nStar := nStar) Z :=
    { label := C.label, slot := C.slot, injective := C.injective }
  have hrealSame : ∀ i j, C'.label i = C'.label j → ∀ q, |Z i q-Z j q| ≤ τ := hp
  have hsameZ : ∀ i j, C'.label i = C'.label j → torusLInfDistance (Z i) (Z j) ≤ τ := by
    intro i j hij
    simpa only [Z,torusLInfDistance_liftNodes] using hsame i j hij
  have hcrossZ : ∀ i j, C'.label i ≠ C'.label j →
      max τ (16*Real.pi*d*(nStar : ℝ)/G.minThickLength) < torusLInfDistance (Z i) (Z j) := by
    intro i j hij
    simpa only [Z,torusLInfDistance_liftNodes] using hcross i j hij
  have hsepZ : 0 < nodeSeparation Z := by
    simpa only [Z,nodeSeparation_liftNodes] using hsep
  have hnorming := continuousNorming_of_linear_multiclump_blocks G Z C' hd hn0 hnStar
    hsurj hC_B hτ.le hrealSame hcrossZ hblock
  let separation : ℝ := 16*Real.pi*d*(nStar : ℝ)/G.minThickLength
  have hL : (0 : ℝ) < G.minThickLength := by exact_mod_cast minThickLength_pos G
  have hseparation : 0 < separation := by dsimp [separation]; positivity
  have hgap : 16*Real.pi*d*(nStar : ℝ) ≤ separation*G.minThickLength := by
    dsimp [separation]
    rw [div_mul_cancel₀ _ (ne_of_gt hL)]
  have hcrossScale : ∀ i j, C'.label i ≠ C'.label j →
      separation < torusLInfDistance (Z i) (Z j) := by
    intro i j hij
    exact (le_max_right τ separation).trans_lt (hcrossZ i j hij)
  let s := fullApertureCubeSide G.minAperture
  have hsprops := fullApertureCubeSide_properties hN4
  have hs8 : 8*n ≤ s := fullApertureCubeSide_large hn0 hNn
  have hsSeparation : 8*Real.pi*d*nStar/(s : ℝ) ≤ separation :=
    fullApertureCubeSide_gap G hnStar hseparation hN4 hgap
  have hcube := multiClumpCubeLowerBound_le G C' hn0 hnStar hsize
    hsameZ hcrossScale hsprops.1 hs8 hsprops.2.2.1 hsSeparation hτdim hsepZ
  have hfinal := multiClumpArrayLowerBound_le_of_norming_cube_and_restriction G Z hn0
    multidimensionalTuranConstant_pos hnorming hsprops.2.1 hcube
    (aperture_supNorm_turan G hn0 Z)
  simpa only [Z,multiClumpArrayLowerBound_liftNodes,generalizedVandermonde_liftNodes] using hfinal

/-- A partition interface: injective clump slots are constructed from the
actual fiber cardinalities, so they are not an additional public hypothesis. -/
theorem multiClumpArray_minimumSingularValue_lower
    {d n A nStar : ℕ} (G : SegmentedGrid d) (Y : Fin n → Point d)
    (label : Fin n → Fin A) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (hnStar : 0 < nStar) (hsize : nStar ≤ n)
    (hsurj : Function.Surjective label)
    (hclumpSize : ∀ a, (Finset.univ.filter fun j => label j = a).card ≤ nStar)
    {τ C_B : ℝ} (hτ : 0 < τ) (hτupper : τ ≤ Real.pi/(2*(d : ℝ)))
    (hC_B : 24 ≤ C_B)
    (hsep : 0 < nodeSeparation Y)
    (hsame : ∀ i j, label i = label j → torusLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, label i ≠ label j →
      max τ (16*Real.pi*d*(nStar : ℝ)/G.minThickLength) < torusLInfDistance (Y i) (Y j))
    (hN : max (16*n) (32*d^2*nStar) ≤ G.minAperture)
    (hblock : multiClumpBlockConstant d C_B * G.rowCount *
      ((nStar : ℝ)^(4*d+5)/(G.minThickLength : ℝ)^(d+1)+
        (nStar : ℝ)^(4*d+1)*τ/(G.minThickLength : ℝ)^d) ≤ 1) :
    Real.sqrt (multiClumpNormingConstant d n nStar multidimensionalTuranConstant /
      ((n : ℝ)*8^nStar)) * (2/(Real.pi*n))^d * G.rhoL *
      (G.fillingRatio/(multidimensionalTuranConstant*d))^(n-1) *
      ((G.minAperture : ℝ)/(6*nStar))^((d : ℝ)/2) *
      min 1 ((G.minAperture : ℝ)*nodeSeparation Y/(8*Real.pi*nStar))^(nStar-1) ≤
        matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  obtain ⟨C,hC⟩ := NumDetect.exists_clumpSlots (x := Y) label hclumpSize
  have hsurjC : Function.Surjective C.label := by rw [hC]; exact hsurj
  have hsameC : ∀ i j, C.label i = C.label j → torusLInfDistance (Y i) (Y j) ≤ τ := by
    simpa only [hC] using hsame
  have hcrossC : ∀ i j, C.label i ≠ C.label j →
      max τ (16*Real.pi*d*(nStar : ℝ)/G.minThickLength) < torusLInfDistance (Y i) (Y j) := by
    simpa only [hC] using hcross
  exact multiClumpArrayLowerBound_le_minimumSingularValue G Y C hd hn hnStar hsize
    hsurjC hτ hτupper hC_B hsep hsameC hcrossC hN hblock

end
end LeanNumDetect.MultiTuran.MultiClump
