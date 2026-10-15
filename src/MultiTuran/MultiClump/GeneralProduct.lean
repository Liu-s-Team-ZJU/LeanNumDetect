import MultiTuran.MultiClump.Norming
import MultiTuran.MultiClump.FullCube
import MultiTuran.MultiClump.Lifting
import MultiTuran.Turan

/-!
# General product sampling inside an independently specified aperture

The measured blocks belong to `G`, while the aperture box and full-cube scale
belong to `H`. No measured row is added and no endpoint is substituted for the
specified enclosing aperture. Together with unitary row-frequency translation,
this is the product-set scope of the standalone Riemann proof note.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Matrix WithLp Set MeasureTheory

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

/-- The measured-set density in the independently specified enclosing box. -/
def enclosingFillingRatio {d : ℕ} (G H : SegmentedGrid d) : ℝ :=
  (G.rowCount : ℝ)/H.boxVolume

/-- The original long-block factor with the enclosing, rather than measured,
aperture volume in the denominator. -/
def enclosingLongBlockFactor {d : ℕ} (G H : SegmentedGrid d) : ℝ :=
  Real.sqrt ((∏ q, (G.coordinateMinLength q : ℝ))/H.boxVolume)

/-- The literal bound, with measured row geometry from `G` and every aperture
factor from the separately specified `H`. -/
def generalProductArrayLowerBound {d n : ℕ} (G H : SegmentedGrid d)
    (Y : Fin n → Point d) (nStar : ℕ) : ℝ :=
  Real.sqrt (multiClumpNormingConstant d n nStar multidimensionalTuranConstant /
    ((n : ℝ)*8^nStar)) * (2/(Real.pi*n))^d * enclosingLongBlockFactor G H *
    (enclosingFillingRatio G H/(multidimensionalTuranConstant*d))^(n-1) *
    ((H.minAperture : ℝ)/(6*nStar))^((d : ℝ)/2) *
    min 1 ((H.minAperture : ℝ)*nodeSeparation Y/(8*Real.pi*nStar))^(nStar-1)

@[simp] theorem enclosingFillingRatio_self {d : ℕ} (G : SegmentedGrid d) :
    enclosingFillingRatio G G = G.fillingRatio := rfl

@[simp] theorem enclosingLongBlockFactor_self {d : ℕ} (G : SegmentedGrid d) :
    enclosingLongBlockFactor G G = G.rhoL := rfl

@[simp] theorem generalProductArrayLowerBound_self {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (nStar : ℕ) :
    generalProductArrayLowerBound G G Y nStar =
      multiClumpArrayLowerBound multidimensionalTuranConstant G Y nStar := rfl

theorem enclosingFillingRatio_pos {d : ℕ} (G H : SegmentedGrid d) :
    0 < enclosingFillingRatio G H :=
  div_pos (by exact_mod_cast G.rowCount_pos) H.boxVolume_pos

theorem enclosingLongBlockFactor_nonneg {d : ℕ} (G H : SegmentedGrid d) :
    0 ≤ enclosingLongBlockFactor G H := Real.sqrt_nonneg _

theorem thickening_subset_enclosingApertureBox {d : ℕ} (G H : SegmentedGrid d)
    (houter : ∀ q, G.aperture q ≤ H.aperture q) : G.thickening ⊆ H.apertureBox := by
  intro t ht q hq
  have h := G.thickening_subset_apertureBox ht q hq
  exact ⟨h.1, h.2.trans (by exact_mod_cast houter q)⟩

theorem minAperture_le_enclosing_minAperture {d : ℕ} (G H : SegmentedGrid d)
    (houter : ∀ q, G.aperture q ≤ H.aperture q) : G.minAperture ≤ H.minAperture := by
  unfold SegmentedGrid.minAperture
  apply Finset.le_inf'
  intro q _
  exact (G.minAperture_le q).trans (houter q)

/-- The original Turán comparison on the specified outer aperture and the
actual inner measured thickening. -/
theorem enclosingAperture_supNorm_turan {d n : ℕ} (G H : SegmentedGrid d)
    (houter : ∀ q, G.aperture q ≤ H.aperture q) (hn : 0 < n)
    (Y : Fin n → Point d) (c : Fin n → ℂ) :
    setSupNorm (exponentialSum Y c) H.apertureBox ≤
      (multidimensionalTuranConstant*d/enclosingFillingRatio G H)^(n-1)*
        setSupNorm (exponentialSum Y c) G.thickening := by
  have hconvex : Convex ℝ H.apertureBox := convex_pi (fun _ _ => convex_Icc _ _)
  have hvol : 0 < volume G.thickening := by
    rw [G.thickening_volume]
    exact_mod_cast G.rowCount_pos
  have h := exponentialSum_convexBody_supNorm_le G.dimension_pos hn
    H.apertureBox_isCompact hconvex G.thickening_measurableSet
    (thickening_subset_enclosingApertureBox G H houter) hvol Y c
  rw [H.apertureBox_volume_toReal, G.thickening_volume_toReal] at h
  have he : multidimensionalTuranConstant*d/enclosingFillingRatio G H =
      multidimensionalTuranConstant*d*H.boxVolume/(G.rowCount : ℝ) := by
    unfold enclosingFillingRatio
    rw [div_div_eq_mul_div]
  rw [he]
  exact h

private theorem enclosingLongBlockFactor_eq_prod_sqrt {d : ℕ} (G H : SegmentedGrid d) :
    enclosingLongBlockFactor G H = (∏ q, Real.sqrt (G.coordinateMinLength q : ℝ))/
      Real.sqrt H.boxVolume := by
  unfold enclosingLongBlockFactor
  rw [Real.sqrt_div (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)),
    Real.sqrt_prod Finset.univ (fun _ _ => Nat.cast_nonneg _)]

private theorem enclosing_scaledRestriction_normalization {d n : ℕ}
    (G H : SegmentedGrid d) (hn : 0 < n) :
    Real.sqrt H.boxVolume*
      (∏ q, Real.pi*(n : ℝ)/(2*Real.sqrt (G.coordinateMinLength q : ℝ)))*
      ((2/(Real.pi*(n : ℝ)))^d*enclosingLongBlockFactor G H) = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hpi : Real.pi*(n : ℝ) ≠ 0 := mul_ne_zero Real.pi_ne_zero hn0
  have hbox : Real.sqrt H.boxVolume ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr H.boxVolume_pos)
  have hprod : (∏ q, Real.sqrt (G.coordinateMinLength q : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q _
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact_mod_cast G.coordinateMinLength_pos q
  have hc : (∏ q, Real.pi*(n : ℝ)/(2*Real.sqrt (G.coordinateMinLength q : ℝ))) =
      (Real.pi*(n : ℝ)/2)^d/(∏ q, Real.sqrt (G.coordinateMinLength q : ℝ)) := by
    calc
      _ = ∏ q, (Real.pi*(n : ℝ)/2)/Real.sqrt (G.coordinateMinLength q : ℝ) := by
        apply Finset.prod_congr rfl
        intro q _
        rw [div_div]
      _ = _ := by
        rw [Finset.prod_div_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hinv : (Real.pi*(n : ℝ)/2)^d*(2/(Real.pi*(n : ℝ)))^d = 1 := by
    rw [← mul_pow]
    have he : (Real.pi*(n : ℝ)/2)*(2/(Real.pi*(n : ℝ))) = 1 := by field_simp
    rw [he, one_pow]
  rw [hc, enclosingLongBlockFactor_eq_prod_sqrt]
  calc
    _ = (Real.pi*(n : ℝ)/2)^d*(2/(Real.pi*(n : ℝ)))^d := by field_simp
    _ = 1 := hinv

private theorem enclosingFillingRatio_pow_mul_inverse {d : ℕ} (G H : SegmentedGrid d)
    (k : ℕ) :
    (multidimensionalTuranConstant*d/enclosingFillingRatio G H)^k*
      (enclosingFillingRatio G H/(multidimensionalTuranConstant*d))^k = 1 := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt G.dimension_pos)
  have hden := mul_ne_zero multidimensionalTuranConstant_pos.ne' hd
  have hratio := (enclosingFillingRatio_pos G H).ne'
  rw [← mul_pow, div_mul_div_cancel₀ hratio, div_self hden, one_pow]

/-- Full-aperture transport in `H`, norming on the measured grid `G`, and the
original restriction chain between these two different sets. -/
theorem singularValue_lower_of_enclosing_norming_and_cube {d n s : ℕ}
    (G H : SegmentedGrid d) (Y : Fin n → Point d)
    (houter : ∀ q, G.aperture q ≤ H.aperture q) (hn : 0 < n)
    {η b : ℝ} (hη : 0 ≤ η) (hb : 0 ≤ b)
    (hnorming : ContinuousNorming G Y η) (hfull : s+1 ≤ H.minAperture)
    (hcube : b ≤ matrixSingularValue (fullCubeVandermonde 1 s Y) (n-1)) :
    Real.sqrt η*(2/(Real.pi*n))^d*enclosingLongBlockFactor G H*
      (enclosingFillingRatio G H/(multidimensionalTuranConstant*d))^(n-1)*b ≤
        matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  let A := (2/(Real.pi*n))^d*enclosingLongBlockFactor G H*
    (enclosingFillingRatio G H/(multidimensionalTuranConstant*d))^(n-1)
  let τ := (multidimensionalTuranConstant*d/enclosingFillingRatio G H)^(n-1)
  let T := Real.sqrt H.boxVolume*τ*
    (∏ q, Real.pi*n/(2*Real.sqrt (G.coordinateMinLength q : ℝ)))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (by positivity) (enclosingLongBlockFactor_nonneg G H))
      (pow_nonneg (div_nonneg (enclosingFillingRatio_pos G H).le
        (mul_nonneg multidimensionalTuranConstant_pos.le (Nat.cast_nonneg d))) _)
  have hτ : 0 ≤ τ := by
    dsimp [τ]
    exact pow_nonneg (div_nonneg
      (mul_nonneg multidimensionalTuranConstant_pos.le (Nat.cast_nonneg d))
      (enclosingFillingRatio_pos G H).le) _
  have hTA : T*A = 1 := by
    calc
      _ = (Real.sqrt H.boxVolume*
        (∏ q, Real.pi*n/(2*Real.sqrt (G.coordinateMinLength q : ℝ)))*
        ((2/(Real.pi*n))^d*enclosingLongBlockFactor G H))*
        ((multidimensionalTuranConstant*d/enclosingFillingRatio G H)^(n-1)*
          (enclosingFillingRatio G H/(multidimensionalTuranConstant*d))^(n-1)) := by
            dsimp [T,A,τ]
            ring
      _ = 1 := by
        rw [enclosing_scaledRestriction_normalization G H hn,
          enclosingFillingRatio_pow_mul_inverse]
        norm_num
  have hcontinuous : ∀ c : Fin n → ℂ,
      (A*b)*Real.sqrt (∑ j, ‖c j‖^2) ≤ continuousL2Norm G Y c := by
    intro c
    have hap := fullAperture_L2_lower_full_residue H Y c hn
      (by norm_num : 0 < (1 : ℕ)) (by simpa only [Nat.mul_one] using hfull)
    simp only [Nat.cast_one, Real.one_rpow, one_mul] at hap
    have hlower : b*Real.sqrt (∑ j, ‖c j‖^2) ≤
        Real.sqrt (setEnergy Y c H.apertureBox) :=
      (mul_le_mul_of_nonneg_right hcube (Real.sqrt_nonneg _)).trans hap
    have hsup := enclosingAperture_supNorm_turan G H houter hn Y c
    have hupper : Real.sqrt (setEnergy Y c H.apertureBox) ≤ T*continuousL2Norm G Y c := by
      calc
        _ ≤ Real.sqrt H.boxVolume*setSupNorm (exponentialSum Y c) H.apertureBox :=
          apertureL2_le_sqrt_boxVolume_mul_supNorm H Y c
        _ ≤ Real.sqrt H.boxVolume*(τ*setSupNorm (exponentialSum Y c) G.thickening) :=
          mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt H.boxVolume*(τ*
          ((∏ q, Real.pi*n/(2*Real.sqrt (G.coordinateMinLength q : ℝ)))*
            continuousL2Norm G Y c)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (exponentialSum_product_supNorm_le G hn Y c) hτ)
            (Real.sqrt_nonneg _)
        _ = _ := by dsimp [T]; ring
    calc
      _ = A*(b*Real.sqrt (∑ j, ‖c j‖^2)) := by ring
      _ ≤ A*(T*continuousL2Norm G Y c) :=
        mul_le_mul_of_nonneg_left (hlower.trans hupper) hA
      _ = (T*A)*continuousL2Norm G Y c := by ring
      _ = _ := by rw [hTA,one_mul]
  have h := minimumSingularValue_ge_of_continuousNorming G Y hn hη
    (mul_nonneg hA hb) hnorming
    (continuousEnergy_lower_of_L2_lower G Y (mul_nonneg hA hb) hcontinuous)
  convert h using 1
  dsimp [A]
  ring


theorem generalProductArrayLowerBound_le_of_norming_cube
    {d n s nStar : ℕ} (G H : SegmentedGrid d) (Y : Fin n → Point d)
    (houter : ∀ q, G.aperture q ≤ H.aperture q) (hn : 0 < n)
    (hnorming : ContinuousNorming G Y
      (multiClumpNormingConstant d n nStar multidimensionalTuranConstant))
    (hfull : s+1 ≤ H.minAperture)
    (hcube : multiClumpCubeLowerBound H n nStar (nodeSeparation Y) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n-1)) :
    generalProductArrayLowerBound G H Y nStar ≤
      matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  have hη := multiClumpNormingConstant_nonneg d n nStar multidimensionalTuranConstant
    multidimensionalTuranConstant_pos.le
  have h := singularValue_lower_of_enclosing_norming_and_cube G H Y houter hn hη
    (multiClumpCubeLowerBound_nonneg H n nStar (nodeSeparation_nonneg Y))
    hnorming hfull hcube
  have hsqrt : Real.sqrt (multiClumpNormingConstant d n nStar multidimensionalTuranConstant /
      ((n : ℝ)*8^nStar)) =
      Real.sqrt (multiClumpNormingConstant d n nStar multidimensionalTuranConstant) /
        Real.sqrt ((n : ℝ)*8^nStar) := Real.sqrt_div hη _
  unfold generalProductArrayLowerBound
  rw [hsqrt]
  convert h using 1
  unfold multiClumpCubeLowerBound
  ring

/-- The gap measured against the true inner block length is sufficient for
the cube at the independently specified, possibly larger aperture. -/
theorem fullApertureCubeSide_enclosing_gap {d nStar : ℕ} (G H : SegmentedGrid d)
    (houter : ∀ q, G.aperture q ≤ H.aperture q)
    (hnStar : 0 < nStar) {separation : ℝ} (hseparation : 0 < separation) (hN : 4 ≤ H.minAperture)
    (hgap : 16*Real.pi*d*(nStar : ℝ)^2 ≤ separation*G.minThickLength) :
    8*Real.pi*d*nStar/(fullApertureCubeSide H.minAperture : ℝ) ≤ separation := by
  have hL : (G.minThickLength : ℝ) ≤ H.minAperture := by
    exact_mod_cast (minThickLength_le_minAperture G).trans
      (minAperture_le_enclosing_minAperture G H houter)
  have hNs := (fullApertureCubeSide_properties hN).2.2.1
  have hNsR : (H.minAperture : ℝ) ≤ 2*(fullApertureCubeSide H.minAperture : ℝ) := by
    exact_mod_cast hNs
  have hs : (0 : ℝ) < fullApertureCubeSide H.minAperture := by
    exact_mod_cast (show 0 < fullApertureCubeSide H.minAperture by omega)
  have hns : (1 : ℝ) ≤ nStar := by exact_mod_cast hnStar
  have hpow : (nStar : ℝ) ≤ (nStar : ℝ)^2 := le_self_pow₀ hns (by norm_num)
  have h₁ := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ 16*Real.pi*d by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hL hseparation.le
  have h₃ := mul_le_mul_of_nonneg_left hNsR hseparation.le
  apply (div_le_iff₀ hs).mpr
  nlinarith only [h₁,hgap,h₂,h₃]

@[simp] theorem generalProductArrayLowerBound_liftNodes {d n : ℕ}
    (G H : SegmentedGrid d) (Y : Fin n → Point d)
    (p : Fin n → Fin d → ℤ) (nStar : ℕ) :
    generalProductArrayLowerBound G H (liftNodes Y p) nStar =
      generalProductArrayLowerBound G H Y nStar := by
  simp only [generalProductArrayLowerBound, nodeSeparation_liftNodes]

/-- The full Riemann multi-clump theorem on the actual measured blocks with
an arbitrary independent enclosing aperture. All hypotheses are geometric
or the literal block sampling threshold. -/
theorem generalProductArrayLowerBound_le_minimumSingularValue
    {d n A nStar : ℕ} (G H : SegmentedGrid d) (Y : Fin n → Point d)
    (C : NumDetect.ClumpSlots (A := A) (nStar := nStar) Y)
    (houter : ∀ q, G.aperture q ≤ H.aperture q)
    (hd : 2 ≤ d) (hn : 2 ≤ n) (hnStar : 0 < nStar) (hsize : nStar ≤ n)
    (hsurj : Function.Surjective C.label) {τ C_B : ℝ}
    (hτ : 0 < τ) (hτupper : τ ≤ Real.pi/(2*(d : ℝ)))
    (hC_B : 24 ≤ C_B)
    (hsep : 0 < nodeSeparation Y)
    (hsame : ∀ i j, C.label i = C.label j → torusLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j →
      max τ (16*Real.pi*d*(nStar : ℝ)^2/G.minThickLength) < torusLInfDistance (Y i) (Y j))
    (hN : max (16*n) (32*d^2*nStar) ≤ H.minAperture)
    (hblock : multiClumpBlockConstant d C_B * G.rowCount *
      ((nStar : ℝ)^(4*d+5)/(G.minThickLength : ℝ)^(d+1)+
        (nStar : ℝ)^(4*d+1)*τ/(G.minThickLength : ℝ)^d) ≤ 1) :
    generalProductArrayLowerBound G H Y nStar ≤
      matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  have hn0 : 0 < n := by omega
  have hNn : 16*n ≤ H.minAperture := (le_max_left _ _).trans hN
  have hN4 : 4 ≤ H.minAperture := by omega
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
      max τ (16*Real.pi*d*(nStar : ℝ)^2/G.minThickLength) < torusLInfDistance (Z i) (Z j) := by
    intro i j hij
    simpa only [Z,torusLInfDistance_liftNodes] using hcross i j hij
  have hsepZ : 0 < nodeSeparation Z := by
    simpa only [Z,nodeSeparation_liftNodes] using hsep
  have hnorming := continuousNorming_of_multiclump_blocks G Z C' hd hn0 hnStar
    hsurj hC_B hτ.le hrealSame hcrossZ hblock
  let separation : ℝ := 16*Real.pi*d*(nStar : ℝ)^2/G.minThickLength
  have hL : (0 : ℝ) < G.minThickLength := by exact_mod_cast minThickLength_pos G
  have hseparation : 0 < separation := by dsimp [separation]; positivity
  have hgap : 16*Real.pi*d*(nStar : ℝ)^2 ≤ separation*G.minThickLength := by
    dsimp [separation]
    rw [div_mul_cancel₀ _ (ne_of_gt hL)]
  have hcrossScale : ∀ i j, C'.label i ≠ C'.label j →
      separation < torusLInfDistance (Z i) (Z j) := by
    intro i j hij
    exact (le_max_right τ separation).trans_lt (hcrossZ i j hij)
  let s := fullApertureCubeSide H.minAperture
  have hsprops := fullApertureCubeSide_properties hN4
  have hs8 : 8*n ≤ s := fullApertureCubeSide_large hn0 hNn
  have hsSeparation : 8*Real.pi*d*nStar/(s : ℝ) ≤ separation :=
    fullApertureCubeSide_enclosing_gap G H houter hnStar hseparation hN4 hgap
  have hcube := multiClumpCubeLowerBound_le H C' hn0 hnStar hsize
    hsameZ hcrossScale hsprops.1 hs8 hsprops.2.2.1 hsSeparation hτdim hsepZ
  have hfinal := generalProductArrayLowerBound_le_of_norming_cube G H Z houter hn0
    hnorming hsprops.2.1 hcube
  simpa only [Z,generalProductArrayLowerBound_liftNodes,generalizedVandermonde_liftNodes] using hfinal

/-- The complete displayed formula for a finite clump partition, with no
auxiliary interpolation, norming, or spectral hypotheses. -/
theorem generalProductArray_minimumSingularValue_lower
    {d n A nStar : ℕ} (G H : SegmentedGrid d) (Y : Fin n → Point d)
    (label : Fin n → Fin A) (houter : ∀ q, G.aperture q ≤ H.aperture q)
    (hd : 2 ≤ d) (hn : 2 ≤ n) (hnStar : 0 < nStar) (hsize : nStar ≤ n)
    (hsurj : Function.Surjective label)
    (hclumpSize : ∀ a, (Finset.univ.filter fun j => label j = a).card ≤ nStar)
    {τ C_B : ℝ} (hτ : 0 < τ) (hτupper : τ ≤ Real.pi/(2*(d : ℝ)))
    (hC_B : 24 ≤ C_B)
    (hsep : 0 < nodeSeparation Y)
    (hsame : ∀ i j, label i = label j → torusLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, label i ≠ label j →
      max τ (16*Real.pi*d*(nStar : ℝ)^2/G.minThickLength) < torusLInfDistance (Y i) (Y j))
    (hN : max (16*n) (32*d^2*nStar) ≤ H.minAperture)
    (hblock : multiClumpBlockConstant d C_B * G.rowCount *
      ((nStar : ℝ)^(4*d+5)/(G.minThickLength : ℝ)^(d+1)+
        (nStar : ℝ)^(4*d+1)*τ/(G.minThickLength : ℝ)^d) ≤ 1) :
    Real.sqrt (multiClumpNormingConstant d n nStar multidimensionalTuranConstant /
      ((n : ℝ)*8^nStar)) * (2/(Real.pi*n))^d *
      Real.sqrt ((∏ q, (G.coordinateMinLength q : ℝ))/H.boxVolume) *
      (((G.rowCount : ℝ)/H.boxVolume)/(multidimensionalTuranConstant*d))^(n-1) *
      ((H.minAperture : ℝ)/(6*nStar))^((d : ℝ)/2) *
      min 1 ((H.minAperture : ℝ)*nodeSeparation Y/(8*Real.pi*nStar))^(nStar-1) ≤
        matrixSingularValue (generalizedVandermonde G Y) (n-1) := by
  obtain ⟨C,hC⟩ := NumDetect.exists_clumpSlots (x := Y) label hclumpSize
  have hsurjC : Function.Surjective C.label := by rw [hC]; exact hsurj
  have hsameC : ∀ i j, C.label i = C.label j → torusLInfDistance (Y i) (Y j) ≤ τ := by
    simpa only [hC] using hsame
  have hcrossC : ∀ i j, C.label i ≠ C.label j →
      max τ (16*Real.pi*d*(nStar : ℝ)^2/G.minThickLength) < torusLInfDistance (Y i) (Y j) := by
    simpa only [hC] using hcross
  exact generalProductArrayLowerBound_le_minimumSingularValue G H Y C houter hd hn hnStar hsize
    hsurjC hτ hτupper hC_B hsep hsameC hcrossC hN hblock

end
end LeanNumDetect.MultiTuran.MultiClump
