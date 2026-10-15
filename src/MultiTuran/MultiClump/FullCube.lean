import NumDetect.Random.CubeClumpBounds
import MultiTuran.FullCube
import MultiTuran.MultiClump.ClumpGeometry
import MultiTuran.MultiClump.BoundFormula

/-!
# Multi-clump full-cube lower bounds

These statements derive the clipped full-aperture input of the multi-clump
Riemann note from the proved cardinal-polynomial constructions.  The positive
spacing parameter is any lower bound for the pair distances; it need not equal
the actual minimum separation.  Clump diameter and inter-clump gap remain
separate parameters.  No external admission is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Matrix WithLp
open scoped BigOperators
open LeanNumDetect.NumDetect

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

theorem clumpCardinalPolynomial
    {d n A nStar M : ℕ} {τ η β Δ : ℝ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x) (anchor : Fin n)
    (hd : 1 ≤ d) (hs : 1 ≤ nStar) (hM : 2 * nStar ≤ M)
    (hΔ : 0 < Δ) (hβ : 1 / (2 * Real.log 2) < β)
    (hcube : ∀ j, InAngularCube (x j))
    (hsame : ∀ i j, C.label i = C.label j → periodicLInfDistance (x i) (x j) ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j → η < periodicLInfDistance (x i) (x j))
    (hτ : τ ≤ Real.pi / (2 * d))
    (hη : 4 * Real.pi * β * d / ((M / nStar : ℕ) + 1) ≤ η)
    (hmin : ∀ i j, i ≠ j → Δ ≤ periodicL1Distance (x i) (x j))
    (hscale : Δ ≤ 2 * Real.pi * nStar / M) :
    ∃ P : SegmentedPolynomial d (M + (M - M / nStar)) 0 (2 * M + 1),
      (∀ j, P.angularValue (x j) = if anchor = j then 1 else 0) ∧
      P.mass ≤ (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar *
        (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1) := by
  classical
  have ha := liFrameConstant_pos hβ
  have hK : nStar * (M / nStar) ≤ M := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self M nStar
  have hKD : M / nStar < 2 * M + 1 := by
    have hdiv := Nat.div_le_self M nStar
    omega
  have hprodD : nStar * (M / nStar) < 2 * M + 1 := by omega
  have hframe := BartonCubeFrame.hasFineCubeFrame_of_translatedCube hd hβ hη
  have hframes (color : Fin nStar) (v : ↥(clumpColorClass C anchor color) → ℂ) :
      (2 - Real.exp (1 / (2 * β))) * (((M / nStar + 1) ^ d : ℕ) : ℝ) *
        SegmentedVDM.energy v ≤ SegmentedVDM.energy
          (fineCubeEvaluation (M / nStar) (fun j : ↥(clumpColorClass C anchor color) => x j) *ᵥ v) := by
    apply @hframe (↥(clumpColorClass C anchor color)) inferInstance inferInstance
      (fun j => x j) (fun j => hcube j) _ v
    intro i j hij
    exact hcross i j (clumpColorClass_labels_ne C anchor color i j hij)
  obtain ⟨G₀, hG1, hG0, hGmass⟩ :=
    localizationPolynomial_of_colorFrames C anchor hKD hprodD ha hframes
  let G : SegmentedPolynomial d M 0 (2 * M + 1) := G₀.widen hK le_rfl (by omega)
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlocal : Δ / 2 ≤ Real.pi * nStar / ((M : ℝ) * 1) := by
    have h := (le_div_iff₀ hMR).mp hscale
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) * 1)).mpr
    nlinarith
  obtain ⟨B₀, hBvalue, hBmass⟩ := withinClumpPolynomial C anchor hd hs hM
    (D := 1) (by omega) (by positivity : 0 < Δ / 2) hcube hsame
    (by simpa using hτ) (fun i j hij => (by linarith [hmin i j hij])) (by simpa only [Nat.cast_one] using hlocal)
  have hR : M - M / nStar ≤ M := Nat.sub_le _ _
  let B : SegmentedPolynomial d (M - M / nStar) 0 (2 * M + 1) :=
    B₀.coarseToFine (by omega)
  have hsum : M + (M - M / nStar) < 2 * M + 1 := by omega
  let P := G.mul B hsum
  refine ⟨P, ?_, ?_⟩
  · intro j
    simp only [P, SegmentedPolynomial.angularValue_mul, B,
      SegmentedPolynomial.angularValue_coarseToFine, G, SegmentedPolynomial.angularValue_widen]
    by_cases hj : C.label j = C.label anchor
    · rw [hBvalue j hj]
      by_cases haj : anchor = j
      · subst j
        simp [hG1]
      · simp [haj]
    · rw [hG0 j hj, zero_mul]
      have haj : anchor ≠ j := fun h => hj (congrArg C.label h.symm)
      simp [haj]
  · have hBmass' : B.mass ≤
        (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1) := by
      simpa [B] using hBmass
    have hGmass' : G.mass ≤ (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar := by
      simpa [G] using hGmass
    exact (SegmentedPolynomial.mass_mul_le G B hsum).trans
      (mul_le_mul hGmass' hBmass' B.mass_nonneg (by positivity))


/-- The one-block segmented matrix is exactly the original full cube after
reindexing its rows. -/
theorem segmentedVandermonde_oneBlock_singularValue {d n L : ℕ}
    (Y : Fin n → Point d) (i : ℕ) :
    matrixSingularValue (segmentedVandermonde L 0 (L + 1) Y) i =
      matrixSingularValue (fullCubeVandermonde 1 L Y) i := by
  have hmat : (segmentedVandermonde L 0 (L + 1) Y).submatrix
      (SegmentedPolynomial.fineCubeIndexEquiv d L).symm (Equiv.refl (Fin n)) =
      fullCubeVandermonde 1 L Y := by
    ext k j
    simp [segmentedVandermonde, NumDetect.generalizedVandermonde, steeringVector,
      segmentedFrequency, SegmentedPolynomial.fineCubeIndexEquiv,
      fullCubeVandermonde, exponential, dot]
  rw [← hmat, matrixSingularValue_submatrix_equiv]

/-- Raw cube lower bound at half bandwidth.  Unlike the public pre-existing
clump corollary, `Δ` is arbitrary below all pair distances, which permits the
clipped separation used by the multi-clump note. -/
theorem fullCube_clump_raw_lower_halfBandwidth
    {d n A nStar M : ℕ} {τ separation β Δ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 1 ≤ d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hcube : ∀ j, InAngularCube (Y j))
    (hsame : ∀ i j, C.label i = C.label j → periodicLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < periodicLInfDistance (Y i) (Y j))
    (hM : 4 * n ≤ M) (hβ : 1 / (2 * Real.log 2) < β)
    (hseparation : 4 * Real.pi * β * d * nStar / M ≤ separation)
    (hτ : τ ≤ Real.pi / (2 * d)) (hΔ : 0 < Δ)
    (hmin : ∀ i j, i ≠ j → Δ ≤ periodicL1Distance (Y i) (Y j))
    (hscale : Δ ≤ 2 * Real.pi * nStar / M) :
    let H := (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar *
        (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1)
    Real.sqrt (((M / nStar + 1) ^ d : ℕ) : ℝ) / (Real.sqrt n * H) ≤
      matrixSingularValue (fullCubeVandermonde 1 (2 * M) Y) (n - 1) := by
  classical
  dsimp only
  have hM0 : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  have hβ0 : 0 < β := (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
  have hK : (M : ℝ) ≤ nStar * (((M / nStar : ℕ) : ℝ) + 1) := by
    exact_mod_cast (Nat.lt_mul_div_succ M hs).le
  have hseparation' : 4 * Real.pi * β * d / ((M / nStar : ℕ) + 1) ≤ separation := by
    apply le_trans _ hseparation
    apply (div_le_div_iff₀ (by positivity) hMR).mpr
    convert mul_le_mul_of_nonneg_left hK
      (show 0 ≤ 4 * Real.pi * β * d by positivity) using 1 <;> ring
  choose P hPv hPm using fun anchor => clumpCardinalPolynomial C anchor hd
    (by omega : 1 ≤ nStar) (by omega : 2 * nStar ≤ M) hΔ hβ
    hcube hsame hcross hτ hseparation' hmin hscale
  let H := (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar *
        (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1)
  have ha := liFrameConstant_pos hβ
  have hH : 0 < H := by dsimp [H]; positivity
  have hsum : M + (M - M / nStar) + M / nStar < 2 * M + 1 := by
    have := Nat.div_le_self M nStar
    omega
  have hh := SegmentedPolynomial.singularValue_ge_of_smoothedSegmentedPolynomials
    hn Y P hPv hsum hH hPm (b := M / nStar) (z := 0)
  have hbudget : M + (M - M / nStar) + M / nStar = 2 * M := by
    have := Nat.div_le_self M nStar
    omega
  rw [hbudget, segmentedVandermonde_oneBlock_singularValue] at hh
  simpa only [H, Nat.add_zero, zero_add, zero_mul, one_mul] using hh


/-- Exact explicit cube coefficient with an arbitrary admissible positive
spacing lower bound and separate diameter and inter-clump gap. -/
theorem fullCube_clump_singularValue_lower_halfBandwidth
    {d n A nStar M : ℕ} {τ separation β Δ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 1 ≤ d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hcube : ∀ j, InAngularCube (Y j))
    (hsame : ∀ i j, C.label i = C.label j → periodicLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < periodicLInfDistance (Y i) (Y j))
    (hM : 4 * n ≤ M) (hβ : 1 / (2 * Real.log 2) < β)
    (hseparation : 4 * Real.pi * β * d * nStar / M ≤ separation)
    (hτ : τ ≤ Real.pi / (2 * d)) (hΔ : 0 < Δ)
    (hmin : ∀ i j, i ≠ j → Δ ≤ periodicL1Distance (Y i) (Y j))
    (hscale : Δ ≤ 2 * Real.pi * nStar / M) :
    (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
      Real.sqrt (((2 * ((2 * M) / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) /
      (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1)) *
      (((2 * M : ℕ) : ℝ) * Δ / (4 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 (2 * M) Y) (n - 1) := by
  let H := (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar *
    (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1)
  have hraw := fullCube_clump_raw_lower_halfBandwidth C hd hn hs hsize
    hcube hsame hcross hM hβ hseparation hτ hΔ hmin hscale
  have ha := liFrameConstant_pos hβ
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hH : 0 < H := by dsimp [H]; positivity
  have hpacket : 2 * ((2 * M) / (4 * nStar)) + 1 ≤ M / nStar + 1 := by
    have hdiv := Nat.div_mul_le_self (2 * M) (4 * nStar)
    have hmul : (2 * ((2 * M) / (4 * nStar))) * nStar ≤ M := by nlinarith
    have h := (Nat.le_div_iff_mul_le hs).mpr hmul
    omega
  have hpacketRoot :
      Real.sqrt (((2 * ((2 * M) / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) ≤
      Real.sqrt (((M / nStar + 1) ^ d : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.pow_le_pow_left hpacket d
  have hrootpow : (Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar =
      (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ha.le]
    congr 1
    ring
  have ht : (((M : ℝ) / nStar) * (Δ / 2) / Real.pi) =
      ((2 * M : ℕ) : ℝ) * Δ / (4 * Real.pi * nStar) := by
    push_cast
    ring
  calc
    _ = Real.sqrt (((2 * ((2 * M) / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) /
        (Real.sqrt n * H) := by
      rw [← hrootpow]
      dsimp [H]
      rw [ht]
      simp only [div_pow, one_pow]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr ha), ne_of_gt (Real.sqrt_pos.mpr
        (show (0 : ℝ) < n by exact_mod_cast hn)), Real.pi_ne_zero,
        ne_of_gt (show (0 : ℝ) < nStar by exact_mod_cast hs),
        ne_of_gt (show (0 : ℝ) < M by exact_mod_cast (show 0 < M by omega)), hΔ.ne']
      <;> ring
    _ ≤ Real.sqrt (((M / nStar + 1) ^ d : ℕ) : ℝ) / (Real.sqrt n * H) :=
      div_le_div_of_nonneg_right hpacketRoot (by positivity)
    _ ≤ _ := hraw

/-- Even-bandwidth form matching the manuscript's original `A_{1,s}`. -/
theorem fullCube_clump_singularValue_lower
    {d n A nStar s : ℕ} {τ separation β Δ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 1 ≤ d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hcube : ∀ j, InAngularCube (Y j))
    (hsame : ∀ i j, C.label i = C.label j → periodicLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < periodicLInfDistance (Y i) (Y j))
    (heven : Even s) (hsn : 8 * n ≤ s) (hβ : 1 / (2 * Real.log 2) < β)
    (hseparation : 8 * Real.pi * β * d * nStar / s ≤ separation)
    (hτ : τ ≤ Real.pi / (2 * d)) (hΔ : 0 < Δ)
    (hmin : ∀ i j, i ≠ j → Δ ≤ periodicL1Distance (Y i) (Y j))
    (hscale : Δ ≤ 4 * Real.pi * nStar / s) :
    (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
      Real.sqrt (((2 * (s / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) /
      (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1)) *
      ((s : ℝ) * Δ / (4 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
  obtain ⟨M, hM⟩ := heven
  have hsM : s = 2 * M := by omega
  clear hM
  subst s
  apply fullCube_clump_singularValue_lower_halfBandwidth C hd hn hs hsize hcube
    hsame hcross (by omega : 4 * n ≤ M) hβ
  · convert hseparation using 1 <;> push_cast <;> ring
  · exact hτ
  · exact hΔ
  · exact hmin
  · convert hscale using 1 <;> push_cast <;> ring


@[simp] theorem fullCubeVandermonde_principalAngularPoint {d n : ℕ}
    (M s : ℕ) (Y : Fin n → Point d) :
    fullCubeVandermonde M s (fun j => principalAngularPoint (Y j)) =
      fullCubeVandermonde M s Y := by
  funext k j
  have h := integerFourierPhase_principalAngularPoint
    (fun q => ((M * (k q).val : ℕ) : ℤ)) (Y j)
  simpa only [fullCubeVandermonde, exponential, Nat.cast_one, one_mul,
    Int.cast_natCast, Int.cast_mul, Nat.cast_mul, mul_assoc, mul_left_comm] using h

/-- The explicit full-cube estimate for arbitrary real representatives.
The principal chart used by the interpolation construction is removed by an
exact integer-frequency normalization; continuous clump lifts can therefore
be chosen independently later in the Riemann argument. -/
theorem fullCube_clump_singularValue_lower_of_torus
    {d n A nStar s : ℕ} {τ separation β Δ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 1 ≤ d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hsame : ∀ i j, C.label i = C.label j → torusLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < torusLInfDistance (Y i) (Y j))
    (heven : Even s) (hsn : 8 * n ≤ s) (hβ : 1 / (2 * Real.log 2) < β)
    (hseparation : 8 * Real.pi * β * d * nStar / s ≤ separation)
    (hτ : τ ≤ Real.pi / (2 * d)) (hΔ : 0 < Δ)
    (hmin : ∀ i j, i ≠ j → Δ ≤ torusLInfDistance (Y i) (Y j))
    (hscale : Δ ≤ 4 * Real.pi * nStar / s) :
    (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
      Real.sqrt (((2 * (s / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) /
      (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1)) *
      ((s : ℝ) * Δ / (4 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
  let C' : ClumpSlots (A := A) (nStar := nStar)
      (fun j => principalAngularPoint (Y j)) :=
    { label := C.label, slot := C.slot, injective := C.injective }
  have hcube (j : Fin n) := principalAngularPoint_mem (Y j)
  have hsame' (i j : Fin n) (hij : C'.label i = C'.label j) :
      periodicLInfDistance (principalAngularPoint (Y i)) (principalAngularPoint (Y j)) ≤ τ := by
    rw [← torusLInfDistance_eq_periodicLInfDistance (hcube i) (hcube j),
      torusLInfDistance_principalAngularPoint]
    exact hsame i j hij
  have hcross' (i j : Fin n) (hij : C'.label i ≠ C'.label j) :
      separation < periodicLInfDistance (principalAngularPoint (Y i)) (principalAngularPoint (Y j)) := by
    rw [← torusLInfDistance_eq_periodicLInfDistance (hcube i) (hcube j),
      torusLInfDistance_principalAngularPoint]
    exact hcross i j hij
  have hmin' (i j : Fin n) (hij : i ≠ j) :
      Δ ≤ periodicL1Distance (principalAngularPoint (Y i)) (principalAngularPoint (Y j)) := by
    have h := (hmin i j hij).trans (by
      simpa only [torusLInfDistance_principalAngularPoint] using
        torusLInfDistance_le_periodicL1Distance (hcube i) (hcube j))
    exact h
  have h := fullCube_clump_singularValue_lower C' hd hn hs hsize hcube
    hsame' hcross' heven hsn hβ hseparation hτ hΔ hmin' hscale
  simpa only [fullCubeVandermonde_principalAngularPoint] using h

/-- Clipped separation bound, with no condition that the actual minimum
separation lie in the super-resolution regime.  Every assumption concerns
only clump geometry, full aperture, or the supplied pair-distance lower bound. -/
theorem fullCube_clump_clipped_lower_of_torus
    {d n A nStar s : ℕ} {τ separation β θ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 1 ≤ d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hsame : ∀ i j, C.label i = C.label j → torusLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < torusLInfDistance (Y i) (Y j))
    (heven : Even s) (hsn : 8 * n ≤ s) (hβ : 1 / (2 * Real.log 2) < β)
    (hseparation : 8 * Real.pi * β * d * nStar / s ≤ separation)
    (hτ : τ ≤ Real.pi / (2 * d)) (hθ : 0 < θ)
    (hmin : ∀ i j, i ≠ j → θ ≤ torusLInfDistance (Y i) (Y j)) :
    (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
      Real.sqrt (((2 * (s / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) /
      (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1)) *
      (min 1 ((s : ℝ) * θ / (4 * Real.pi * nStar))) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hc0 : (0 : ℝ) < 4 * Real.pi * nStar := by positivity
  let Δ := min θ (4 * Real.pi * nStar / s)
  have hΔ : 0 < Δ := lt_min hθ (by positivity)
  have hΔmin (i j : Fin n) (hij : i ≠ j) :
      Δ ≤ torusLInfDistance (Y i) (Y j) := (min_le_left _ _).trans (hmin i j hij)
  have hscale : Δ ≤ 4 * Real.pi * nStar / s := min_le_right _ _
  have hfactor : (s : ℝ) * Δ / (4 * Real.pi * nStar) =
      min 1 ((s : ℝ) * θ / (4 * Real.pi * nStar)) := by
    by_cases h : θ ≤ 4 * Real.pi * nStar / s
    · have hprod : (s : ℝ) * θ / (4 * Real.pi * nStar) ≤ 1 := by
        apply (div_le_iff₀ hc0).2
        have hh := (le_div_iff₀ hs0).1 h
        nlinarith
      dsimp only [Δ]
      rw [min_eq_left h, min_eq_right hprod]
    · have h' : 4 * Real.pi * nStar / s ≤ θ := le_of_lt (lt_of_not_ge h)
      have hprod : 1 ≤ (s : ℝ) * θ / (4 * Real.pi * nStar) := by
        apply (le_div_iff₀ hc0).2
        have hh := (div_le_iff₀ hs0).1 h'
        nlinarith
      dsimp only [Δ]
      rw [min_eq_right h', min_eq_left hprod]
      field_simp
  have h := fullCube_clump_singularValue_lower_of_torus C hd hn hs hsize
    hsame hcross heven hsn hβ hseparation hτ hΔ hΔmin hscale
  rw [hfactor] at h
  exact h


/-- The bandwidth-independent coefficient of the existing cube theorem,
now for any spacing lower bound and arbitrary real representatives. -/
theorem fullCube_clump_uniform_lower_of_torus
    {d n A nStar s : ℕ} {τ separation β Δ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 1 ≤ d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hsame : ∀ i j, C.label i = C.label j → torusLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < torusLInfDistance (Y i) (Y j))
    (heven : Even s) (hsn : 8 * n ≤ s) (hβ : 1 / (2 * Real.log 2) < β)
    (hseparation : 8 * Real.pi * β * d * nStar / s ≤ separation)
    (hτ : τ ≤ Real.pi / (2 * d)) (hΔ : 0 < Δ)
    (hmin : ∀ i j, i ≠ j → Δ ≤ torusLInfDistance (Y i) (Y j))
    (hscale : Δ ≤ 4 * Real.pi * nStar / s) :
    liCubeClumpUniformCoefficient d n nStar β * ((s : ℝ) * Δ) ^ (nStar - 1) *
      Real.sqrt (((s + 1) ^ d : ℕ) : ℝ) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
  have h := fullCube_clump_singularValue_lower_of_torus C hd hn hs hsize
    hsame hcross heven hsn hβ hseparation hτ hΔ hmin hscale
  have hrows : 0 < Real.sqrt (((s + 1) ^ d : ℕ) : ℝ) := by positivity
  have hexact : liCubeClumpLower d n nStar s β Δ *
      Real.sqrt (((s + 1) ^ d : ℕ) : ℝ) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
    convert h using 1
    unfold liCubeClumpLower
    field_simp [ne_of_gt hrows]
  have hsstar : 8 * nStar ≤ s := by omega
  exact (mul_le_mul_of_nonneg_right
    (liCubeClumpUniformLower_le_exact hn hs hsstar hβ hΔ.le) hrows.le).trans hexact


/-- The parameter `β=1` lies in the range of the proved cube frame. -/
theorem betaOne_admissible : 1 / (2 * Real.log 2) < (1 : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_lt_one (by positivity : 0 < 2 * Real.log 2)).2
  nlinarith [Real.log_two_gt_d9]

/-- A convenient uniform weakening of Li's positive frame coefficient.
The numerical estimate uses only `exp 1 < 3`. -/
theorem cubeClump_prefactor_lower {n nStar : ℕ}
    (hn : 0 < n) (hs : 0 < nStar) :
    1 / Real.sqrt ((n : ℝ) * 8 ^ nStar) ≤
      (2 - Real.exp (1 / 2 : ℝ)) ^ ((nStar : ℝ) / 2) /
        (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1)) := by
  have hexpsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have ha : (1 / 4 : ℝ) ≤ 2 - Real.exp (1 / 2 : ℝ) := by
    nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 / 2 : ℝ)]
  have hapos : 0 < 2 - Real.exp (1 / 2 : ℝ) := by linarith
  have hbase : (2 : ℝ) ≤ 8 * (2 - Real.exp (1 / 2 : ℝ)) := by linarith
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hbase nStar
  have hsmall := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.sub_le nStar 1)
  have hrootpow : (Real.sqrt (2 - Real.exp (1 / 2 : ℝ))) ^ nStar =
      (2 - Real.exp (1 / 2 : ℝ)) ^ ((nStar : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hapos.le]
    congr 1
    ring
  rw [← hrootpow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simp only [one_mul]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n),
    Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) * 8 ^ nStar)]
  have htwo : ((Real.sqrt 2) ^ (nStar - 1)) ^ 2 = (2 : ℝ) ^ (nStar - 1) := by
    rw [← pow_mul, Nat.mul_comm (nStar - 1) 2, pow_mul]
    norm_num
  have hframe : ((Real.sqrt (2 - Real.exp (1 / 2 : ℝ))) ^ nStar) ^ 2 =
      (2 - Real.exp (1 / 2 : ℝ)) ^ nStar := by
    rw [← pow_mul, Nat.mul_comm nStar 2, pow_mul, Real.sq_sqrt hapos.le]
  rw [htwo, hframe]
  calc
    (n : ℝ) * 2 ^ (nStar - 1) ≤ n * 2 ^ nStar :=
      mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg n)
    _ ≤ n * (8 * (2 - Real.exp (1 / 2 : ℝ))) ^ nStar :=
      mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)
    _ = (2 - Real.exp (1 / 2 : ℝ)) ^ nStar * (n * 8 ^ nStar) := by
      rw [mul_pow]
      ring

/-- The packet cardinality yields the aperture factor in the current explicit
multi-clump bound.  The half-aperture comparison is kept inside the radius. -/
theorem cubeClump_packetCount_lower {d nStar s N : ℕ}
    (hs : 0 < nStar) (hsstar : 8 * nStar ≤ s) (hN : N ≤ 2 * s) :
    ((N : ℝ) / (6 * nStar)) ^ ((d : ℝ) / 2) ≤
      Real.sqrt (((2 * (s / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) := by
  let q := s / (4 * nStar)
  have hq : 2 ≤ q := (Nat.le_div_iff_mul_le (by omega : 0 < 4 * nStar)).mpr
    (by omega)
  have hlt : s < 4 * nStar * (q + 1) := by
    simpa only [q, Nat.mul_comm] using Nat.lt_mul_div_succ s (by omega : 0 < 4 * nStar)
  have hcount : s + 1 ≤ 3 * nStar * (2 * q + 1) := by nlinarith
  have hNcount : N ≤ 6 * nStar * (2 * q + 1) := by nlinarith
  have hcountR : (N : ℝ) / (6 * nStar) ≤ (2 * q + 1 : ℕ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 6 * nStar)).2
    exact_mod_cast (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hNcount)
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (N : ℝ) / (6 * nStar))
    hcountR (by positivity : 0 ≤ (d : ℝ) / 2)
  have he : ((2 * q + 1 : ℕ) : ℝ) ^ ((d : ℝ) / 2) =
      Real.sqrt ((((2 * q + 1) ^ d : ℕ) : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Nat.cast_pow,
      ← Real.rpow_natCast_mul (Nat.cast_nonneg (2 * q + 1)) d (1 / 2 : ℝ)]
    congr 1
    ring
  simpa only [he, q] using hpow

/-- Comparable-aperture version retaining the full clipped Rayleigh scale.
This is the concrete full-cube input used by `multiClumpCubeLowerBound`. -/
theorem fullCube_clump_fullAperture_lower
    {d n A nStar s N : ℕ} {τ separation θ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 1 ≤ d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hsame : ∀ i j, C.label i = C.label j → torusLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < torusLInfDistance (Y i) (Y j))
    (heven : Even s) (hsn : 8 * n ≤ s) (hN : N ≤ 2 * s)
    (hseparation : 8 * Real.pi * d * nStar / s ≤ separation)
    (hτ : τ ≤ Real.pi / (2 * d)) (hθ : 0 < θ)
    (hmin : ∀ i j, i ≠ j → θ ≤ torusLInfDistance (Y i) (Y j)) :
    1 / Real.sqrt ((n : ℝ) * 8 ^ nStar) *
      ((N : ℝ) / (6 * nStar)) ^ ((d : ℝ) / 2) *
      (min 1 ((N : ℝ) * θ / (8 * Real.pi * nStar))) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
  have hraw := fullCube_clump_clipped_lower_of_torus C hd hn hs hsize
    hsame hcross heven hsn betaOne_admissible (by simpa only [mul_one] using hseparation)
    hτ hθ hmin
  have hraw' :
      ((2 - Real.exp (1 / 2 : ℝ)) ^ ((nStar : ℝ) / 2) /
        (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1))) *
      Real.sqrt (((2 * (s / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) *
      min 1 ((s : ℝ) * θ / (4 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
    convert hraw using 1 <;> simp only [mul_one] <;> ring
  have hcoef := cubeClump_prefactor_lower hn hs
  have hcount := cubeClump_packetCount_lower (d := d) hs (by omega : 8 * nStar ≤ s) hN
  have hNreal : (N : ℝ) ≤ 2 * s := by exact_mod_cast hN
  have hquot : (N : ℝ) * θ / (8 * Real.pi * nStar) ≤
      (s : ℝ) * θ / (4 * Real.pi * nStar) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hprod := mul_le_mul_of_nonneg_right hNreal hθ.le
    have h := mul_le_mul_of_nonneg_right hprod
      (by positivity : (0 : ℝ) ≤ 4 * Real.pi * nStar)
    convert h using 1 <;> ring
  have hscaled := min_le_min (le_refl (1 : ℝ)) hquot
  have hscaledpow := pow_le_pow_left₀
    (by positivity : 0 ≤ min 1 ((N : ℝ) * θ / (8 * Real.pi * nStar))) hscaled
    (nStar - 1)
  have ha0 : 0 < 2 - Real.exp (1 / 2 : ℝ) := by
    simpa only [mul_one] using liFrameConstant_pos betaOne_admissible
  have h1 := mul_le_mul hcoef hcount (by positivity) (by positivity)
  have h2 := mul_le_mul h1 hscaledpow (by positivity) (by positivity)
  exact h2.trans hraw'

/-- Exact interface to the current factored manuscript formula. -/
theorem multiClumpCubeLowerBound_le {d n A nStar s : ℕ}
    (G : SegmentedGrid d) {τ separation : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hsame : ∀ i j, C.label i = C.label j → torusLInfDistance (Y i) (Y j) ≤ τ)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < torusLInfDistance (Y i) (Y j))
    (heven : Even s) (hsn : 8 * n ≤ s) (hN : G.minAperture ≤ 2 * s)
    (hseparation : 8 * Real.pi * d * nStar / s ≤ separation)
    (hτ : τ ≤ Real.pi / (2 * d)) (hsep : 0 < nodeSeparation Y) :
    multiClumpCubeLowerBound G n nStar (nodeSeparation Y) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
  exact fullCube_clump_fullAperture_lower C G.dimension_pos hn hs hsize
    hsame hcross heven hsn hN hseparation hτ hsep (nodeSeparation_le_pair Y)

end
end LeanNumDetect.MultiTuran.MultiClump
