import MultiTuran.ConsecutiveWindow.CubeInterpolation
import MultiTuran.MultiClump.BlockParameters

/-! # Full-aperture cube bounds with unrestricted clump geometry

Correspondence: `lem:aperture` in the consecutive-window supplement. The
cross-clump gap and maximum fiber cardinality are the only clump conditions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
open NumDetect
noncomputable section

theorem fullCube_unrestricted_clump_raw_lower
    {d n A nStar s : ℕ} {separation β Δ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 0 < d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hcube : ∀ j, InAngularCube (Y j))
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < torusLInfDistance (Y i) (Y j))
    (heven : Even s) (hsn : 8 * n ≤ s) (hβ : 1 / (2 * Real.log 2) < β)
    (hseparation : 8 * Real.pi * β * d * nStar / s ≤ separation)
    (hΔ : 0 < Δ) (hmin : ∀ i j, i ≠ j → Δ ≤ torusLInfDistance (Y i) (Y j))
    (hscale : Δ ≤ 4 * Real.pi * nStar / s) :
    (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
      Real.sqrt (((2 * (s / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) /
      (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1)) *
      ((s : ℝ) * Δ / (4 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
  obtain ⟨M,hM⟩ := heven
  have hsM : s = 2 * M := by omega
  clear hM
  subst s
  have hgap : 4 * Real.pi * β * d * nStar / M ≤ separation := by
    convert hseparation using 1 <;> push_cast <;> ring
  have hscale' : Δ ≤ 2 * Real.pi * nStar / M := by
    convert hscale using 1 <;> push_cast <;> ring
  have hraw := cube_raw_ratio_unrestricted C hd hn hs hsize hcube hcross
    (by omega : 4 * n ≤ M) hβ hgap hΔ hmin hscale'
  exact liCubeClump_raw_coefficient_le_of_ratio hn hs (by omega : 0 < M) hβ hΔ hraw

/-- The same raw bound for arbitrary real representatives of the torus. -/
theorem fullCube_unrestricted_clump_raw_lower_of_torus
    {d n A nStar s : ℕ} {separation β Δ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 0 < d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < torusLInfDistance (Y i) (Y j))
    (heven : Even s) (hsn : 8 * n ≤ s) (hβ : 1 / (2 * Real.log 2) < β)
    (hseparation : 8 * Real.pi * β * d * nStar / s ≤ separation)
    (hΔ : 0 < Δ) (hmin : ∀ i j, i ≠ j → Δ ≤ torusLInfDistance (Y i) (Y j))
    (hscale : Δ ≤ 4 * Real.pi * nStar / s) :
    (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
      Real.sqrt (((2 * (s / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) /
      (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1)) *
      ((s : ℝ) * Δ / (4 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
  let C' : ClumpSlots (A := A) (nStar := nStar) (fun j => MultiClump.principalAngularPoint (Y j)) :=
    {label := C.label,slot := C.slot,injective := C.injective}
  have hcross' (i j : Fin n) (hij : C'.label i ≠ C'.label j) :
      separation < torusLInfDistance (MultiClump.principalAngularPoint (Y i)) (MultiClump.principalAngularPoint (Y j)) := by
    rw [MultiClump.torusLInfDistance_principalAngularPoint]
    exact hcross i j hij
  have hmin' (i j : Fin n) (hij : i ≠ j) :
      Δ ≤ torusLInfDistance (MultiClump.principalAngularPoint (Y i)) (MultiClump.principalAngularPoint (Y j)) := by
    rw [MultiClump.torusLInfDistance_principalAngularPoint]
    exact hmin i j hij
  have h := fullCube_unrestricted_clump_raw_lower C' hd hn hs hsize
    (fun j => MultiClump.principalAngularPoint_mem (Y j)) hcross' heven hsn hβ hseparation hΔ hmin' hscale
  simpa only [MultiClump.fullCubeVandermonde_principalAngularPoint] using h

/-- Clipping the supplied positive spacing parameter gives the exact minimum
in the supplement, without a super-resolution-only premise. -/
theorem fullCube_unrestricted_clump_clipped_lower
    {d n A nStar s : ℕ} {separation β θ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 0 < d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < torusLInfDistance (Y i) (Y j))
    (heven : Even s) (hsn : 8 * n ≤ s) (hβ : 1 / (2 * Real.log 2) < β)
    (hseparation : 8 * Real.pi * β * d * nStar / s ≤ separation)
    (hθ : 0 < θ) (hmin : ∀ i j, i ≠ j → θ ≤ torusLInfDistance (Y i) (Y j)) :
    (2 - Real.exp (1 / (2 * β))) ^ ((nStar : ℝ) / 2) *
      Real.sqrt (((2 * (s / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) /
      (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1)) *
      min 1 ((s : ℝ) * θ / (4 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hc0 : 0 < 4 * Real.pi * (nStar : ℝ) := by positivity
  let Δ := min θ (4 * Real.pi * nStar / s)
  have hΔ : 0 < Δ := lt_min hθ (by positivity)
  have hΔmin (i j : Fin n) (hij : i ≠ j) :
      Δ ≤ torusLInfDistance (Y i) (Y j) := (min_le_left _ _).trans (hmin i j hij)
  have hfactor : (s : ℝ) * Δ / (4 * Real.pi * nStar) =
      min 1 ((s : ℝ) * θ / (4 * Real.pi * nStar)) := by
    dsimp only [Δ]
    rw [mul_min_of_nonneg _ _ hs0.le,← min_div_div_right hc0.le]
    have hunit : (s : ℝ) * (4 * Real.pi * nStar / s) / (4 * Real.pi * nStar) = 1 := by
      field_simp
    rw [hunit,min_comm]
  have h := fullCube_unrestricted_clump_raw_lower_of_torus C hd hn hs hsize hcross
    heven hsn hβ hseparation hΔ hΔmin (min_le_right _ _)
  rw [hfactor] at h
  exact h

/-- The exact displayed full-aperture coefficient, with no within-clump
geometry hypothesis. -/
theorem fullCube_unrestricted_clump_fullAperture_lower
    {d n A nStar s N : ℕ} {separation θ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 0 < d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < torusLInfDistance (Y i) (Y j))
    (heven : Even s) (hsn : 8 * n ≤ s) (hN : N ≤ 2 * s)
    (hseparation : 8 * Real.pi * d * nStar / s ≤ separation)
    (hθ : 0 < θ) (hmin : ∀ i j, i ≠ j → θ ≤ torusLInfDistance (Y i) (Y j)) :
    1 / Real.sqrt ((n : ℝ) * 8 ^ nStar) *
      ((N : ℝ) / (6 * nStar)) ^ ((d : ℝ) / 2) *
      min 1 ((N : ℝ) * θ / (8 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
  have hraw := fullCube_unrestricted_clump_clipped_lower C hd hn hs hsize hcross
    heven hsn MultiClump.betaOne_admissible (by simpa only [mul_one] using hseparation) hθ hmin
  have hraw' :
      ((2 - Real.exp (1 / 2 : ℝ)) ^ ((nStar : ℝ) / 2) /
        (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1))) *
      Real.sqrt (((2 * (s / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) *
      min 1 ((s : ℝ) * θ / (4 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
    convert hraw using 1 <;> simp only [mul_one] <;> ring
  have hcoef := MultiClump.cubeClump_prefactor_lower hn hs
  have hcount := MultiClump.cubeClump_packetCount_lower (d := d) hs (by omega : 8 * nStar ≤ s) hN
  have hNreal : (N : ℝ) ≤ 2 * s := by exact_mod_cast hN
  have hquot : (N : ℝ) * θ / (8 * Real.pi * nStar) ≤
      (s : ℝ) * θ / (4 * Real.pi * nStar) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hprod := mul_le_mul_of_nonneg_right hNreal hθ.le
    have h := mul_le_mul_of_nonneg_right hprod (by positivity : (0 : ℝ) ≤ 4 * Real.pi * nStar)
    convert h using 1 <;> ring
  have hscaled := min_le_min (le_refl (1 : ℝ)) hquot
  have hscaledpow := pow_le_pow_left₀
    (by positivity : 0 ≤ min 1 ((N : ℝ) * θ / (8 * Real.pi * nStar))) hscaled (nStar - 1)
  have ha0 : 0 < 2 - Real.exp (1 / 2 : ℝ) := by
    simpa only [mul_one] using liFrameConstant_pos MultiClump.betaOne_admissible
  have h1 := mul_le_mul hcoef hcount (by positivity) (by positivity)
  have h2 := mul_le_mul h1 hscaledpow (by positivity) (by positivity)
  exact h2.trans hraw'

/-- The supplement's selected even full-aperture cube and its exact
coefficient. The gap is stated directly at aperture `N`; clump diameters
are unrestricted. -/
theorem selected_fullAperture_unrestricted_clump_lower
    {d n A nStar N : ℕ} {θ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 2 ≤ d) (hn : 2 ≤ n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hN : max (16 * n) (32 * d ^ 2 * nStar) ≤ N)
    (hcross : ∀ i j, C.label i ≠ C.label j →
      16 * Real.pi * d * nStar / N < torusLInfDistance (Y i) (Y j))
    (hθ : 0 < θ) (hmin : ∀ i j, i ≠ j → θ ≤ torusLInfDistance (Y i) (Y j)) :
    1 / Real.sqrt ((n : ℝ) * 8 ^ nStar) *
      ((N : ℝ) / (6 * nStar)) ^ ((d : ℝ) / 2) *
      min 1 ((N : ℝ) * θ / (8 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 (MultiClump.fullApertureCubeSide N) Y)
        (n - 1) := by
  have hn0 : 0 < n := by omega
  have hNn : 16 * n ≤ N := (le_max_left _ _).trans hN
  have hN4 : 4 ≤ N := by omega
  have hprops := MultiClump.fullApertureCubeSide_properties hN4
  have hlarge := MultiClump.fullApertureCubeSide_large hn0 hNn
  have hs0 : (0 : ℝ) < MultiClump.fullApertureCubeSide N := by
    exact_mod_cast (show 0 < MultiClump.fullApertureCubeSide N by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNs : (N : ℝ) ≤ 2 * (MultiClump.fullApertureCubeSide N : ℝ) := by
    exact_mod_cast hprops.2.2.1
  have hgap : 8 * Real.pi * d * nStar / (MultiClump.fullApertureCubeSide N : ℝ) ≤
      16 * Real.pi * d * nStar / N := by
    apply (div_le_div_iff₀ hs0 hN0).mpr
    convert mul_le_mul_of_nonneg_left hNs
      (show 0 ≤ 8 * Real.pi * d * nStar by positivity) using 1 <;> ring
  exact fullCube_unrestricted_clump_fullAperture_lower C (by omega) hn0 hs hsize
    hcross hprops.1 hlarge hprops.2.2.1 hgap hθ hmin

/-- The selected-aperture bound using the manuscript's measured aperture
and actual minimum periodic node spacing. -/
theorem selected_multiClumpCubeLowerBound_le {d n A nStar : ℕ}
    (H : SegmentedGrid d) (Y : Fin n → Point d)
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 2 ≤ d) (hn : 2 ≤ n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hN : max (16 * n) (32 * d ^ 2 * nStar) ≤ H.minAperture)
    (hcross : ∀ i j, C.label i ≠ C.label j →
      16 * Real.pi * d * nStar / H.minAperture < torusLInfDistance (Y i) (Y j))
    (hsep : 0 < nodeSeparation Y) :
    MultiClump.multiClumpCubeLowerBound H n nStar (nodeSeparation Y) ≤
      matrixSingularValue
        (fullCubeVandermonde 1 (MultiClump.fullApertureCubeSide H.minAperture) Y) (n - 1) := by
  exact selected_fullAperture_unrestricted_clump_lower C hd hn hs hsize hN
    hcross hsep (nodeSeparation_le_pair Y)

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
