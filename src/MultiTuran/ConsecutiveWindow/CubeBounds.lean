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
    (heven : Even s) (hsn : 4 * nStar ≤ s) (hβ : 1 / (2 * Real.log 2) < β)
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
    (by omega : 2 * nStar ≤ M) hβ hgap hΔ hmin hscale'
  exact liCubeClump_raw_coefficient_le_of_ratio hn hs (by omega : 0 < M) hβ hΔ hraw

/-- The same raw bound for arbitrary real representatives of the torus. -/
theorem fullCube_unrestricted_clump_raw_lower_of_torus
    {d n A nStar s : ℕ} {separation β Δ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 0 < d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < torusLInfDistance (Y i) (Y j))
    (heven : Even s) (hsn : 4 * nStar ≤ s) (hβ : 1 / (2 * Real.log 2) < β)
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
    (heven : Even s) (hsn : 4 * nStar ≤ s) (hβ : 1 / (2 * Real.log 2) < β)
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

/-- The positive separated-frame coefficient at `β = 1`, with a rational
exponential bound that keeps the uniform clump factor at `6`. -/
theorem windowCube_prefactor_lower {n nStar : ℕ}
    (hn : 0 < n) (hs : 0 < nStar) :
    1 / Real.sqrt ((n : ℝ) * 6 ^ nStar) ≤
      (2 - Real.exp (1 / 2 : ℝ)) ^ ((nStar : ℝ) / 2) /
        (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1)) := by
  have hexp := Real.exp_bound' (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at hexp
  have ha : (1 / 3 : ℝ) ≤ 2 - Real.exp (1 / 2 : ℝ) := by linarith
  have hapos : 0 < 2 - Real.exp (1 / 2 : ℝ) := by linarith
  have hbase : (2 : ℝ) ≤ 6 * (2 - Real.exp (1 / 2 : ℝ)) := by linarith
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
    Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) * 6 ^ nStar)]
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
    _ ≤ n * (6 * (2 - Real.exp (1 / 2 : ℝ))) ^ nStar :=
      mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg n)
    _ = (2 - Real.exp (1 / 2 : ℝ)) ^ nStar * (n * 6 ^ nStar) := by
      rw [mul_pow]
      ring

/-- The packet count retains four fifths of the measured aperture. -/
theorem windowCube_packetCount_lower {d nStar s N : ℕ}
    (hs : 0 < nStar) (hsstar : 8 * nStar ≤ s) (hN : 4 * N ≤ 5 * s) :
    Real.sqrt (((N : ℝ) / (3 * nStar)) ^ d) ≤
      Real.sqrt (((2 * (s / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) := by
  let q := s / (4 * nStar)
  have hq : 2 ≤ q := (Nat.le_div_iff_mul_le (by omega : 0 < 4 * nStar)).mpr
    (by omega)
  have hlt : s < 4 * nStar * (q + 1) := by
    simpa only [q, Nat.mul_comm] using Nat.lt_mul_div_succ s (by omega : 0 < 4 * nStar)
  have hlinear : 5 * (q + 1) ≤ 3 * (2 * q + 1) := by omega
  have hweighted := Nat.mul_le_mul_left (4 * nStar) hlinear
  have hcount : 5 * s < 12 * nStar * (2 * q + 1) := by nlinarith only [hlt, hweighted]
  have hNcount : N ≤ 3 * nStar * (2 * q + 1) := by nlinarith
  have hcountR : (N : ℝ) / (3 * nStar) ≤ (2 * q + 1 : ℕ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * nStar)).2
    exact_mod_cast (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hNcount)
  apply Real.sqrt_le_sqrt
  simpa only [Nat.cast_pow] using pow_le_pow_left₀ (by positivity) hcountR d

/-- The full-aperture coefficient with unrestricted clump geometry. -/
theorem fullCube_unrestricted_clump_fullAperture_lower
    {d n A nStar s N : ℕ} {separation θ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 0 < d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hcross : ∀ i j, C.label i ≠ C.label j → separation < torusLInfDistance (Y i) (Y j))
    (heven : Even s) (hsn : 8 * nStar ≤ s) (hN : 4 * N ≤ 5 * s)
    (hseparation : 8 * Real.pi * d * nStar / s ≤ separation)
    (hθ : 0 < θ) (hmin : ∀ i j, i ≠ j → θ ≤ torusLInfDistance (Y i) (Y j)) :
    1 / Real.sqrt ((n : ℝ) * 6 ^ nStar) *
      Real.sqrt (((N : ℝ) / (3 * nStar)) ^ d) *
      min 1 ((N : ℝ) * θ / (5 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
  have hraw := fullCube_unrestricted_clump_clipped_lower C hd hn hs hsize hcross
    heven (by omega : 4 * nStar ≤ s) MultiClump.betaOne_admissible
    (by simpa only [mul_one] using hseparation) hθ hmin
  have hraw' :
      ((2 - Real.exp (1 / 2 : ℝ)) ^ ((nStar : ℝ) / 2) /
        (Real.sqrt n * (Real.sqrt 2) ^ (nStar - 1))) *
      Real.sqrt (((2 * (s / (4 * nStar)) + 1) ^ d : ℕ) : ℝ) *
      min 1 ((s : ℝ) * θ / (4 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 s Y) (n - 1) := by
    convert hraw using 1 <;> simp only [mul_one] <;> ring
  have hcoef := windowCube_prefactor_lower hn hs
  have hcount := windowCube_packetCount_lower (d := d) hs hsn hN
  have hNreal : (4 : ℝ) * N ≤ 5 * s := by exact_mod_cast hN
  have hquot : (N : ℝ) * θ / (5 * Real.pi * nStar) ≤
      (s : ℝ) * θ / (4 * Real.pi * nStar) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hprod := mul_le_mul_of_nonneg_right hNreal hθ.le
    have h := mul_le_mul_of_nonneg_right hprod (by positivity : (0 : ℝ) ≤ Real.pi * nStar)
    convert h using 1 <;> ring
  have hscaled := min_le_min (le_refl (1 : ℝ)) hquot
  have hscaledpow := pow_le_pow_left₀
    (by positivity : 0 ≤ min 1 ((N : ℝ) * θ / (5 * Real.pi * nStar))) hscaled (nStar - 1)
  have ha0 : 0 < 2 - Real.exp (1 / 2 : ℝ) := by
    simpa only [mul_one] using liFrameConstant_pos MultiClump.betaOne_admissible
  have h1 := mul_le_mul hcoef hcount (by positivity) (by positivity)
  have h2 := mul_le_mul h1 hscaledpow (by positivity) (by positivity)
  exact h2.trans hraw'

/-- The selected even full-aperture cube. The clump gap is stated directly
at aperture `N`, and clump diameters are unrestricted. -/
theorem selected_fullAperture_unrestricted_clump_lower
    {d n A nStar N : ℕ} {θ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 2 ≤ d) (hn : 2 ≤ n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hN : 10 * nStar ≤ N)
    (hcross : ∀ i j, C.label i ≠ C.label j →
      10 * Real.pi * d * nStar / N < torusLInfDistance (Y i) (Y j))
    (hθ : 0 < θ) (hmin : ∀ i j, i ≠ j → θ ≤ torusLInfDistance (Y i) (Y j)) :
    1 / Real.sqrt ((n : ℝ) * 6 ^ nStar) *
      Real.sqrt (((N : ℝ) / (3 * nStar)) ^ d) *
      min 1 ((N : ℝ) * θ / (5 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue (fullCubeVandermonde 1 (MultiClump.fullApertureCubeSide N) Y)
        (n - 1) := by
  have hn0 : 0 < n := by omega
  have hN4 : 4 ≤ N := by omega
  have hprops := MultiClump.fullApertureCubeSide_properties hN4
  have hlarge : 8 * nStar ≤ MultiClump.fullApertureCubeSide N := by omega
  have hs0 : (0 : ℝ) < MultiClump.fullApertureCubeSide N := by
    exact_mod_cast (show 0 < MultiClump.fullApertureCubeSide N by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNs : 4 * N ≤ 5 * MultiClump.fullApertureCubeSide N := by omega
  have hNsR : (4 : ℝ) * N ≤ 5 * MultiClump.fullApertureCubeSide N := by exact_mod_cast hNs
  have hgap : 8 * Real.pi * d * nStar / (MultiClump.fullApertureCubeSide N : ℝ) ≤
      10 * Real.pi * d * nStar / N := by
    apply (div_le_div_iff₀ hs0 hN0).mpr
    convert mul_le_mul_of_nonneg_left hNsR
      (show 0 ≤ 2 * Real.pi * d * nStar by positivity) using 1 <;> ring
  exact fullCube_unrestricted_clump_fullAperture_lower C (by omega) hn0 hs hsize
    hcross hprops.1 hlarge hNs hgap hθ hmin

/-- The selected-aperture bound using the manuscript's measured aperture
and actual minimum periodic node spacing. -/
theorem selected_multiClumpCubeLowerBound_le {d n A nStar : ℕ}
    (H : SegmentedGrid d) (Y : Fin n → Point d)
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 2 ≤ d) (hn : 2 ≤ n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hN : 10 * nStar ≤ H.minAperture)
    (hcross : ∀ i j, C.label i ≠ C.label j →
      10 * Real.pi * d * nStar / H.minAperture < torusLInfDistance (Y i) (Y j))
    (hsep : 0 < nodeSeparation Y) :
    1 / Real.sqrt ((n : ℝ) * 6 ^ nStar) *
      ((H.minAperture : ℝ) / (3 * nStar)) ^ ((d : ℝ) / 2) *
      min 1 ((H.minAperture : ℝ) * nodeSeparation Y / (5 * Real.pi * nStar)) ^ (nStar - 1) ≤
      matrixSingularValue
        (fullCubeVandermonde 1 (MultiClump.fullApertureCubeSide H.minAperture) Y) (n - 1) := by
  have h := selected_fullAperture_unrestricted_clump_lower C hd hn hs hsize hN
    hcross hsep (nodeSeparation_le_pair Y)
  have hpower : Real.sqrt (((H.minAperture : ℝ) / (3 * nStar)) ^ d) =
      ((H.minAperture : ℝ) / (3 * nStar)) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul
      (by positivity : 0 ≤ (H.minAperture : ℝ) / (3 * nStar)) d (1 / 2 : ℝ)]
    congr 1
    ring
  rw [hpower] at h
  exact h

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
