import MultiTuran.ConsecutiveWindow.CubeWithinClump

/-! # Full-cube cardinal polynomials for arbitrary clump diameters

The color-frame localization and the original cube smoothing interface are
shared with NumDetect. Only the within-clump factors use the unrestricted
torus construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators Matrix

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
open NumDetect
noncomputable section

theorem liInterpolationPolynomial_unrestricted
    {d n A nStar M : ℕ} {η β Δ : ℝ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x) (anchor : Fin n)
    (hd : 0 < d) (hs : 0 < nStar) (hM : 2 * nStar ≤ M)
    (hΔ : 0 < Δ) (hβ : 1 / (2 * Real.log 2) < β)
    (hcube : ∀ j, InAngularCube (x j))
    (hcross : ∀ i j, C.label i ≠ C.label j → η < periodicLInfDistance (x i) (x j))
    (hη : 4 * Real.pi * β * d / ((M / nStar : ℕ) + 1) ≤ η)
    (hmin : ∀ i j, i ≠ j → Δ ≤ torusLInfDistance (x i) (x j))
    (hscale : Δ ≤ 2 * Real.pi * nStar / M) :
    ∃ P : SegmentedPolynomial d (M + (M - M / nStar)) 0 (2 * M + 1),
      (∀ j, P.angularValue (x j) = if anchor = j then 1 else 0) ∧
      P.mass ≤ (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar *
        (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1) := by
  classical
  have ha := liFrameConstant_pos hβ
  have hdiv : M / nStar ≤ M := Nat.div_le_self M nStar
  have hK : nStar * (M / nStar) ≤ M := by simpa [Nat.mul_comm] using Nat.div_mul_le_self M nStar
  have hKD : M / nStar < 2 * M + 1 := by have := Nat.div_le_self M nStar; omega
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
  obtain ⟨G₀,hG1,hG0,hGmass⟩ :=
    localizationPolynomial_of_colorFrames C anchor hKD hprodD ha hframes
  let G : SegmentedPolynomial d M 0 (2 * M + 1) := G₀.widen hK le_rfl (by omega)
  obtain ⟨B₀,hBvalue,hBmass⟩ := withinClumpPolynomial_unrestricted C anchor hd hs hM
    hcube hΔ hmin hscale
  have hR : M - M / nStar ≤ M := Nat.sub_le _ _
  let B : SegmentedPolynomial d (M - M / nStar) 0 (2 * M + 1) :=
    B₀.coarseToFine (by omega)
  have hsum : M + (M - M / nStar) < 2 * M + 1 := by omega
  let P := G.mul B hsum
  refine ⟨P,?_,?_⟩
  · intro j
    simp only [P,SegmentedPolynomial.angularValue_mul,B,
      SegmentedPolynomial.angularValue_coarseToFine,G,SegmentedPolynomial.angularValue_widen]
    by_cases hj : C.label j = C.label anchor
    · rw [hBvalue j hj]
      by_cases haj : anchor = j
      · subst j
        simp [hG1]
      · simp [haj]
    · rw [hG0 j hj,zero_mul]
      have haj : anchor ≠ j := fun h => hj (congrArg C.label h.symm)
      simp [haj]
  · have hBmass' : B.mass ≤ (Real.sqrt 2 /
        (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1) := by simpa [B] using hBmass
    have hGmass' : G.mass ≤ (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar := by
      simpa [G] using hGmass
    exact (SegmentedPolynomial.mass_mul_le G B hsum).trans
      (mul_le_mul hGmass' hBmass' B.mass_nonneg (by positivity))

/-- The original shared interpolation-to-singular-value interface applied to
unrestricted clumps. No clump-diameter premise appears in this statement. -/
theorem cube_raw_ratio_unrestricted
    {d n A nStar M : ℕ} {η β Δ : ℝ} {Y : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 0 < d) (hn : 0 < n) (hs : 0 < nStar) (hsize : nStar ≤ n)
    (hcube : ∀ j, InAngularCube (Y j))
    (hcross : ∀ i j, C.label i ≠ C.label j → η < torusLInfDistance (Y i) (Y j))
    (hM : 2 * nStar ≤ M) (hβ : 1 / (2 * Real.log 2) < β)
    (hη : 4 * Real.pi * β * d * nStar / M ≤ η) (hΔ : 0 < Δ)
    (hmin : ∀ i j, i ≠ j → Δ ≤ torusLInfDistance (Y i) (Y j))
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
  have hη' : 4 * Real.pi * β * d / ((M / nStar : ℕ) + 1) ≤ η := by
    apply le_trans _ hη
    apply (div_le_div_iff₀ (by positivity) hMR).mpr
    convert mul_le_mul_of_nonneg_left hK
      (show 0 ≤ 4 * Real.pi * β * d by positivity) using 1 <;> ring
  have hcross' (i j : Fin n) (hij : C.label i ≠ C.label j) :
      η < periodicLInfDistance (Y i) (Y j) := by
    rw [← MultiClump.torusLInfDistance_eq_periodicLInfDistance (hcube i) (hcube j)]
    exact hcross i j hij
  choose P hPv hPm using fun anchor => liInterpolationPolynomial_unrestricted C anchor
    hd hs (by omega : 2 * nStar ≤ M) hΔ hβ hcube hcross' hη' hmin hscale
  let H := (1 / Real.sqrt (2 - Real.exp (1 / (2 * β)))) ^ nStar *
    (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1)
  have ha := liFrameConstant_pos hβ
  have hH : 0 < H := by dsimp [H]; positivity
  have h := liCubeClump_raw_ratio_of_interpolation Y hn hH P hPv hPm
  rw [MultiClump.segmentedVandermonde_oneBlock_singularValue] at h
  simpa only [H] using h

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
