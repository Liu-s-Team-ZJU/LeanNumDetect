import MultiTuran.ConsecutiveWindow.CubeFactors

/-! # Within-clump interpolation with unrestricted torus geometry -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.ConsecutiveWindow
open NumDetect
noncomputable section

/-- The within-clump cardinal polynomial uses only the number of neighbors
and their positive periodic separation, not their diameter. -/
theorem withinClumpPolynomial_unrestricted
    {d n A nStar M : ℕ} {Δ : ℝ} {x : Fin n → Point d}
    (C : ClumpSlots (A := A) (nStar := nStar) x) (anchor : Fin n)
    (hd : 0 < d) (hs : 0 < nStar) (hM : 2 * nStar ≤ M)
    (hcube : ∀ j, InAngularCube (x j)) (hΔ : 0 < Δ)
    (hmin : ∀ i j, i ≠ j → Δ ≤ torusLInfDistance (x i) (x j))
    (hscale : Δ ≤ 2 * Real.pi * nStar / M) :
    ∃ P : SegmentedPolynomial d 0 (M - M / nStar) 1,
      (∀ j, C.label j = C.label anchor →
        P.angularValue (x j) = if anchor = j then 1 else 0) ∧
      P.mass ≤ (Real.sqrt 2 /
        (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ (nStar - 1) := by
  classical
  let S := C.neighbors anchor
  let q := S.card
  let e : Fin q ≃ S := (Fintype.equivFinOfCardEq (by simp [q])).symm
  have hq : q ≤ nStar - 1 := C.neighbors_card anchor
  have hsR : (0 : ℝ) < nStar := by exact_mod_cast hs
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hT : 2 ≤ (M : ℝ) / nStar := by
    apply (le_div_iff₀ hsR).mpr
    exact_mod_cast hM
  have hΔhalf : 0 < Δ / 2 := by positivity
  have hTD : ((M : ℝ) / nStar) * (Δ / 2) ≤ Real.pi := by
    have h := (le_div_iff₀ hMR).mp hscale
    calc
      _ = ((M : ℝ) * Δ) / (2 * nStar) := by ring
      _ ≤ Real.pi := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * nStar)).mpr
        nlinarith only [h]
  choose F hF1 hF0 hFm using fun i : Fin q =>
    torus_neighbor_factor hd hT hΔhalf hTD (x anchor) (x (e i))
      (hcube anchor) (hcube (e i))
      (by
        have hne := ((C.mem_neighbors anchor (e i)).mp (e i).property).1
        have h := hmin (e i) anchor hne
        linarith)
  have hfloor : ⌊(M : ℝ) / nStar⌋₊ = M / nStar := by
    rw [Nat.floor_div_natCast,Nat.floor_natCast]
  have hbudget : ⌊(M : ℝ) / nStar⌋₊ * q ≤ M - M / nStar := by
    rw [hfloor]
    have hqsucc : q + 1 ≤ nStar := by omega
    have hmul := Nat.mul_le_mul_right (M / nStar) hqsucc
    have hdiv := Nat.div_mul_le_self M nStar
    have hsum : (M / nStar) * q + M / nStar ≤ M := by nlinarith
    omega
  let P : SegmentedPolynomial d 0 (M - M / nStar) 1 :=
    (SegmentedPolynomial.prod q F (by simp)).widen (by simp) hbudget (by norm_num)
  have hvalue (y : Point d) : P.angularValue y = ∏ i, (F i).angularValue y := by
    simp only [P,SegmentedPolynomial.angularValue_widen,
      SegmentedPolynomial.angularValue_prod]
  have hfactor : 1 ≤ Real.sqrt 2 /
      (((M : ℝ) / nStar) * (Δ / 2) / Real.pi) := by
    have hden : 0 < ((M : ℝ) / nStar) * (Δ / 2) / Real.pi := by positivity
    have hdenOne : ((M : ℝ) / nStar) * (Δ / 2) / Real.pi ≤ 1 :=
      (div_le_one Real.pi_pos).mpr hTD
    have hroot : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    apply (le_div_iff₀ hden).mpr
    nlinarith
  refine ⟨P,?_,?_⟩
  · intro j hj
    rw [hvalue]
    by_cases haj : anchor = j
    · subst j
      simp only [ite_true]
      exact Finset.prod_eq_one (fun i _ => hF1 i)
    · rw [if_neg haj]
      have hjS : j ∈ S := by simp [S,Ne.symm haj,hj]
      let j' : S := ⟨j,hjS⟩
      have he : (e (e.symm j')).val = j := congrArg Subtype.val (e.apply_symm_apply j')
      apply Finset.prod_eq_zero (Finset.mem_univ (e.symm j'))
      have hz := hF0 (e.symm j')
      simpa only [he] using hz
  · calc
      P.mass = (SegmentedPolynomial.prod q F (by simp)).mass :=
        SegmentedPolynomial.mass_widen _ _ _ _
      _ ≤ ∏ i, (F i).mass := SegmentedPolynomial.mass_prod_le F (by simp)
      _ ≤ ∏ _i : Fin q, Real.sqrt 2 /
          (((M : ℝ) / nStar) * (Δ / 2) / Real.pi) :=
        Finset.prod_le_prod (fun i _ => (F i).mass_nonneg) (fun i _ => hFm i)
      _ = (Real.sqrt 2 / (((M : ℝ) / nStar) * (Δ / 2) / Real.pi)) ^ q := by
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      _ ≤ _ := pow_le_pow_right₀ hfactor hq

end
end LeanNumDetect.MultiTuran.ConsecutiveWindow
