import General.Fourier.CubeShiftPaths

/-! Common integer translations of the concrete whitened Fourier frame. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators InnerProductSpace
open Matrix WithLp

namespace LeanNumDetect.CubeShiftBounds
noncomputable section

def integerRootMultiplier {d n : ℕ} (z : Fin n → Fin d → ℂ) (t : Fin d → ℤ) (j : Fin n) : ℂ :=
  ∏ r : Fin d, z j r ^ t r

def coefficientTranslation {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℤ) : Matrix (Fin n) (Fin n) ℂ :=
  P⁻¹ * Matrix.diagonal (integerRootMultiplier z t) * P

def cubeTranslation {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℤ) : Matrix (Fin n) (Fin n) ℂ :=
  (coefficientTranslation z P t)ᴴ

theorem integerRootMultiplier_add {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (hz : ∀ j r, z j r ≠ 0) (s t : Fin d → ℤ) :
    integerRootMultiplier z (s + t) =
      fun j => integerRootMultiplier z s j * integerRootMultiplier z t j := by
  funext j
  unfold integerRootMultiplier
  simp only [Pi.add_apply]
  simp_rw [zpow_add₀ (hz j _)]
  rw [Finset.prod_mul_distrib]

theorem cubeTranslation_zero {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) : cubeTranslation z P 0 = 1 := by
  letI := hP.invertible
  have hm : integerRootMultiplier z (0 : Fin d → ℤ) = fun _ : Fin n => (1 : ℂ) := by
    funext j
    simp only [integerRootMultiplier, Pi.zero_apply, zpow_zero, Finset.prod_const_one]
  simp only [cubeTranslation, coefficientTranslation, hm, Matrix.diagonal_one,
    Matrix.mul_one, Matrix.inv_mul_of_invertible, Matrix.conjTranspose_one]

theorem coefficientTranslation_intertwining {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (t : Fin d → ℤ) :
    P * coefficientTranslation z P t = Matrix.diagonal (integerRootMultiplier z t) * P := by
  letI := hP.invertible
  simp only [coefficientTranslation, ← Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
    Matrix.one_mul]

theorem cubeTranslation_add {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hz : ∀ j r, z j r ≠ 0) (s t : Fin d → ℤ) :
    cubeTranslation z P (s + t) = cubeTranslation z P t * cubeTranslation z P s := by
  letI := hP.invertible
  have hm : coefficientTranslation z P (s + t) =
      coefficientTranslation z P s * coefficientTranslation z P t := by
    unfold coefficientTranslation
    rw [integerRootMultiplier_add z hz, ← Matrix.diagonal_mul_diagonal']
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc P P⁻¹,
      Matrix.mul_inv_of_invertible, Matrix.one_mul]
  simp only [cubeTranslation, hm, Matrix.conjTranspose_mul]

theorem cubeTranslation_neg_mul {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hz : ∀ j r, z j r ≠ 0) (t : Fin d → ℤ) :
    cubeTranslation z P (-t) * cubeTranslation z P t = 1 := by
  rw [← cubeTranslation_add z P hP hz t (-t), add_neg_cancel,
    cubeTranslation_zero z P hP]

theorem cubeTranslation_single_nat {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (r : Fin d) (q : ℕ) :
    cubeTranslation z P (Pi.single r (q : ℤ)) = coordinateShift z P r q := by
  have hm : integerRootMultiplier z (Pi.single r (q : ℤ)) = fun j => z j r ^ q := by
    funext j
    unfold integerRootMultiplier
    rw [Finset.prod_eq_single r]
    · simp only [Pi.single_eq_same, zpow_natCast]
    · intro s _ hs
      simp only [Pi.single_eq_of_ne hs, zpow_zero]
    · simp
  simp only [cubeTranslation, coefficientTranslation, hm, coordinateShift, coefficientShift]

theorem cubeTranslation_single_neg_nat {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (r : Fin d) (q : ℕ) :
    cubeTranslation z P (Pi.single r (-(q : ℤ))) =
      coordinateShift (fun j s => (z j s)⁻¹) P r q := by
  have hm : integerRootMultiplier z (Pi.single r (-(q : ℤ))) = fun j => ((z j r)⁻¹) ^ q := by
    funext j
    unfold integerRootMultiplier
    rw [Finset.prod_eq_single r]
    · simp only [Pi.single_eq_same, _root_.zpow_neg, zpow_natCast, inv_pow]
    · intro s _ hs
      simp only [Pi.single_eq_of_ne hs, zpow_zero]
    · simp
  simp only [cubeTranslation, coefficientTranslation, hm, coordinateShift, coefficientShift]

/-- Common translation norm for a displacement between two cube points. -/
theorem cubeTranslation_difference_norm_le {d n L : ℕ}
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L)
    (k ell : Fin d → Fin (L + 1)) :
    ‖(cubeTranslation z P (fun r => (ell r).val - (k r).val)).toEuclideanLin.toContinuousLinearMap‖ ≤
      cubeShiftComparisonConstant d n := by
  have hnz : ∀ j r, z j r ≠ 0 := by
    intro j r h
    have ht := hz j r
    rw [h, norm_zero] at ht
    norm_num at ht
  let Q := L / (2 * n)
  have hbudget := coarseBudget_of_bandwidth hn hL
  have hcover : ∀ r, (coordinateDifference k ell r).val ≤ (4 * n) * Q := by
    intro r
    have hr := (coordinateDifference k ell r).isLt
    exact (by omega : (coordinateDifference k ell r).val ≤ L).trans hbudget.2.2
  let path := mixedCoordinatePath (4 * n) Q k ell
  let s := fun t r => ((path t r).val : ℤ) - (k r).val
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold cubeShiftComparisonConstant; positivity)
  intro v₀
  change ‖(cubeTranslation z P (fun r => ((ell r).val : ℤ) - (k r).val)).toEuclideanLin v₀‖ ≤
    cubeShiftComparisonConstant d n * ‖v₀‖
  let v := fun t => (cubeTranslation z P (s t)).toEuclideanLin v₀
  have hstep : ∀ t, t < (4 * n) * d → ‖v (t + 1)‖ ≤ (2 : ℝ) ^ n * ‖v t‖ := by
    intro t ht
    obtain ⟨r, q, hq, hchange⟩ := mixedCoordinatePath_step (4 * n) Q (by omega)
      k ell hcover t ht
    have hnq : n * q ≤ L + 1 := (Nat.mul_le_mul_left n hq).trans hbudget.2.1
    rcases hchange with hplus | hminus
    · have hs : s (t + 1) = s t + Pi.single r (q : ℤ) := by
        funext a
        have h := congrFun hplus a
        by_cases ha : a = r
        · subst a
          rw [Function.update_self] at h
          simp only [s, path, Pi.add_apply, Pi.single_eq_same]
          change ((mixedCoordinatePath (4 * n) Q k ell (t + 1) r).val : ℤ) - _ = _
          omega
        · rw [Function.update_of_ne ha] at h
          simp only [s, path, Pi.add_apply, Pi.single_eq_of_ne ha, add_zero]
          exact_mod_cast congrArg (fun m : ℕ => (m : ℤ) - (k a).val) h
      dsimp [v]
      rw [hs, cubeTranslation_add z P hP hnz, cubeTranslation_single_nat,
        Matrix.toLpLin_mul_same]
      have hb := coordinateShift_norm_le z P hP (L + 1) hwhite r (fun j => (hz j r).le) q hnq
      exact ((coordinateShift z P r q).toEuclideanLin.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    · have hs : s (t + 1) = s t + Pi.single r (-(q : ℤ)) := by
        funext a
        have h := congrFun hminus a
        by_cases ha : a = r
        · subst a
          rw [Function.update_self] at h
          simp only [s, path, Pi.add_apply, Pi.single_eq_same]
          change ((mixedCoordinatePath (4 * n) Q k ell (t + 1) r).val : ℤ) - _ = _
          omega
        · rw [Function.update_of_ne ha] at h
          simp only [s, path, Pi.add_apply, Pi.single_eq_of_ne ha, add_zero]
          exact_mod_cast (congrArg (fun m : ℕ => (m : ℤ) - (k a).val) h).symm
      dsimp [v]
      rw [hs, cubeTranslation_add z P hP hnz, cubeTranslation_single_neg_nat,
        Matrix.toLpLin_mul_same]
      have hb := coordinateShift_inverseRoots_norm_le z P hP (L + 1) hwhite r (fun j => hz j r) q hnq
      exact ((coordinateShift (fun j a => (z j a)⁻¹) P r q).toEuclideanLin.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have h := norm_path_endpoint_le v (by positivity : (0 : ℝ) ≤ 2 ^ n) ((4 * n) * d) hstep
  have hs0 : s 0 = 0 := by
    funext r
    simp only [s, path, mixedCoordinatePath_zero, sub_self, Pi.zero_apply]
  have hsend : s ((4 * n) * d) = fun r => ((ell r).val : ℤ) - (k r).val := by
    funext r
    simp only [s, path, mixedCoordinatePath_end _ _ _ _ hcover]
  dsimp [v] at h
  rw [hs0, hsend, cubeTranslation_zero z P hP] at h
  simpa only [Matrix.toLpLin_one, LinearMap.id_apply, cubeShiftComparisonConstant] using h

def integerRawCubeRootRow {d n : ℕ} (z : Fin n → Fin d → ℂ) (k : Fin d → ℤ) :
    EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun j => star (integerRootMultiplier z k j))

def integerIsotropicCubeRootRow {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) (k : Fin d → ℤ) :
    EuclideanSpace ℂ (Fin n) :=
  (Real.sqrt ((N ^ d : ℕ) : ℝ) : ℂ) • Pᴴ.toEuclideanLin (integerRawCubeRootRow z k)

theorem integerIsotropicCubeRootRow_nat {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) (k : Fin d → ℕ) :
    integerIsotropicCubeRootRow z P N (fun r => (k r : ℤ)) = isotropicCubeRootRow z P N k := by
  simp only [integerIsotropicCubeRootRow, isotropicCubeRootRow, Fintype.card_fin,
    whitenedCubeRootRow, integerRawCubeRootRow, rawCubeRootRow,
    integerRootMultiplier, zpow_natCast]

theorem integerRawCubeRootRow_translation {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (hz : ∀ j r, z j r ≠ 0) (k t : Fin d → ℤ) :
    integerRawCubeRootRow z (k + t) =
      (Matrix.diagonal (integerRootMultiplier z t))ᴴ.toEuclideanLin (integerRawCubeRootRow z k) := by
  rw [Matrix.diagonal_conjTranspose, Matrix.toLpLin_apply]
  ext j
  simp only [integerRawCubeRootRow, PiLp.toLp_apply]
  rw [Matrix.mulVec_diagonal, integerRootMultiplier_add z hz]
  simp only [star_mul, Pi.star_apply]

theorem integerIsotropicCubeRootRow_translation {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hz : ∀ j r, z j r ≠ 0) (N : ℕ) (k t : Fin d → ℤ) :
    integerIsotropicCubeRootRow z P N (k + t) =
      (cubeTranslation z P t).toEuclideanLin (integerIsotropicCubeRootRow z P N k) := by
  have hm : cubeTranslation z P t * Pᴴ =
      Pᴴ * (Matrix.diagonal (integerRootMultiplier z t))ᴴ := by
    have h := congrArg Matrix.conjTranspose (coefficientTranslation_intertwining z P hP t)
    simpa only [Matrix.conjTranspose_mul, cubeTranslation] using h
  unfold integerIsotropicCubeRootRow
  rw [integerRawCubeRootRow_translation z hz]
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, ← hm,
    Matrix.toLpLin_mul_same, map_smul]
  rfl

/-- Natural positive specialization used by translated cube bases. -/
def naturalCubeTranslation {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℕ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (cubeTranslation z P (fun r => (t r : ℤ))).toEuclideanLin.toContinuousLinearMap

theorem isotropicCubeRootRow_natural_translation {d n : ℕ} (z : Fin n → Fin d → ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hz : ∀ j r, z j r ≠ 0) (N : ℕ) (k t : Fin d → ℕ) :
    isotropicCubeRootRow z P N (k + t) = naturalCubeTranslation z P t (isotropicCubeRootRow z P N k) := by
  have h := integerIsotropicCubeRootRow_translation z P hP hz N
    (fun r => (k r : ℤ)) (fun r => (t r : ℤ))
  have hcast : (fun r => ((k + t) r : ℤ)) =
      (fun r => (k r : ℤ)) + (fun r => (t r : ℤ)) := by
    funext r
    simp only [Pi.add_apply, Nat.cast_add]
  rw [← hcast, integerIsotropicCubeRootRow_nat, integerIsotropicCubeRootRow_nat] at h
  exact h

theorem cubeTranslation_norm_le {d n L : ℕ}
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L)
    (t : Fin d → ℤ) (ht : ∀ r, |t r| ≤ (L : ℤ)) :
    ‖(cubeTranslation z P t).toEuclideanLin.toContinuousLinearMap‖ ≤
      cubeShiftComparisonConstant d n := by
  let k : Fin d → Fin (L + 1) := fun r => ⟨(-t r).toNat, by
    have h := abs_le.mp (ht r)
    omega⟩
  let ell : Fin d → Fin (L + 1) := fun r => ⟨(t r).toNat, by
    have h := abs_le.mp (ht r)
    omega⟩
  have hdiff : (fun r => ((ell r).val : ℤ) - (k r).val) = t := by
    funext r
    dsimp [ell, k]
    omega
  have h := cubeTranslation_difference_norm_le z P hP hwhite hz hn hL k ell
  rw [hdiff] at h
  exact h

theorem cubeTranslation_conorm_le {d n L : ℕ}
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L)
    (t : Fin d → ℤ) (ht : ∀ r, |t r| ≤ (L : ℤ)) (v : EuclideanSpace ℂ (Fin n)) :
    ‖v‖ ≤ cubeShiftComparisonConstant d n * ‖(cubeTranslation z P t).toEuclideanLin v‖ := by
  have hnz : ∀ j r, z j r ≠ 0 := by
    intro j r h
    have hzr := hz j r
    rw [h, norm_zero] at hzr
    norm_num at hzr
  have hminus := cubeTranslation_norm_le z P hP hwhite hz hn hL (-t)
    (by intro r; simpa only [Pi.neg_apply, abs_neg] using ht r)
  have he : (cubeTranslation z P (-t)).toEuclideanLin
      ((cubeTranslation z P t).toEuclideanLin v) = v := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      cubeTranslation_neg_mul z P hP hnz t]
    simp
  calc
    ‖v‖ = ‖(cubeTranslation z P (-t)).toEuclideanLin ((cubeTranslation z P t).toEuclideanLin v)‖ := by rw [he]
    _ ≤ ‖(cubeTranslation z P (-t)).toEuclideanLin.toContinuousLinearMap‖ *
        ‖(cubeTranslation z P t).toEuclideanLin v‖ :=
      (cubeTranslation z P (-t)).toEuclideanLin.toContinuousLinearMap.le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_right hminus (norm_nonneg _)

theorem naturalCubeTranslation_norm_le {d n L : ℕ}
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L)
    (t : Fin d → ℕ) (ht : ∀ r, t r ≤ L) :
    ‖naturalCubeTranslation z P t‖ ≤ cubeShiftComparisonConstant d n := by
  apply cubeTranslation_norm_le z P hP hwhite hz hn hL
  intro r
  rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ t r)]
  exact_mod_cast ht r

theorem naturalCubeTranslation_conorm_le {d n L : ℕ}
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L)
    (t : Fin d → ℕ) (ht : ∀ r, t r ≤ L) (v : EuclideanSpace ℂ (Fin n)) :
    ‖v‖ ≤ cubeShiftComparisonConstant d n * ‖naturalCubeTranslation z P t v‖ := by
  apply cubeTranslation_conorm_le z P hP hwhite hz hn hL
  intro r
  rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ t r)]
  exact_mod_cast ht r

#print axioms cubeTranslation_difference_norm_le
#print axioms naturalCubeTranslation_conorm_le
#print axioms isotropicCubeRootRow_natural_translation

end
end LeanNumDetect.CubeShiftBounds
