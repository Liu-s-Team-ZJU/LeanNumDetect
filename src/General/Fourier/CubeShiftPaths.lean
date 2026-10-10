import General.Fourier.CubeShiftBounds

/-! Bounded cube paths with both coordinate orientations, and uniform norm
comparison for the concrete whitened cube rows. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators InnerProductSpace
open Matrix WithLp

namespace LeanNumDetect.CubeShiftBounds
noncomputable section

def coordinateDifference {d N : ℕ} (k ell : Fin d → Fin N) (r : Fin d) : Fin N :=
  ⟨if (k r).val ≤ (ell r).val then (ell r).val - (k r).val else (k r).val - (ell r).val, by
    have hk := (k r).isLt
    have hl := (ell r).isLt
    split_ifs <;> omega⟩

def mixedCoordinatePath {d N : ℕ} (length Q : ℕ) (k ell : Fin d → Fin N)
    (t : ℕ) (r : Fin d) : Fin N :=
  let p := coordinatePath length Q (coordinateDifference k ell) t r
  ⟨if (k r).val ≤ (ell r).val then (k r).val + p.val else (k r).val - p.val, by
    have hcap : p.val ≤ (coordinateDifference k ell r).val := Nat.min_le_left _ _
    have hk := (k r).isLt
    have hl := (ell r).isLt
    split_ifs with h
    · simp only [coordinateDifference, if_pos h] at hcap
      omega
    · omega⟩

theorem mixedCoordinatePath_zero {d N : ℕ} (length Q : ℕ) (k ell : Fin d → Fin N) :
    mixedCoordinatePath length Q k ell 0 = k := by
  funext r
  apply Fin.ext
  simp only [mixedCoordinatePath, coordinatePath, Nat.zero_sub, Nat.zero_mul,
    Nat.min_zero, Nat.add_zero, Nat.sub_zero, ite_self]

theorem mixedCoordinatePath_end {d N : ℕ} (length Q : ℕ) (k ell : Fin d → Fin N)
    (hk : ∀ r, (coordinateDifference k ell r).val ≤ length * Q) :
    mixedCoordinatePath length Q k ell (length * d) = ell := by
  have he := coordinatePath_end length Q (coordinateDifference k ell) hk
  funext r
  apply Fin.ext
  have h := congrArg Fin.val (congrFun he r)
  simp only [mixedCoordinatePath]
  rw [h]
  simp only [coordinateDifference]
  split_ifs <;> omega

theorem mixedCoordinatePath_step {d N : ℕ} (length Q : ℕ) (hlength : 0 < length)
    (k ell : Fin d → Fin N)
    (hk : ∀ r, (coordinateDifference k ell r).val ≤ length * Q)
    (t : ℕ) (ht : t < length * d) :
    ∃ r : Fin d, ∃ q : ℕ, q ≤ Q ∧
      ((fun s => (mixedCoordinatePath length Q k ell (t + 1) s).val) =
          Function.update (fun s => (mixedCoordinatePath length Q k ell t s).val) r
            ((mixedCoordinatePath length Q k ell t r).val + q) ∨
        (fun s => (mixedCoordinatePath length Q k ell t s).val) =
          Function.update (fun s => (mixedCoordinatePath length Q k ell (t + 1) s).val) r
            ((mixedCoordinatePath length Q k ell (t + 1) r).val + q)) := by
  obtain ⟨r, q, hq, hstep⟩ := coordinatePath_step length Q hlength
    (coordinateDifference k ell) hk t ht
  have hr : (coordinatePath length Q (coordinateDifference k ell) (t + 1) r).val =
      (coordinatePath length Q (coordinateDifference k ell) t r).val + q := by
    have h := congrFun hstep r
    simpa only [Function.update_self] using h
  have hother : ∀ s, s ≠ r →
      (mixedCoordinatePath length Q k ell (t + 1) s).val =
        (mixedCoordinatePath length Q k ell t s).val := by
    intro s hs
    have h := congrFun hstep s
    rw [Function.update_of_ne hs] at h
    simp only [mixedCoordinatePath]
    rw [h]
  refine ⟨r, q, hq, ?_⟩
  by_cases hdir : (k r).val ≤ (ell r).val
  · left
    funext s
    by_cases hs : s = r
    · subst s
      rw [Function.update_self]
      simp only [mixedCoordinatePath, if_pos hdir]
      omega
    · rw [Function.update_of_ne hs]
      exact hother s hs
  · right
    funext s
    by_cases hs : s = r
    · subst s
      rw [Function.update_self]
      have hcap : (coordinatePath length Q (coordinateDifference k ell) (t + 1) r).val ≤
          (coordinateDifference k ell r).val := Nat.min_le_left _ _
      simp only [coordinateDifference, if_neg hdir] at hcap
      simp only [mixedCoordinatePath, if_neg hdir]
      omega
    · rw [Function.update_of_ne hs]
      exact (hother s hs).symm

theorem coordinateShift_inverseRoots_mul {ι : Type*} [Fintype ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (r : ι) (hz : ∀ j, z j r ≠ 0) (q : ℕ) :
    coordinateShift (fun j s => (z j s)⁻¹) P r q * coordinateShift z P r q = 1 := by
  letI := hP.invertible
  have hd : Matrix.diagonal (fun j => z j r ^ q) *
      Matrix.diagonal (fun j => ((z j r)⁻¹) ^ q) = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Matrix.diagonal_mul_diagonal']
    have h : (fun j => z j r ^ q * ((z j r)⁻¹) ^ q) = fun _ : Fin n => (1 : ℂ) := by
      funext j
      rw [← mul_pow, mul_inv_cancel₀ (hz j), one_pow]
    rw [h]
    exact Matrix.diagonal_one
  unfold coordinateShift
  rw [← Matrix.conjTranspose_mul]
  have hm : coefficientShift z P r q * coefficientShift (fun j s => (z j s)⁻¹) P r q = 1 := by
    unfold coefficientShift
    calc
      _ = P⁻¹ * (Matrix.diagonal (fun j => z j r ^ q) *
          Matrix.diagonal (fun j => ((z j r)⁻¹) ^ q)) * P := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc P P⁻¹,
          Matrix.mul_inv_of_invertible, Matrix.one_mul]
      _ = 1 := by rw [hd]; simp only [Matrix.mul_one, Matrix.inv_mul_of_invertible]
  rw [hm, Matrix.conjTranspose_one]

theorem isotropicCubeRootRow_coordinate_shift_both_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (N : ℕ) (hwhite : Pᴴ * cubeRootGram z N * P = 1)
    (k : ι → ℕ) (r : ι) (hz : ∀ j, ‖z j r‖ = 1) (q : ℕ) (hnq : n * q ≤ N) :
    ‖isotropicCubeRootRow z P N (Function.update k r (k r + q))‖ ≤
        (2 : ℝ) ^ n * ‖isotropicCubeRootRow z P N k‖ ∧
      ‖isotropicCubeRootRow z P N k‖ ≤
        (2 : ℝ) ^ n * ‖isotropicCubeRootRow z P N (Function.update k r (k r + q))‖ := by
  have hnz : ∀ j, z j r ≠ 0 := by
    intro j h
    have ht := hz j
    rw [h, norm_zero] at ht
    norm_num at ht
  have hf := isotropicCubeRootRow_coordinate_shift z P hP N k r q
  have hi : isotropicCubeRootRow z P N k =
      (coordinateShift (fun j s => (z j s)⁻¹) P r q).toEuclideanLin
        (isotropicCubeRootRow z P N (Function.update k r (k r + q))) := by
    rw [hf]
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      coordinateShift_inverseRoots_mul z P hP r hnz q]
    simp
  constructor
  · rw [hf]
    have hnorm := coordinateShift_norm_le z P hP N hwhite r (fun j => (hz j).le) q hnq
    exact ((coordinateShift z P r q).toEuclideanLin.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  · rw [hi]
    have hnorm := coordinateShift_inverseRoots_norm_le z P hP N hwhite r hz q hnq
    exact ((coordinateShift (fun j s => (z j s)⁻¹) P r q).toEuclideanLin.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

theorem norm_path_endpoint_le {E : Type*} [SeminormedAddCommGroup E]
    (v : ℕ → E) {B : ℝ} (hB : 0 ≤ B) (steps : ℕ)
    (hstep : ∀ t, t < steps → ‖v (t + 1)‖ ≤ B * ‖v t‖) :
    ‖v steps‖ ≤ B ^ steps * ‖v 0‖ := by
  induction steps with
  | zero => simp
  | succ steps ih =>
    have hp := ih (fun t ht => hstep t (Nat.lt_trans ht (Nat.lt_succ_self steps)))
    calc
      _ ≤ B * ‖v steps‖ := hstep steps (Nat.lt_succ_self _)
      _ ≤ B * (B ^ steps * ‖v 0‖) := mul_le_mul_of_nonneg_left hp hB
      _ = _ := by rw [pow_succ]; ring

theorem isotropicCubeRootRow_norm_comparison {d n L : ℕ}
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L)
    (k ell : Fin d → Fin (L + 1)) :
    ‖isotropicCubeRootRow z P (L + 1) (fun r => (ell r).val)‖ ≤
      ((2 : ℝ) ^ n) ^ ((4 * n) * d) *
        ‖isotropicCubeRootRow z P (L + 1) (fun r => (k r).val)‖ := by
  let Q := L / (2 * n)
  have hbudget := coarseBudget_of_bandwidth hn hL
  have hcover : ∀ r, (coordinateDifference k ell r).val ≤ (4 * n) * Q := by
    intro r
    have hr := (coordinateDifference k ell r).isLt
    exact (by omega : (coordinateDifference k ell r).val ≤ L).trans hbudget.2.2
  let path := mixedCoordinatePath (4 * n) Q k ell
  let v := fun t => isotropicCubeRootRow z P (L + 1) (fun r => (path t r).val)
  have hstep : ∀ t, t < (4 * n) * d → ‖v (t + 1)‖ ≤ (2 : ℝ) ^ n * ‖v t‖ := by
    intro t ht
    obtain ⟨r, q, hq, hchange⟩ := mixedCoordinatePath_step (4 * n) Q (by omega)
      k ell hcover t ht
    have hnq : n * q ≤ L + 1 :=
      (Nat.mul_le_mul_left n hq).trans hbudget.2.1
    have hb := isotropicCubeRootRow_coordinate_shift_both_norm_le z P hP (L + 1)
      hwhite (fun s => (path t s).val) r (fun j => hz j r) q hnq
    rcases hchange with hplus | hminus
    · dsimp [v]
      change ‖isotropicCubeRootRow z P (L + 1)
        (fun s => (mixedCoordinatePath (4 * n) Q k ell (t + 1) s).val)‖ ≤ _
      rw [hplus]
      exact hb.1
    · have hb' := isotropicCubeRootRow_coordinate_shift_both_norm_le z P hP (L + 1)
        hwhite (fun s => (path (t + 1) s).val) r (fun j => hz j r) q hnq
      dsimp [v]
      change _ ≤ (2 : ℝ) ^ n * ‖isotropicCubeRootRow z P (L + 1)
        (fun s => (mixedCoordinatePath (4 * n) Q k ell t s).val)‖
      rw [hminus]
      exact hb'.2
  have h := norm_path_endpoint_le v (by positivity : (0 : ℝ) ≤ 2 ^ n) ((4 * n) * d) hstep
  dsimp [v, path] at h
  rw [mixedCoordinatePath_zero, mixedCoordinatePath_end _ _ _ _ hcover] at h
  exact h

def cubeShiftComparisonConstant (d n : ℕ) : ℝ := ((2 : ℝ) ^ n) ^ ((4 * n) * d)

theorem isotropicCubeRootRow_norm_sq_sum {d n N : ℕ}
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (hwhite : Pᴴ * cubeRootGram z N * P = 1) :
    (∑ k : Fin d → Fin N, ‖isotropicCubeRootRow z P N (fun r => (k r).val)‖ ^ 2) =
      ((N ^ d : ℕ) : ℝ) * n := by
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  simp_rw [← b.sum_sq_norm_inner_left]
  rw [Finset.sum_comm]
  simp only [isotropicCubeRootRow_parseval z P N hwhite,
    b.orthonormal.norm_eq_one, one_pow, mul_one, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Uniform lower and upper row norm bounds with no minimum-spacing input. -/
theorem isotropicCubeRootRow_norm_bounds {d n L : ℕ}
    (z : Fin n → Fin d → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hwhite : Pᴴ * cubeRootGram z (L + 1) * P = 1)
    (hz : ∀ j r, ‖z j r‖ = 1) (hn : 0 < n) (hL : 2 * n ≤ L)
    (k : Fin d → Fin (L + 1)) :
    Real.sqrt n / cubeShiftComparisonConstant d n ≤
        ‖isotropicCubeRootRow z P (L + 1) (fun r => (k r).val)‖ ∧
      ‖isotropicCubeRootRow z P (L + 1) (fun r => (k r).val)‖ ≤
        cubeShiftComparisonConstant d n * Real.sqrt n := by
  let K := cubeShiftComparisonConstant d n
  let C : ℝ := ((L + 1) ^ d : ℕ)
  let f := fun ell : Fin d → Fin (L + 1) =>
    isotropicCubeRootRow z P (L + 1) (fun r => (ell r).val)
  have hK : 0 < K := by dsimp [K, cubeShiftComparisonConstant]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hcard : Fintype.card (Fin d → Fin (L + 1)) = (L + 1) ^ d := by simp
  have hs : (∑ ell, ‖f ell‖ ^ 2) = C * n := isotropicCubeRootRow_norm_sq_sum z P hwhite
  have hp : ∀ ell, ‖f k‖ ^ 2 ≤ K ^ 2 * ‖f ell‖ ^ 2 := by
    intro ell
    have h := isotropicCubeRootRow_norm_comparison z P hP hwhite hz hn hL ell k
    have hpow := pow_le_pow_left₀ (norm_nonneg _) h 2
    dsimp [f, K, cubeShiftComparisonConstant]
    nlinarith [hpow]
  have hp' : ∀ ell, ‖f ell‖ ^ 2 ≤ K ^ 2 * ‖f k‖ ^ 2 := by
    intro ell
    have h := isotropicCubeRootRow_norm_comparison z P hP hwhite hz hn hL k ell
    have hpow := pow_le_pow_left₀ (norm_nonneg _) h 2
    dsimp [f, K, cubeShiftComparisonConstant]
    nlinarith [hpow]
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun ell _ => hp ell)
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, ← Finset.mul_sum, hs] at hu
  have hu' : C * ‖f k‖ ^ 2 ≤ C * (K ^ 2 * n) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hu
  have husq := (mul_le_mul_iff_right₀ hC).mp hu'
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun ell _ => hp' ell)
  rw [hs, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] at hl
  have hl' : C * (n : ℝ) ≤ C * (K ^ 2 * ‖f k‖ ^ 2) := hl
  have hlsq := (mul_le_mul_iff_right₀ hC).mp hl'
  constructor
  · apply (div_le_iff₀ hK).mpr
    have hnorm : Real.sqrt n ≤ K * ‖f k‖ := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [Real.sq_sqrt (Nat.cast_nonneg _), mul_pow]
      exact hlsq
    simpa only [mul_comm] using hnorm
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact husq

#print axioms isotropicCubeRootRow_norm_comparison
#print axioms isotropicCubeRootRow_norm_bounds

end
end LeanNumDetect.CubeShiftBounds
