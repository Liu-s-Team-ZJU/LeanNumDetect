import General.Fourier.UnitRootRecurrence
import Mathlib.Analysis.InnerProductSpace.PiL2
import General.Probability.RelativeMatrixSampling
import General.MatrixAnalysis.GramPerturbation

/-! Coarse discrete shifts of unit-root exponential sums.  The constants depend
only on the number of roots, and remain valid when roots coincide. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open scoped BigOperators InnerProductSpace
open Matrix WithLp

namespace LeanNumDetect.CubeShiftBounds
noncomputable section

/-- Unnormalized squared energy on a consecutive block of `N` integers. -/
def blockEnergy (f : ℕ → ℂ) (a N : ℕ) : ℝ :=
  ∑ r ∈ Finset.range N, ‖f (a + r)‖ ^ 2

theorem blockEnergy_nonneg (f : ℕ → ℂ) (a N : ℕ) : 0 ≤ blockEnergy f a N := by
  unfold blockEnergy
  positivity

theorem blockEnergy_subblock_le (f : ℕ → ℂ) (a b q N : ℕ) (hbq : b + q ≤ N) :
    blockEnergy f (a + b) q ≤ blockEnergy f a N := by
  have hm : blockEnergy f a (b + q) ≤ blockEnergy f a N := by
    unfold blockEnergy
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hbq)
      (fun _ _ _ => by positivity)
  have he : blockEnergy f a (b + q) = blockEnergy f a b + blockEnergy f (a + b) q := by
    unfold blockEnergy
    rw [Finset.sum_range_add]
    simp only [Nat.add_assoc]
  have hp := blockEnergy_nonneg f a b
  linarith

/-- Scalar samples written as a Euclidean slab vector. -/
def blockVector (f : ℕ → ℂ) (a N : ℕ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun r => f (a + r.val))

@[simp] theorem blockVector_norm_sq (f : ℕ → ℂ) (a N : ℕ) :
    ‖blockVector f a N‖ ^ 2 = blockEnergy f a N := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [blockVector, PiLp.toLp_apply, blockEnergy]
  rw [← Fin.sum_univ_eq_sum_range]

theorem blockVector_norm_le_sqrt (f : ℕ → ℂ) (a b q N : ℕ) (hbq : b + q ≤ N) :
    ‖blockVector f (a + b) q‖ ≤ Real.sqrt (blockEnergy f a N) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [blockVector_norm_sq, Real.sq_sqrt (blockEnergy_nonneg f a N)]
  exact blockEnergy_subblock_le f a b q N hbq

/-- The last slab is controlled by an annihilating recurrence, in its exact
coefficient-mass form. -/
theorem boundaryEnergy_le {n : ℕ} (f : ℕ → ℂ) (c : Fin n → ℂ)
    (a N q : ℕ) (hnq : n * q ≤ N)
    (hrec : ∀ k, f (k + n * q) = -∑ j : Fin n, c j * f (k + j.val * q)) :
    blockEnergy f (a + N) q ≤ (∑ j : Fin n, ‖c j‖) ^ 2 * blockEnergy f a N := by
  let b := N - n * q
  have hb : b + n * q = N := by dsimp [b]; omega
  have hvec : blockVector f (a + N) q =
      -∑ j : Fin n, c j • blockVector f (a + (b + j.val * q)) q := by
    ext r
    simp only [blockVector, ofLp_neg, ofLp_sum, ofLp_smul, PiLp.toLp_apply,
      Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [show a + N + r.val = (a + b + r.val) + n * q by omega, hrec]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    congr 1
    omega
  have hnorm : ‖blockVector f (a + N) q‖ ≤
      (∑ j : Fin n, ‖c j‖) * Real.sqrt (blockEnergy f a N) := by
    rw [hvec, norm_neg]
    calc
      _ ≤ ∑ j : Fin n, ‖c j • blockVector f (a + (b + j.val * q)) q‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, ‖c j‖ * Real.sqrt (blockEnergy f a N) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply blockVector_norm_le_sqrt
        have hj : j.val + 1 ≤ n := by omega
        have hmul := Nat.mul_le_mul_right q hj
        simp only [Nat.add_mul, one_mul] at hmul
        omega
      _ = (∑ j : Fin n, ‖c j‖) * Real.sqrt (blockEnergy f a N) :=
        (Finset.sum_mul _ _ _).symm
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [blockVector_norm_sq, mul_pow,
    Real.sq_sqrt (blockEnergy_nonneg f a N)] at hsquare
  exact hsquare

/-- A coarse shift requires the original block and only one boundary slab. -/
theorem shiftEnergy_le {n : ℕ} (f : ℕ → ℂ) (c : Fin n → ℂ)
    (a N q : ℕ) (hnq : n * q ≤ N)
    (hrec : ∀ k, f (k + n * q) = -∑ j : Fin n, c j * f (k + j.val * q)) :
    blockEnergy f (a + q) N ≤
      (1 + (∑ j : Fin n, ‖c j‖) ^ 2) * blockEnergy f a N := by
  have hsum₁ : blockEnergy f a (q + N) =
      blockEnergy f a q + blockEnergy f (a + q) N := by
    unfold blockEnergy
    rw [Finset.sum_range_add]
    simp only [Nat.add_assoc]
  have hsum₂ : blockEnergy f a (q + N) =
      blockEnergy f a N + blockEnergy f (a + N) q := by
    rw [Nat.add_comm q N]
    unfold blockEnergy
    rw [Finset.sum_range_add]
    simp only [Nat.add_assoc]
  have hboundary := boundaryEnergy_le f c a N q hnq hrec
  have hp := blockEnergy_nonneg f a q
  nlinarith

/-- A discrete exponential sum, allowing repeated unit roots. -/
def unitRootSequence {n : ℕ} (z a : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ j : Fin n, a j * z j ^ k

def coarseRecurrenceCoefficient {n : ℕ} (z : Fin n → ℂ) (q : ℕ) (j : Fin n) : ℂ :=
  (ExponentialCompanion.rootPolynomial (fun i => z i ^ q)).coeff j.val

theorem unitRootSequence_recurrence {n : ℕ} (z a : Fin n → ℂ) (q k : ℕ) :
    unitRootSequence z a (k + n * q) =
      -∑ j : Fin n, coarseRecurrenceCoefficient z q j *
        unitRootSequence z a (k + j.val * q) := by
  have hrec (i : Fin n) := ExponentialCompanion.rootPolynomial_recurrence
    (fun i => z i ^ q) i
  unfold unitRootSequence coarseRecurrenceCoefficient
  simp_rw [pow_add, Nat.mul_comm _ q, pow_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he : ∑ j : Fin n,
      (ExponentialCompanion.rootPolynomial (fun i => z i ^ q)).coeff j.val *
        (a i * (z i ^ k * (z i ^ q) ^ j.val)) =
      a i * z i ^ k *
        (∑ j : Fin n,
          (ExponentialCompanion.rootPolynomial (fun i => z i ^ q)).coeff j.val *
            (z i ^ q) ^ j.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, hrec]
  ring

theorem coarseRecurrenceCoefficient_mass_le {n : ℕ} (z : Fin n → ℂ) (q : ℕ)
    (hz : ∀ j, ‖z j‖ ≤ 1) :
    ∑ j : Fin n, ‖coarseRecurrenceCoefficient z q j‖ ≤ (2 : ℝ) ^ n - 1 := by
  have hfreq : ‖fun j => z j ^ q‖ ≤ (1 : ℝ) := by
    apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
    intro j
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (hz j) q).trans_eq (one_pow q)
  simpa only [coarseRecurrenceCoefficient, one_add_one_eq_two] using
    UnitRootRecurrence.rootPolynomial_lower_coefficient_mass_le
      (fun j => z j ^ q) (by norm_num : (0 : ℝ) ≤ 1) hfreq

/-- The coarse coordinate energy estimate, independent of root spacing. -/
theorem unitRootSequence_shiftEnergy_le {n : ℕ} (z a : Fin n → ℂ)
    (hz : ∀ j, ‖z j‖ ≤ 1) (offset N q : ℕ) (hnq : n * q ≤ N) :
    blockEnergy (unitRootSequence z a) (offset + q) N ≤
      ((2 : ℝ) ^ n) ^ 2 * blockEnergy (unitRootSequence z a) offset N := by
  have hshift := shiftEnergy_le (unitRootSequence z a) (coarseRecurrenceCoefficient z q)
    offset N q hnq (unitRootSequence_recurrence z a q)
  have hmass := coarseRecurrenceCoefficient_mass_le z q hz
  have hmass0 : 0 ≤ ∑ j : Fin n, ‖coarseRecurrenceCoefficient z q j‖ := by positivity
  have htwo : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hbudget : 1 + (∑ j : Fin n, ‖coarseRecurrenceCoefficient z q j‖) ^ 2 ≤
      ((2 : ℝ) ^ n) ^ 2 := by nlinarith
  exact hshift.trans (mul_le_mul_of_nonneg_right hbudget
    (blockEnergy_nonneg _ _ _))

theorem unitRootSequence_modulation {n : ℕ} (z a : Fin n → ℂ) (q k : ℕ) :
    unitRootSequence z (fun j => a j * z j ^ q) k = unitRootSequence z a (k + q) := by
  unfold unitRootSequence
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

theorem unitRootSequence_blockEnergy_modulation {n : ℕ} (z a : Fin n → ℂ)
    (offset N q : ℕ) :
    blockEnergy (unitRootSequence z (fun j => a j * z j ^ q)) offset N =
      blockEnergy (unitRootSequence z a) (offset + q) N := by
  unfold blockEnergy
  apply Finset.sum_congr rfl
  intro k _
  rw [unitRootSequence_modulation,
    show offset + k + q = offset + q + k by omega]

theorem unitRootSequence_reverse {n : ℕ} (z a : Fin n → ℂ)
    (hz : ∀ j, z j ≠ 0) (L k : ℕ) (hk : k ≤ L) :
    unitRootSequence (fun j => (z j)⁻¹) (fun j => a j * z j ^ L) k =
      unitRootSequence z a (L - k) := by
  unfold unitRootSequence
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_sub₀ (z j) (hz j) hk, inv_pow]
  ring

theorem unitRootSequence_blockEnergy_inverse_reverse {n : ℕ} (z a : Fin n → ℂ)
    (hz : ∀ j, z j ≠ 0) (N : ℕ) :
    blockEnergy (unitRootSequence (fun j => (z j)⁻¹)
      (fun j => a j * z j ^ (N - 1))) 0 N =
        blockEnergy (unitRootSequence z a) 0 N := by
  unfold blockEnergy
  simp only [Nat.zero_add]
  calc
    _ = ∑ k ∈ Finset.range N, ‖unitRootSequence z a (N - 1 - k)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [unitRootSequence_reverse z a hz (N - 1) k (by
        have h := Finset.mem_range.mp hk
        omega)]
    _ = _ := Finset.sum_range_reflect (fun k => ‖unitRootSequence z a k‖ ^ 2) N

/-- Inverse coarse modulation has the same norm bound for unit roots. -/
theorem unitRootSequence_inverse_modulationEnergy_le {n : ℕ} (z a : Fin n → ℂ)
    (hz : ∀ j, ‖z j‖ = 1) (N q : ℕ) (hnq : n * q ≤ N) :
    blockEnergy (unitRootSequence z (fun j => a j * ((z j)⁻¹) ^ q)) 0 N ≤
      ((2 : ℝ) ^ n) ^ 2 * blockEnergy (unitRootSequence z a) 0 N := by
  have hnz : ∀ j, z j ≠ 0 := by
    intro j h
    have ht := hz j
    rw [h, norm_zero] at ht
    norm_num at ht
  let b : Fin n → ℂ := fun j => a j * z j ^ (N - 1)
  have hzinv : ∀ j, ‖(z j)⁻¹‖ ≤ (1 : ℝ) := by
    intro j
    simp only [norm_inv, hz j, inv_one, le_refl]
  have h := unitRootSequence_shiftEnergy_le (fun j => (z j)⁻¹) b hzinv 0 N q hnq
  have hcoeff : (fun j => b j * ((z j)⁻¹) ^ q) =
      fun j => (a j * ((z j)⁻¹) ^ q) * z j ^ (N - 1) := by
    funext j
    dsimp [b]
    ring
  rw [← unitRootSequence_blockEnergy_modulation (fun j => (z j)⁻¹) b 0 N q,
    hcoeff, unitRootSequence_blockEnergy_inverse_reverse z _ hnz N] at h
  dsimp [b] at h
  rw [unitRootSequence_blockEnergy_inverse_reverse z a hnz N] at h
  exact h

/-- Tensor unit-root sum on an integer cube. -/
def cubeRootSum {ι : Type*} [Fintype ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (a : Fin n → ℂ) (k : ι → ℕ) : ℂ :=
  ∑ j : Fin n, a j * ∏ r : ι, z j r ^ k r

def cubeRootEnergy {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (a : Fin n → ℂ) (N : ℕ) : ℝ :=
  ∑ k : ι → Fin N, ‖cubeRootSum z a (fun r => (k r).val)‖ ^ 2

def fiberCoefficient {ι : Type*} [Fintype ι] [DecidableEq ι] {n N : ℕ}
    (z : Fin n → ι → ℂ) (a : Fin n → ℂ) (r : ι)
    (ν : {s : ι // s ≠ r} → Fin N) (j : Fin n) : ℂ :=
  a j * ∏ s : {s : ι // s ≠ r}, z j s.val ^ (ν s).val

theorem cubeRootSum_split {ι : Type*} [Fintype ι] [DecidableEq ι] {n N : ℕ}
    (z : Fin n → ι → ℂ) (a : Fin n → ℂ) (r : ι)
    (ν : {s : ι // s ≠ r} → Fin N) (k : Fin N) :
    cubeRootSum z a (fun s => (((Equiv.funSplitAt r (Fin N)).symm (k, ν)) s).val) =
      unitRootSequence (fun j => z j r) (fiberCoefficient z a r ν) k.val := by
  unfold cubeRootSum unitRootSequence fiberCoefficient
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ r]
  dsimp only
  have hr : ((Equiv.funSplitAt r (Fin N)).symm (k, ν)) r = k := by
    simp only [Equiv.funSplitAt_symm_apply, dif_pos rfl]
    simp
  have hs : ∀ s : {s : ι // s ≠ r},
      ((Equiv.funSplitAt r (Fin N)).symm (k, ν)) s.val = ν s := by
    intro s
    simp only [Equiv.funSplitAt_symm_apply, dif_neg s.property]
  rw [hr]
  simp_rw [hs]
  ring

theorem cubeRootEnergy_eq_fiberEnergy {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (a : Fin n → ℂ) (N : ℕ) (r : ι) :
    cubeRootEnergy z a N =
      ∑ ν : {s : ι // s ≠ r} → Fin N,
        blockEnergy (unitRootSequence (fun j => z j r) (fiberCoefficient z a r ν)) 0 N := by
  unfold cubeRootEnergy
  rw [← (Equiv.funSplitAt r (Fin N)).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  simp only [cubeRootSum_split, blockEnergy, Nat.zero_add]
  rw [← Fin.sum_univ_eq_sum_range]

theorem fiberCoefficient_modulation {ι : Type*} [Fintype ι] [DecidableEq ι] {n N : ℕ}
    (z : Fin n → ι → ℂ) (a : Fin n → ℂ) (r : ι)
    (ν : {s : ι // s ≠ r} → Fin N) (q : ℕ) :
    fiberCoefficient z (fun j => a j * z j r ^ q) r ν =
      fun j => fiberCoefficient z a r ν j * z j r ^ q := by
  funext j
  unfold fiberCoefficient
  ring

/-- Coarse coordinate modulation on a full cube costs at most `2^n` in
norm, uniformly over every unit-root configuration. -/
theorem cubeRootEnergy_coordinate_modulation_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (z : Fin n → ι → ℂ) (a : Fin n → ℂ) (r : ι)
    (hz : ∀ j, ‖z j r‖ ≤ 1) (N q : ℕ) (hnq : n * q ≤ N) :
    cubeRootEnergy z (fun j => a j * z j r ^ q) N ≤
      ((2 : ℝ) ^ n) ^ 2 * cubeRootEnergy z a N := by
  rw [cubeRootEnergy_eq_fiberEnergy z _ N r, cubeRootEnergy_eq_fiberEnergy z a N r,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ν _
  rw [fiberCoefficient_modulation]
  have h := unitRootSequence_shiftEnergy_le (fun j => z j r) (fiberCoefficient z a r ν)
    hz 0 N q hnq
  rw [← unitRootSequence_blockEnergy_modulation (fun j => z j r)
    (fiberCoefficient z a r ν) 0 N q] at h
  exact h

theorem cubeRootEnergy_coordinate_inverse_modulation_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (z : Fin n → ι → ℂ) (a : Fin n → ℂ) (r : ι)
    (hz : ∀ j, ‖z j r‖ = 1) (N q : ℕ) (hnq : n * q ≤ N) :
    cubeRootEnergy z (fun j => a j * ((z j r)⁻¹) ^ q) N ≤
      ((2 : ℝ) ^ n) ^ 2 * cubeRootEnergy z a N := by
  rw [cubeRootEnergy_eq_fiberEnergy z _ N r, cubeRootEnergy_eq_fiberEnergy z a N r,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ν _
  have hcoeff : fiberCoefficient z (fun j => a j * ((z j r)⁻¹) ^ q) r ν =
      fun j => fiberCoefficient z a r ν j * ((z j r)⁻¹) ^ q := by
    funext j
    unfold fiberCoefficient
    ring
  rw [hcoeff]
  exact unitRootSequence_inverse_modulationEnergy_le (fun j => z j r)
    (fiberCoefficient z a r ν) hz N q hnq

/-- The unnormalized tensor cube matrix and its full Gram matrix. -/
def cubeRootMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (N : ℕ) : Matrix (ι → Fin N) (Fin n) ℂ :=
  fun k j => ∏ r : ι, z j r ^ (k r).val

def cubeRootGram {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (N : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (cubeRootMatrix z N)ᴴ * cubeRootMatrix z N

theorem cubeRootEnergy_eq_matrixNorm {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (N : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    cubeRootEnergy z v.ofLp N = ‖(cubeRootMatrix z N).toEuclideanLin v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Matrix.toLpLin_apply]
  simp only [cubeRootEnergy, cubeRootSum, cubeRootMatrix, Matrix.mulVec,
    dotProduct, PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem cubeRootEnergy_eq_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (N : ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    cubeRootEnergy z v.ofLp N = FiniteMatrixSampling.quadratic (cubeRootGram z N) v := by
  rw [cubeRootEnergy_eq_matrixNorm, matrix_norm_sq_eq_re_inner_gram]
  rfl

theorem cubeRootEnergy_whitened {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (N : ℕ) (P : Matrix (Fin n) (Fin n) ℂ)
    (hwhite : Pᴴ * cubeRootGram z N * P = 1) (v : EuclideanSpace ℂ (Fin n)) :
    cubeRootEnergy z (P.toEuclideanLin v).ofLp N = ‖v‖ ^ 2 := by
  rw [cubeRootEnergy_eq_quadratic, ← FiniteMatrixSampling.quadratic_congruence,
    hwhite, FiniteMatrixSampling.quadratic_identity]

/-- The adjoint of the row translation, in whitened coefficient coordinates. -/
def coefficientShift {ι : Type*} [Fintype ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (r : ι) (q : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  P⁻¹ * Matrix.diagonal (fun j => z j r ^ q) * P

def coordinateShift {ι : Type*} [Fintype ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (r : ι) (q : ℕ) :
    Matrix (Fin n) (Fin n) ℂ := (coefficientShift z P r q)ᴴ

theorem coefficientShift_intertwining {ι : Type*} [Fintype ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (r : ι) (q : ℕ) :
    P * coefficientShift z P r q = Matrix.diagonal (fun j => z j r ^ q) * P := by
  letI := hP.invertible
  simp only [coefficientShift, ← Matrix.mul_assoc, Matrix.mul_inv_of_invertible,
    Matrix.one_mul]

theorem coefficientShift_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (N : ℕ) (hwhite : Pᴴ * cubeRootGram z N * P = 1) (r : ι)
    (hz : ∀ j, ‖z j r‖ ≤ 1) (q : ℕ) (hnq : n * q ≤ N) :
    ‖(coefficientShift z P r q).toEuclideanLin.toContinuousLinearMap‖ ≤ (2 : ℝ) ^ n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖(coefficientShift z P r q).toEuclideanLin v‖ ≤ (2 : ℝ) ^ n * ‖v‖
  have h := cubeRootEnergy_coordinate_modulation_le z (P.toEuclideanLin v).ofLp r hz N q hnq
  have he : (P.toEuclideanLin ((coefficientShift z P r q).toEuclideanLin v)).ofLp =
      fun j => (P.toEuclideanLin v).ofLp j * z j r ^ q := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      coefficientShift_intertwining z P hP r q, Matrix.toLpLin_mul_same]
    simp only [LinearMap.comp_apply, Matrix.toLpLin_apply, Matrix.mulVec_diagonal,
      PiLp.toLp_apply]
    funext j
    rw [Matrix.mulVec_diagonal]
    ring
  rw [← he, cubeRootEnergy_whitened z N P hwhite,
    cubeRootEnergy_whitened z N P hwhite] at h
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith [h]

theorem matrixEuclidean_opNorm_conjTranspose_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖Aᴴ.toEuclideanLin.toContinuousLinearMap‖ = ‖A.toEuclideanLin.toContinuousLinearMap‖ := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem coordinateShift_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (N : ℕ) (hwhite : Pᴴ * cubeRootGram z N * P = 1) (r : ι)
    (hz : ∀ j, ‖z j r‖ ≤ 1) (q : ℕ) (hnq : n * q ≤ N) :
    ‖(coordinateShift z P r q).toEuclideanLin.toContinuousLinearMap‖ ≤ (2 : ℝ) ^ n := by
  rw [coordinateShift, matrixEuclidean_opNorm_conjTranspose_eq]
  exact coefficientShift_norm_le z P hP N hwhite r hz q hnq

theorem coefficientShift_inverseRoots_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (N : ℕ) (hwhite : Pᴴ * cubeRootGram z N * P = 1) (r : ι)
    (hz : ∀ j, ‖z j r‖ = 1) (q : ℕ) (hnq : n * q ≤ N) :
    ‖(coefficientShift (fun j s => (z j s)⁻¹) P r q).toEuclideanLin.toContinuousLinearMap‖ ≤
      (2 : ℝ) ^ n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖(coefficientShift (fun j s => (z j s)⁻¹) P r q).toEuclideanLin v‖ ≤
    (2 : ℝ) ^ n * ‖v‖
  have h := cubeRootEnergy_coordinate_inverse_modulation_le z (P.toEuclideanLin v).ofLp r hz N q hnq
  have he : (P.toEuclideanLin
      ((coefficientShift (fun j s => (z j s)⁻¹) P r q).toEuclideanLin v)).ofLp =
      fun j => (P.toEuclideanLin v).ofLp j * ((z j r)⁻¹) ^ q := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      coefficientShift_intertwining (fun j s => (z j s)⁻¹) P hP r q,
      Matrix.toLpLin_mul_same]
    simp only [LinearMap.comp_apply, Matrix.toLpLin_apply, PiLp.toLp_apply]
    funext j
    rw [Matrix.mulVec_diagonal]
    ring
  rw [← he, cubeRootEnergy_whitened z N P hwhite,
    cubeRootEnergy_whitened z N P hwhite] at h
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith [h]

theorem coordinateShift_inverseRoots_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (N : ℕ) (hwhite : Pᴴ * cubeRootGram z N * P = 1) (r : ι)
    (hz : ∀ j, ‖z j r‖ = 1) (q : ℕ) (hnq : n * q ≤ N) :
    ‖(coordinateShift (fun j s => (z j s)⁻¹) P r q).toEuclideanLin.toContinuousLinearMap‖ ≤
      (2 : ℝ) ^ n := by
  rw [coordinateShift, matrixEuclidean_opNorm_conjTranspose_eq]
  exact coefficientShift_inverseRoots_norm_le z P hP N hwhite r hz q hnq

def rawCubeRootRow {ι : Type*} [Fintype ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (k : ι → ℕ) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun j => star (∏ r : ι, z j r ^ k r))

def whitenedCubeRootRow {ι : Type*} [Fintype ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (k : ι → ℕ) :
    EuclideanSpace ℂ (Fin n) := Pᴴ.toEuclideanLin (rawCubeRootRow z k)

theorem rootProduct_coordinate_shift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℂ) (k : ι → ℕ) (r : ι) (q : ℕ) :
    (∏ s : ι, z s ^ (Function.update k r (k r + q)) s) =
      (∏ s : ι, z s ^ k s) * z r ^ q := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ r,
    Fintype.prod_eq_mul_prod_subtype_ne (fun s => z s ^ k s) r]
  have hs : ∀ s : {s : ι // s ≠ r}, (Function.update k r (k r + q)) s.val = k s.val := by
    intro s
    simp only [Function.update_of_ne s.property]
  simp only [Function.update_self]
  simp_rw [hs]
  rw [pow_add]
  ring

theorem rawCubeRootRow_coordinate_shift {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (k : ι → ℕ) (r : ι) (q : ℕ) :
    rawCubeRootRow z (Function.update k r (k r + q)) =
      (Matrix.diagonal (fun j => z j r ^ q))ᴴ.toEuclideanLin (rawCubeRootRow z k) := by
  rw [Matrix.diagonal_conjTranspose, Matrix.toLpLin_apply]
  ext j
  simp only [rawCubeRootRow, PiLp.toLp_apply]
  rw [Matrix.mulVec_diagonal, rootProduct_coordinate_shift, star_mul]
  simp only [Pi.star_apply]

theorem whitenedCubeRootRow_coordinate_shift {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (k : ι → ℕ) (r : ι) (q : ℕ) :
    whitenedCubeRootRow z P (Function.update k r (k r + q)) =
      (coordinateShift z P r q).toEuclideanLin (whitenedCubeRootRow z P k) := by
  have hm : coordinateShift z P r q * Pᴴ =
      Pᴴ * (Matrix.diagonal (fun j => z j r ^ q))ᴴ := by
    have h := congrArg Matrix.conjTranspose (coefficientShift_intertwining z P hP r q)
    simpa only [Matrix.conjTranspose_mul, coordinateShift] using h
  unfold whitenedCubeRootRow
  rw [rawCubeRootRow_coordinate_shift]
  change (Pᴴ.toEuclideanLin ∘ₗ (Matrix.diagonal (fun j => z j r ^ q))ᴴ.toEuclideanLin)
      (rawCubeRootRow z k) =
    ((coordinateShift z P r q).toEuclideanLin ∘ₗ Pᴴ.toEuclideanLin) (rawCubeRootRow z k)
  rw [← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, hm]

theorem inner_whitenedCubeRootRow {ι : Type*} [Fintype ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (k : ι → ℕ) (v : EuclideanSpace ℂ (Fin n)) :
    ⟪whitenedCubeRootRow z P k, v⟫_ℂ = cubeRootSum z (P.toEuclideanLin v).ofLp k := by
  rw [whitenedCubeRootRow, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_left, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [rawCubeRootRow, PiLp.toLp_apply, Pi.star_apply, star_star, dotProduct, cubeRootSum]

theorem whitenedCubeRootRow_parseval {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (N : ℕ)
    (hwhite : Pᴴ * cubeRootGram z N * P = 1) (v : EuclideanSpace ℂ (Fin n)) :
    (∑ k : ι → Fin N, ‖⟪whitenedCubeRootRow z P (fun r => (k r).val), v⟫_ℂ‖ ^ 2) =
      ‖v‖ ^ 2 := by
  simp only [inner_whitenedCubeRootRow]
  exact cubeRootEnergy_whitened z N P hwhite v

/-- Rows scaled to have identity mean Gram rather than identity Gram sum. -/
def isotropicCubeRootRow {ι : Type*} [Fintype ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (N : ℕ)
    (k : ι → ℕ) : EuclideanSpace ℂ (Fin n) :=
  (Real.sqrt ((N ^ Fintype.card ι : ℕ) : ℝ) : ℂ) • whitenedCubeRootRow z P k

theorem isotropicCubeRootRow_parseval {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (N : ℕ)
    (hwhite : Pᴴ * cubeRootGram z N * P = 1) (v : EuclideanSpace ℂ (Fin n)) :
    (∑ k : ι → Fin N, ‖⟪isotropicCubeRootRow z P N (fun r => (k r).val), v⟫_ℂ‖ ^ 2) =
      ((N ^ Fintype.card ι : ℕ) : ℝ) * ‖v‖ ^ 2 := by
  simp only [isotropicCubeRootRow, inner_smul_left, norm_mul, Complex.conj_ofReal,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), ← Finset.mul_sum]
  rw [whitenedCubeRootRow_parseval z P N hwhite v]

theorem isotropicCubeRootRow_coordinate_shift {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (z : Fin n → ι → ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (N : ℕ) (k : ι → ℕ) (r : ι) (q : ℕ) :
    isotropicCubeRootRow z P N (Function.update k r (k r + q)) =
      (coordinateShift z P r q).toEuclideanLin (isotropicCubeRootRow z P N k) := by
  unfold isotropicCubeRootRow
  rw [whitenedCubeRootRow_coordinate_shift z P hP k r q, map_smul]

/-- A positive coordinate path with a fixed number of steps per coordinate.
Steps that finish early have length zero. -/
def coordinatePath {d N : ℕ} (length Q : ℕ) (k : Fin d → Fin N)
    (t : ℕ) (r : Fin d) : Fin N :=
  ⟨min (k r).val ((t - r.val * length) * Q),
    lt_of_le_of_lt (Nat.min_le_left _ _) (k r).isLt⟩

theorem coordinatePath_zero {d N : ℕ} (length Q : ℕ) (k : Fin d → Fin N) (hN : 0 < N) :
    coordinatePath length Q k 0 = fun _ => ⟨0, hN⟩ := by
  funext r
  apply Fin.ext
  simp only [coordinatePath, Nat.zero_sub, Nat.zero_mul, Nat.min_zero]

/-- The endpoint identity only uses the coverage of every coordinate. -/
theorem coordinatePath_end {d N : ℕ} (length Q : ℕ) (k : Fin d → Fin N)
    (hk : ∀ r, (k r).val ≤ length * Q) :
    coordinatePath length Q k (length * d) = k := by
  funext r
  apply Fin.ext
  change min (k r).val (((length * d) - r.val * length) * Q) = (k r).val
  have hr : r.val + 1 ≤ d := by omega
  have hmul := Nat.mul_le_mul_right length hr
  simp only [Nat.add_mul, one_mul] at hmul
  have hdiff : length ≤ length * d - r.val * length := by
    rw [Nat.mul_comm length d]
    omega
  exact Nat.min_eq_left ((hk r).trans (Nat.mul_le_mul_right Q hdiff))

theorem coordinatePath_step {d N : ℕ} (length Q : ℕ) (hlength : 0 < length)
    (k : Fin d → Fin N) (hk : ∀ r, (k r).val ≤ length * Q)
    (t : ℕ) (ht : t < length * d) :
    ∃ r : Fin d, ∃ q : ℕ, q ≤ Q ∧
      (fun s => (coordinatePath length Q k (t + 1) s).val) =
        Function.update (fun s => (coordinatePath length Q k t s).val) r
          ((coordinatePath length Q k t r).val + q) := by
  let m := t / length
  have hmlo : m * length ≤ t := Nat.div_mul_le_self _ _
  have hmhi : t < (m + 1) * length := by
    simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ t hlength
  have hm : m < d := by
    have hdiv : t / length < d := (Nat.div_lt_iff_lt_mul hlength).mpr
      (by simpa only [Nat.mul_comm] using ht)
    exact hdiv
  let r : Fin d := ⟨m, hm⟩
  have hnewdiff : t + 1 - r.val * length = (t - r.val * length) + 1 := by
    change t + 1 - m * length = (t - m * length) + 1
    omega
  have hnew : (coordinatePath length Q k (t + 1) r).val =
      min (k r).val (((t - r.val * length) * Q) + Q) := by
    simp only [coordinatePath, hnewdiff, Nat.add_mul, one_mul]
  have hcur : (coordinatePath length Q k t r).val =
      min (k r).val ((t - r.val * length) * Q) := rfl
  have hinc : (coordinatePath length Q k t r).val ≤
      (coordinatePath length Q k (t + 1) r).val := by rw [hcur, hnew]; omega
  have hincupper : (coordinatePath length Q k (t + 1) r).val ≤
      (coordinatePath length Q k t r).val + Q := by rw [hcur, hnew]; omega
  let q := (coordinatePath length Q k (t + 1) r).val -
    (coordinatePath length Q k t r).val
  have hq : q ≤ Q := by dsimp [q]; omega
  have hval : (coordinatePath length Q k (t + 1) r).val =
      (coordinatePath length Q k t r).val + q := by dsimp [q]; omega
  refine ⟨r, q, hq, ?_⟩
  funext s
  by_cases hs : s = r
  · subst s
    rw [Function.update_self]
    exact hval
  · rw [Function.update_of_ne hs]
    have hne : s.val ≠ m := fun h => hs (Fin.ext h)
    by_cases hpre : s.val < m
    · have hslen := Nat.mul_le_mul_right length (Nat.succ_le_iff.mpr hpre)
      simp only [Nat.succ_mul] at hslen
      have hdiff : length ≤ t - s.val * length := by omega
      have hdiff' : length ≤ t + 1 - s.val * length := by omega
      have hcap : (k s).val ≤ (t - s.val * length) * Q :=
        (hk s).trans (Nat.mul_le_mul_right Q hdiff)
      have hcap' : (k s).val ≤ (t + 1 - s.val * length) * Q :=
        (hk s).trans (Nat.mul_le_mul_right Q hdiff')
      simp only [coordinatePath, Nat.min_eq_left hcap, Nat.min_eq_left hcap']
    · have hpost : m + 1 ≤ s.val := by omega
      have hslen := Nat.mul_le_mul_right length hpost
      have hdiff : t - s.val * length = 0 := by omega
      have hdiff' : t + 1 - s.val * length = 0 := by omega
      simp only [coordinatePath, hdiff, hdiff', Nat.zero_mul, Nat.min_zero]

/-- The bandwidth already required by Li supplies all coarse path budgets. -/
theorem coarseBudget_of_bandwidth {n L : ℕ} (hn : 0 < n) (hL : 2 * n ≤ L) :
    0 < L / (2 * n) ∧ n * (L / (2 * n)) ≤ L + 1 ∧
      L ≤ (4 * n) * (L / (2 * n)) := by
  let Q := L / (2 * n)
  have hden : 0 < 2 * n := by omega
  have hQ : 1 ≤ Q := (Nat.le_div_iff_mul_le hden).mpr (by omega)
  have hmul : Q * (2 * n) ≤ L := Nat.div_mul_le_self _ _
  have hlt : L < (2 * n) * (Q + 1) := by
    exact Nat.lt_mul_div_succ _ hden
  dsimp [Q] at hQ hmul hlt
  refine ⟨by omega, ?_, ?_⟩ <;> nlinarith

theorem coarseBudget_of_liBandwidth {n L : ℕ} (hn : 0 < n) (hL : 8 * n ≤ L) :
    0 < L / (2 * n) ∧ n * (L / (2 * n)) ≤ L + 1 ∧
      L ≤ (4 * n) * (L / (2 * n)) :=
  coarseBudget_of_bandwidth hn (by omega)

#print axioms unitRootSequence_shiftEnergy_le
#print axioms cubeRootEnergy_coordinate_modulation_le
#print axioms cubeRootEnergy_coordinate_inverse_modulation_le
#print axioms coordinateShift_norm_le
#print axioms coordinateShift_inverseRoots_norm_le
#print axioms whitenedCubeRootRow_coordinate_shift
#print axioms coordinatePath_step
#print axioms coarseBudget_of_liBandwidth
#print axioms isotropicCubeRootRow_parseval

end
end LeanNumDetect.CubeShiftBounds
