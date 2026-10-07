import General.Probability.FiniteBernoulliContraction
import General.Probability.BoundedRowEstimates

/-!
# Separable clipped quadratics

Clipping the real and imaginary squares separately preserves every energy
below the clipping radius and permits scalar Bernoulli contraction. The
lemmas here give the deterministic Lipschitz and envelope estimates without
assuming any concentration or empirical-process theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open LeanNumDetect.FiniteMatrixSampling

namespace LeanNumDetect.BoundedRieszConcentration

/-- A scalar square clipped at the squared amplitude radius. -/
noncomputable def clippedRealSquare (R x : ℝ) : ℝ := min (x ^ 2) (R ^ 2)

theorem clippedRealSquare_nonneg (R x : ℝ) : 0 ≤ clippedRealSquare R x :=
  le_min (sq_nonneg _) (sq_nonneg _)

theorem clippedRealSquare_le_square (R x : ℝ) : clippedRealSquare R x ≤ x ^ 2 :=
  min_le_left _ _

theorem clippedRealSquare_le_radius (R x : ℝ) : clippedRealSquare R x ≤ R ^ 2 :=
  min_le_right _ _

@[simp] theorem clippedRealSquare_zero (R : ℝ) : clippedRealSquare R 0 = 0 := by
  simp [clippedRealSquare, sq_nonneg]

theorem clippedRealSquare_eq_square {R x : ℝ} (hx : |x| ≤ R) :
    clippedRealSquare R x = x ^ 2 := by
  have hR : 0 ≤ R := (abs_nonneg x).trans hx
  have hsq := mul_le_mul hx hx (abs_nonneg _) hR
  simpa [clippedRealSquare, min_eq_left, ← sq, sq_abs] using hsq

theorem clippedRealSquare_eq_min_abs_square {R x : ℝ} (hR : 0 ≤ R) :
    clippedRealSquare R x = (min |x| R) ^ 2 := by
  rcases le_total |x| R with h | h
  · rw [min_eq_left h, clippedRealSquare_eq_square h, sq_abs]
  · rw [min_eq_right h]
    have hsq := mul_le_mul h h hR (abs_nonneg _)
    simp only [← sq, sq_abs] at hsq
    exact min_eq_right hsq

/-- The scalar clipped square is globally `2R`-Lipschitz. -/
theorem clippedRealSquare_lipschitz {R : ℝ} (hR : 0 ≤ R) (x y : ℝ) :
    |clippedRealSquare R x - clippedRealSquare R y| ≤ 2 * R * |x - y| := by
  rw [clippedRealSquare_eq_min_abs_square hR, clippedRealSquare_eq_min_abs_square hR]
  let a := min |x| R
  let b := min |y| R
  have ha : 0 ≤ a := le_min (abs_nonneg _) hR
  have hb : 0 ≤ b := le_min (abs_nonneg _) hR
  have haR : a ≤ R := min_le_right _ _
  have hbR : b ≤ R := min_le_right _ _
  have hdiff : |a - b| ≤ |x - y| := by
    have h := abs_min_sub_min_le_max |x| R |y| R
    simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (|x| - |y|))] at h
    exact h.trans (abs_abs_sub_abs_le_abs_sub x y)
  calc
    |a ^ 2 - b ^ 2| = |a - b| * (a + b) := by
      rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul,
        abs_of_nonneg (add_nonneg ha hb)]
    _ ≤ |x - y| * (2 * R) := mul_le_mul hdiff (by linarith) (add_nonneg ha hb) (abs_nonneg _)
    _ = _ := by ring

/-- Separable clipping of the two real coordinates of a complex energy. -/
noncomputable def clippedComplexEnergy (R : ℝ) (z : ℂ) : ℝ :=
  clippedRealSquare R z.re + clippedRealSquare R z.im

theorem clippedComplexEnergy_nonneg (R : ℝ) (z : ℂ) : 0 ≤ clippedComplexEnergy R z :=
  add_nonneg (clippedRealSquare_nonneg _ _) (clippedRealSquare_nonneg _ _)

theorem clippedComplexEnergy_le_radius (R : ℝ) (z : ℂ) :
    clippedComplexEnergy R z ≤ 2 * R ^ 2 := by
  unfold clippedComplexEnergy
  linarith [clippedRealSquare_le_radius R z.re, clippedRealSquare_le_radius R z.im]

theorem clippedComplexEnergy_le_energy (R : ℝ) (z : ℂ) :
    clippedComplexEnergy R z ≤ ‖z‖ ^ 2 := by
  unfold clippedComplexEnergy
  have h := add_le_add (clippedRealSquare_le_square R z.re) (clippedRealSquare_le_square R z.im)
  rw [Complex.sq_norm, Complex.normSq_apply]
  simpa only [pow_two] using h

theorem clippedComplexEnergy_eq_energy {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) :
    clippedComplexEnergy R z = ‖z‖ ^ 2 := by
  have hre : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hz
  have him : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hz
  rw [clippedComplexEnergy, clippedRealSquare_eq_square hre,
    clippedRealSquare_eq_square him, Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]

@[simp] theorem clippedComplexEnergy_zero (R : ℝ) : clippedComplexEnergy R 0 = 0 := by
  simp [clippedComplexEnergy]

theorem rowPairing_sum_right_real_smul {N m : ℕ} (f : ComplexVector N)
    (rows : Fin m → ComplexVector N) (r : Fin m → ℝ) :
    rowPairing f (∑ i, (r i : ℂ) • rows i) = ∑ i, r i • rowPairing f (rows i) := by
  simp only [rowPairing, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Complex.real_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The expected absolute real projection of the masked linear process
has a row-count square root and only a logarithmic column-count factor.
The coefficient index class may be infinite. -/
theorem masked_linear_bernoulli_supremum_expectation_le
    {N m : ℕ} (hN : 0 < N) {T : Type*} [Nonempty T]
    (f : T → ComplexVector N) (rows : Fin m → ComplexVector N)
    (E : Finset (Fin m)) {s K : ℝ}
    (hf : ∀ t, coefficientL1Norm (f t) ≤ Real.sqrt s)
    (hrows : ∀ i j, ‖rows i j‖ ≤ K)
    (π : ℂ →ₗ[ℝ] ℝ) (hπ : ∀ z, |π z| ≤ ‖z‖) :
    finiteAverage (fun σ : Fin m → Bool => sSup (Set.range fun t =>
      |∑ i, finiteBernoulliSign (σ i) *
        π (rowPairing (f t) (if i ∈ E then rows i else 0))|)) ≤
      2 * Real.sqrt s * Real.sqrt (2 * ((E.card : ℝ) * K ^ 2) * Real.log (2 * (N : ℝ))) := by
  classical
  letI : NeZero N := ⟨hN.ne'⟩
  let Ξ := fun i : Fin m => if i ∈ E then rows i else 0
  let a := fun (j : Fin N) (i : Fin m) => (Ξ i j).re
  let b := fun (j : Fin N) (i : Fin m) => (Ξ i j).im
  let P := fun j (σ : Fin m → Bool) => ∑ i, finiteBernoulliSign (σ i) * a j i
  let Q := fun j (σ : Fin m → Bool) => ∑ i, finiteBernoulliSign (σ i) * b j i
  let Z := fun σ : Fin m → Bool => ∑ i, (finiteBernoulliSign (σ i) : ℂ) • Ξ i
  have hre (σ : Fin m → Bool) (j : Fin N) : (Z σ j).re = P j σ := by
    simp [Z, P, a, Complex.mul_re]
  have him (σ : Fin m → Bool) (j : Fin N) : (Z σ j).im = Q j σ := by
    simp [Z, Q, b, Complex.mul_im]
  have ha : ∀ j, ∑ i, a j i ^ 2 ≤ (E.card : ℝ) * K ^ 2 := by
    intro j
    calc
      _ ≤ ∑ i : Fin m, if i ∈ E then K ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ E
        · have h := (Complex.abs_re_le_norm (rows i j)).trans (hrows i j)
          simpa [a, Ξ, hi, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
        · simp [a, Ξ, hi]
      _ = _ := by simp
  have hb : ∀ j, ∑ i, b j i ^ 2 ≤ (E.card : ℝ) * K ^ 2 := by
    intro j
    calc
      _ ≤ ∑ i : Fin m, if i ∈ E then K ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ E
        · have h := (Complex.abs_im_le_norm (rows i j)).trans (hrows i j)
          simpa [b, Ξ, hi, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
        · simp [b, Ξ, hi]
      _ = _ := by simp
  have hZ (σ : Fin m → Bool) (j : Fin N) : ‖Z σ j‖ ≤
      finiteProcessAbsoluteMaximum P σ + finiteProcessAbsoluteMaximum Q σ := by
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
      rw [hre, him]
      exact add_le_add (abs_process_le_absoluteMaximum P j σ)
        (abs_process_le_absoluteMaximum Q j σ))
  have hpoint (σ : Fin m → Bool) : sSup (Set.range fun t =>
      |∑ i, finiteBernoulliSign (σ i) * π (rowPairing (f t) (Ξ i))|) ≤
      Real.sqrt s * (finiteProcessAbsoluteMaximum P σ + finiteProcessAbsoluteMaximum Q σ) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    have hid : ∑ i, finiteBernoulliSign (σ i) * π (rowPairing (f t) (Ξ i)) =
        π (rowPairing (f t) (Z σ)) := by
      dsimp only [Z]
      rw [rowPairing_sum_right_real_smul, map_sum]
      simp only [map_smul, smul_eq_mul]
    dsimp only
    rw [hid]
    apply (hπ _).trans
    apply (rowPairing_norm_le (f t) (Z σ) (hZ σ)).trans
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right (hf t)
    exact add_nonneg (finiteProcessAbsoluteMaximum_nonneg P σ)
      (finiteProcessAbsoluteMaximum_nonneg Q σ)
  calc
    _ ≤ finiteAverage (fun σ : Fin m → Bool => Real.sqrt s *
        (finiteProcessAbsoluteMaximum P σ + finiteProcessAbsoluteMaximum Q σ)) :=
      finiteAverage_mono hpoint
    _ = Real.sqrt s * (finiteAverage (finiteProcessAbsoluteMaximum P) +
        finiteAverage (finiteProcessAbsoluteMaximum Q)) := by
      change finiteAverage (fun σ : Fin m → Bool => Real.sqrt s •
        (finiteProcessAbsoluteMaximum P σ + finiteProcessAbsoluteMaximum Q σ)) = _
      rw [finiteAverage_smul, finiteAverage_add]
      rfl
    _ ≤ _ := by
      have hp := finiteBernoulli_absoluteMaximum_expectation_sqrt_bound a ha
      have hq := finiteBernoulli_absoluteMaximum_expectation_sqrt_bound b hb
      have h := mul_le_mul_of_nonneg_left (add_le_add hp hq) (Real.sqrt_nonneg s)
      simpa [P, Q, Fintype.card_fin, ← two_mul, mul_assoc, mul_comm, mul_left_comm] using h

/-- Scalar contraction controls a clipped projected quadratic uniformly
over an arbitrary complex coefficient class in the ℓ¹ ball. -/
theorem masked_clipped_projection_expectation_le
    {N m : ℕ} (hN : 0 < N) {T : Type*} [Nonempty T]
    (f : T → ComplexVector N) (rows : Fin m → ComplexVector N)
    (E : Finset (Fin m)) {s K R : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hf : ∀ t, coefficientL1Norm (f t) ≤ Real.sqrt s)
    (hrows : ∀ i j, ‖rows i j‖ ≤ K)
    (t₀ : T) (hfzero : f t₀ = 0)
    (π : ℂ →ₗ[ℝ] ℝ) (hπ : ∀ z, |π z| ≤ ‖z‖) :
    finiteAverage (fun σ : Fin m → Bool => sSup (Set.range fun t =>
      |∑ i, finiteBernoulliSign (σ i) * clippedRealSquare R
        (π (rowPairing (f t) (if i ∈ E then rows i else 0)))|)) ≤
      8 * R * Real.sqrt s *
        Real.sqrt (2 * ((E.card : ℝ) * K ^ 2) * Real.log (2 * (N : ℝ))) := by
  classical
  let x := fun t (i : Fin m) => π (rowPairing (f t) (if i ∈ E then rows i else 0))
  let y := fun t (i : Fin m) => clippedRealSquare R (x t i)
  have hx : ∀ i, BddAbove (Set.range fun t => |x t i|) := by
    intro i
    refine ⟨K * Real.sqrt s, ?_⟩
    rintro _ ⟨t, rfl⟩
    apply (hπ _).trans
    apply (rowPairing_norm_le (f t) _ ?_).trans
    · exact mul_le_mul_of_nonneg_left (hf t) hK
    · intro j
      split_ifs with hi
      · exact hrows i j
      · simpa using hK
  have hy : ∀ i, BddAbove (Set.range fun t => |y t i|) := by
    intro i
    refine ⟨R ^ 2, ?_⟩
    rintro _ ⟨t, rfl⟩
    dsimp only [y]
    rw [abs_of_nonneg (clippedRealSquare_nonneg _ _)]
    exact clippedRealSquare_le_radius _ _
  have hzero : ∀ i, y t₀ i = 0 := by
    intro i
    simp [y, x, hfzero, rowPairing]
  have hc := bernoulli_bounded_absoluteSupremum_contraction x y
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR)
    (fun i t u => clippedRealSquare_lipschitz hR (x t i) (x u i)) hx hy t₀ hzero
  apply hc.trans
  have hlin := masked_linear_bernoulli_supremum_expectation_le hN f rows E hf hrows π hπ
  have h := mul_le_mul_of_nonneg_left hlin
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR))
  convert h using 1
  ring

/-- The localized clipped complex-energy class has expectation proportional
to the amplitude radius and the square root of the number of retained
coordinates. This is uniform over the full, possibly infinite coefficient
class. -/
theorem masked_clipped_energy_expectation_le
    {N m : ℕ} (hN : 0 < N) {T : Type*} [Nonempty T]
    (f : T → ComplexVector N) (rows : Fin m → ComplexVector N)
    (E : Finset (Fin m)) {s K R : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hf : ∀ t, coefficientL1Norm (f t) ≤ Real.sqrt s)
    (hrows : ∀ i j, ‖rows i j‖ ≤ K)
    (t₀ : T) (hfzero : f t₀ = 0) :
    finiteAverage (fun σ : Fin m → Bool => sSup (Set.range fun t =>
      |∑ i, finiteBernoulliSign (σ i) * clippedComplexEnergy R
        (rowPairing (f t) (if i ∈ E then rows i else 0))|)) ≤
      16 * R * Real.sqrt s *
        Real.sqrt (2 * ((E.card : ℝ) * K ^ 2) * Real.log (2 * (N : ℝ))) := by
  let y := fun t (i : Fin m) => clippedRealSquare R
    (rowPairing (f t) (if i ∈ E then rows i else 0)).re
  let z := fun t (i : Fin m) => clippedRealSquare R
    (rowPairing (f t) (if i ∈ E then rows i else 0)).im
  have hy : ∀ i, BddAbove (Set.range fun t => |y t i|) := by
    intro i
    refine ⟨R ^ 2, ?_⟩
    rintro _ ⟨t, rfl⟩
    dsimp only [y]
    rw [abs_of_nonneg (clippedRealSquare_nonneg _ _)]
    exact clippedRealSquare_le_radius _ _
  have hz : ∀ i, BddAbove (Set.range fun t => |z t i|) := by
    intro i
    refine ⟨R ^ 2, ?_⟩
    rintro _ ⟨t, rfl⟩
    dsimp only [z]
    rw [abs_of_nonneg (clippedRealSquare_nonneg _ _)]
    exact clippedRealSquare_le_radius _ _
  have hpoint (σ : Fin m → Bool) : sSup (Set.range fun t =>
      |∑ i, finiteBernoulliSign (σ i) * clippedComplexEnergy R
        (rowPairing (f t) (if i ∈ E then rows i else 0))|) ≤
      sSup (Set.range fun t => |∑ i, finiteBernoulliSign (σ i) * y t i|) +
        sSup (Set.range fun t => |∑ i, finiteBernoulliSign (σ i) * z t i|) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨t, rfl⟩
    dsimp only
    change |∑ i, finiteBernoulliSign (σ i) * (y t i + z t i)| ≤ _
    simp only [mul_add, Finset.sum_add_distrib]
    exact (abs_add_le _ _).trans (add_le_add
      (le_csSup (bddAbove_range_abs_linear_combination y
        (fun i => finiteBernoulliSign (σ i)) hy) (Set.mem_range_self t))
      (le_csSup (bddAbove_range_abs_linear_combination z
        (fun i => finiteBernoulliSign (σ i)) hz) (Set.mem_range_self t)))
  have hre := masked_clipped_projection_expectation_le hN f rows E hK hR hf hrows
    t₀ hfzero Complex.reLm Complex.abs_re_le_norm
  have him := masked_clipped_projection_expectation_le hN f rows E hK hR hf hrows
    t₀ hfzero Complex.imLm Complex.abs_im_le_norm
  calc
    _ ≤ finiteAverage (fun σ : Fin m → Bool =>
        sSup (Set.range fun t => |∑ i, finiteBernoulliSign (σ i) * y t i|) +
          sSup (Set.range fun t => |∑ i, finiteBernoulliSign (σ i) * z t i|)) :=
      finiteAverage_mono hpoint
    _ = finiteAverage (fun σ : Fin m → Bool =>
        sSup (Set.range fun t => |∑ i, finiteBernoulliSign (σ i) * y t i|)) +
          finiteAverage (fun σ : Fin m → Bool =>
            sSup (Set.range fun t => |∑ i, finiteBernoulliSign (σ i) * z t i|)) :=
      finiteAverage_add _ _
    _ ≤ _ := by
      have h := add_le_add hre him
      convert h using 1 <;> first | rfl | ring

end LeanNumDetect.BoundedRieszConcentration
