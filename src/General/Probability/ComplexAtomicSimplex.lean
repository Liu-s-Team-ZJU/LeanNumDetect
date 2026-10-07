import General.Probability.BoundedRowEstimates

/-!
# A finite atomic simplex containing a complex ℓ¹ ball

The atoms are zero and the four signed coordinate directions. A vector with
complex ℓ¹ norm at most `R / 2` is represented by a probability simplex on
these `4N + 1` atoms. The factor two avoids any real-versus-complex convention
in the elementary empirical approximation argument.
-/

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect.BoundedRieszConcentration

def complexCoordinatePhase (d : Fin 4) : ℂ :=
  if d.val = 0 then 1 else if d.val = 1 then -1 else if d.val = 2 then Complex.I else -Complex.I

def complexCoordinateMass (z : ℂ) (d : Fin 4) : ℝ :=
  if d.val = 0 then max z.re 0 else if d.val = 1 then max (-z.re) 0
  else if d.val = 2 then max z.im 0 else max (-z.im) 0

theorem complexCoordinatePhase_norm (d : Fin 4) : ‖complexCoordinatePhase d‖ = 1 := by
  fin_cases d <;> simp [complexCoordinatePhase]

theorem complexCoordinateMass_nonneg (z : ℂ) (d : Fin 4) :
    0 ≤ complexCoordinateMass z d := by
  fin_cases d <;> simp [complexCoordinateMass]

theorem sum_complexCoordinateMass (z : ℂ) :
    ∑ d, complexCoordinateMass z d = |z.re| + |z.im| := by
  have hp (r : ℝ) : max r 0 + max (-r) 0 = |r| := by
    by_cases hr : 0 ≤ r
    · rw [max_eq_left hr, max_eq_right (by linarith), abs_of_nonneg hr]
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith),
        abs_of_neg (lt_of_not_ge hr)]
      ring
  rw [Fin.sum_univ_four]
  change max z.re 0 + max (-z.re) 0 + max z.im 0 + max (-z.im) 0 = _
  rw [hp, add_assoc, hp]

theorem sum_complexCoordinateMass_phase (z : ℂ) :
    ∑ d, (complexCoordinateMass z d : ℂ) * complexCoordinatePhase d = z := by
  have hm (r : ℝ) : max r 0 - max (-r) 0 = r := by
    by_cases hr : 0 ≤ r
    · rw [max_eq_left hr, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  rw [Fin.sum_univ_four]
  change ((max z.re 0 : ℝ) : ℂ) * 1 + ((max (-z.re) 0 : ℝ) : ℂ) * (-1) +
    ((max z.im 0 : ℝ) : ℂ) * Complex.I + ((max (-z.im) 0 : ℝ) : ℂ) * (-Complex.I) = z
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  · simpa only [sub_eq_add_neg] using hm z.re
  · simpa only [sub_eq_add_neg] using hm z.im

/-- Zero together with the four signed real and imaginary coordinate atoms. -/
def complexCoordinateAtom {N : ℕ} (R : ℝ) :
    Option (Fin N × Fin 4) → ComplexVector N
  | none => 0
  | some (j, d) => fun i => if i = j then (R : ℂ) * complexCoordinatePhase d else 0

noncomputable def complexCoordinateWeights {N : ℕ} (R : ℝ) (f : ComplexVector N) :
    Option (Fin N × Fin 4) → ℝ
  | none => 1 - (∑ j, (|Complex.re (f j)| + |Complex.im (f j)|)) / R
  | some (j, d) => complexCoordinateMass (f j) d / R

theorem realImaginaryL1_le_twice {N : ℕ} (f : ComplexVector N) :
    (∑ j, (|Complex.re (f j)| + |Complex.im (f j)|)) ≤
      2 * coefficientL1Norm f := by
  calc
    _ ≤ ∑ j, (‖f j‖ + ‖f j‖) := Finset.sum_le_sum fun j _ =>
      add_le_add (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
    _ = _ := by simp only [coefficientL1Norm, Finset.sum_add_distrib]; ring

theorem complexCoordinateWeights_nonneg {N : ℕ} {R : ℝ} (hR : 0 < R)
    (f : ComplexVector N) (hf : 2 * coefficientL1Norm f ≤ R)
    (a : Option (Fin N × Fin 4)) : 0 ≤ complexCoordinateWeights R f a := by
  cases a with
  | none =>
    dsimp [complexCoordinateWeights]
    have h := (div_le_one hR).mpr ((realImaginaryL1_le_twice f).trans hf)
    linarith
  | some a => exact div_nonneg (complexCoordinateMass_nonneg _ _) hR.le

theorem sum_complexCoordinateWeights {N : ℕ} {R : ℝ}
    (f : ComplexVector N) : ∑ a, complexCoordinateWeights R f a = 1 := by
  classical
  simp only [Fintype.sum_option, Fintype.sum_prod_type, complexCoordinateWeights]
  simp_rw [← Finset.sum_div, sum_complexCoordinateMass]
  ring

theorem complexCoordinateAtom_coordinate_bound {N : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (a : Option (Fin N × Fin 4)) (i : Fin N) : ‖complexCoordinateAtom R a i‖ ≤ R := by
  cases a with
  | none => simpa [complexCoordinateAtom] using hR
  | some a =>
    simp only [complexCoordinateAtom]
    split_ifs
    · simp [complexCoordinatePhase_norm, Real.norm_eq_abs, abs_of_nonneg hR]
    · simpa using hR

theorem coefficientL1Norm_complexCoordinateAtom_le {N : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (a : Option (Fin N × Fin 4)) : coefficientL1Norm (complexCoordinateAtom R a) ≤ R := by
  classical
  cases a with
  | none => simpa [complexCoordinateAtom] using hR
  | some a =>
    rcases a with ⟨j, d⟩
    simp only [coefficientL1Norm, complexCoordinateAtom]
    simp only [apply_ite norm, norm_zero]
    rw [Finset.sum_ite_eq']
    simp [complexCoordinatePhase_norm, Real.norm_eq_abs, abs_of_nonneg hR]

/-- Exact barycenter identity for the atomic probability simplex. -/
theorem sum_weights_complexCoordinateAtom {N : ℕ} {R : ℝ} (hR : R ≠ 0)
    (f : ComplexVector N) :
    (∑ a, (complexCoordinateWeights R f a : ℂ) • complexCoordinateAtom R a) = f := by
  classical
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_option,
    Fintype.sum_prod_type, complexCoordinateWeights, complexCoordinateAtom,
    Pi.zero_apply, mul_zero, zero_add]
  rw [Finset.sum_comm]
  simp_rw [mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  simpa only [Complex.ofReal_div, ← mul_assoc, div_mul_cancel₀ _ hRc] using
    sum_complexCoordinateMass_phase (f i)

/-- Every point of a complex ℓ¹ ball is the barycenter of a finite probability
simplex whose atoms have coordinate bound twice the ball radius. -/
theorem complexL1Ball_atomicSimplex {N : ℕ} {s : ℝ} (hs : 0 < s)
    (f : ComplexVector N) (hf : coefficientL1Norm f ≤ Real.sqrt s) :
    ∃ w : Option (Fin N × Fin 4) → ℝ,
      (∀ a, 0 ≤ w a) ∧ (∑ a, w a = 1) ∧
      (∑ a, (w a : ℂ) • complexCoordinateAtom (2 * Real.sqrt s) a) = f ∧
      (∀ (a : Option (Fin N × Fin 4)) (j : Fin N),
        ‖complexCoordinateAtom (2 * Real.sqrt s) a j‖ ≤ 2 * Real.sqrt s) := by
  have hR : 0 < 2 * Real.sqrt s := by positivity
  refine ⟨complexCoordinateWeights (2 * Real.sqrt s) f,
    complexCoordinateWeights_nonneg hR f (by linarith),
    sum_complexCoordinateWeights f,
    sum_weights_complexCoordinateAtom hR.ne' f,
    complexCoordinateAtom_coordinate_bound hR.le⟩

end LeanNumDetect.BoundedRieszConcentration
