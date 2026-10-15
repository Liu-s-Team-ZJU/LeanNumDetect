import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-! # Polynomial coefficient energy from finite root evaluations

This is a finite Parseval argument on `ZMod (M+1)`. No integration or
continuous Fourier-series theorem is used.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace LeanNumDetect.MultiTuran
noncomputable section

private theorem stdAddChar_norm {N : ℕ} [NeZero N] (a : ZMod N) :
    ‖ZMod.stdAddChar a‖ = 1 := (ZMod.toCircle a).norm_coe

private theorem stdAddChar_star {N : ℕ} [NeZero N] (a : ZMod N) :
    star (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [Complex.star_def, ← Complex.inv_eq_conj (stdAddChar_norm a),
    AddChar.map_neg_eq_inv]

private theorem stdAddChar_orthogonality {N : ℕ} [NeZero N] (i j : ZMod N) :
    (∑ t : ZMod N, star (ZMod.stdAddChar (i * t)) * ZMod.stdAddChar (j * t)) =
      if i = j then (N : ℂ) else 0 := by
  classical
  have he (t : ZMod N) :
      star (ZMod.stdAddChar (i * t)) * ZMod.stdAddChar (j * t) =
        ZMod.stdAddChar (t * (j - i)) := by
    rw [stdAddChar_star, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [he]
  rw [AddChar.sum_mulShift (j - i) (ZMod.isPrimitive_stdAddChar N)]
  simp [sub_eq_zero, eq_comm, ZMod.card]

/-- Finite Parseval identity for the unnormalized Fourier evaluation matrix. -/
theorem zmod_fourier_energy {N : ℕ} [NeZero N] (c : ZMod N → ℂ) :
    (∑ t : ZMod N, ‖∑ j : ZMod N, c j * ZMod.stdAddChar (j * t)‖ ^ 2) =
      (N : ℝ) * ∑ j : ZMod N, ‖c j‖ ^ 2 := by
  classical
  have hcomplex :
      (∑ t : ZMod N,
        star (∑ i : ZMod N, c i * ZMod.stdAddChar (i * t)) *
          (∑ j : ZMod N, c j * ZMod.stdAddChar (j * t))) =
        (N : ℂ) * ∑ j : ZMod N, star (c j) * c j := by
    simp only [star_sum, star_mul, Finset.sum_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i : ZMod N, ∑ j : ZMod N, (star (c i) * c j) *
          (if i = j then (N : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        calc
          _ = (star (c i) * c j) *
              ∑ t : ZMod N, star (ZMod.stdAddChar (i * t)) *
                ZMod.stdAddChar (j * t) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            ring
          _ = _ := by rw [stdAddChar_orthogonality]
      _ = _ := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        apply Finset.sum_congr rfl
        intro j _
        ring
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.star_def, Complex.conj_mul'] using hcomplex

/-- A uniform bound at the `N` roots of unity bounds coefficient energy. -/
theorem zmod_coefficient_energy_le_of_root_bound {N : ℕ} [NeZero N]
    (c : ZMod N → ℂ) {B : ℝ}
    (hbound : ∀ t : ZMod N,
      ‖∑ j : ZMod N, c j * ZMod.stdAddChar (j * t)‖ ≤ B) :
    (∑ j : ZMod N, ‖c j‖ ^ 2) ≤ B ^ 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hsum :
      (∑ t : ZMod N, ‖∑ j : ZMod N, c j * ZMod.stdAddChar (j * t)‖ ^ 2) ≤
        (N : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _t : ZMod N, B ^ 2 := Finset.sum_le_sum fun t _ =>
        (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hbound t))).mpr (hbound t)
      _ = _ := by simp [ZMod.card]
  rw [zmod_fourier_energy] at hsum
  exact (mul_le_mul_iff_right₀ hN).mp hsum

/-- Exact coefficient-energy estimate from a bound on the complex unit circle. -/
theorem polynomial_coefficient_energy_le {M : ℕ} (P : ℂ[X])
    (hdegree : P.natDegree ≤ M) {B : ℝ}
    (hbound : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ B) :
    (∑ k : Fin (M + 1), ‖P.coeff k.val‖ ^ 2) ≤ B ^ 2 := by
  let c : ZMod (M+1) → ℂ := fun j => P.coeff j.val
  have h := zmod_coefficient_energy_le_of_root_bound c (B := B) (fun t => by
    have heval : P.eval (ZMod.stdAddChar t) =
        ∑ j : ZMod (M+1), c j * ZMod.stdAddChar (j * t) := by
      rw [P.eval_eq_sum_range' (Nat.lt_succ_of_le hdegree),
        ← Fin.sum_univ_eq_sum_range]
      change (∑ j : ZMod (M+1), P.coeff j.val * ZMod.stdAddChar t ^ j.val) = _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      rw [← AddChar.map_nsmul_eq_pow]
      congr 1
      simp [nsmul_eq_mul]
    rw [← heval]
    exact hbound _ (stdAddChar_norm t))
  exact h

end
end LeanNumDetect.MultiTuran
