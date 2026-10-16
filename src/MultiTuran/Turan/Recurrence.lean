import General.Fourier.ExponentialSums
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Polynomial growth for sums of powers of unit roots

Removing one root by a first difference and using Pascal's identity gives
the exact degree `n - 1` extrapolation majorant. Roots may coincide.
-/

set_option autoImplicit false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.TuranRecurrence
noncomputable section

def powerSum {n : ℕ} (z c : Fin n → ℂ) (M : ℕ) : ℂ :=
  ∑ j, c j * z j ^ M

def majorant (n M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (2 : ℝ)^j * (M.choose j : ℝ)

theorem majorant_nonneg (n M : ℕ) : 0 ≤ majorant n M := by
  unfold majorant
  positivity

@[simp] theorem majorant_zero (M : ℕ) : majorant 0 M = 0 := by
  simp [majorant]

@[simp] theorem majorant_at_zero (n : ℕ) : majorant (n+1) 0 = 1 := by
  unfold majorant
  rw [Finset.sum_range_succ']
  simp

theorem majorant_succ (n M : ℕ) :
    majorant (n+1) (M+1) = majorant (n+1) M + 2 * majorant n M := by
  unfold majorant
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
  simp_rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ, mul_add]
  rw [Finset.sum_add_distrib]
  simp_rw [mul_assoc, Nat.succ_eq_add_one]
  have hsum : (∑ x ∈ Finset.range n, (2 : ℝ)^x * (2 * (M.choose x : ℝ))) =
      2 * ∑ x ∈ Finset.range n, (2 : ℝ)^x * (M.choose x : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  ring

theorem powerSum_difference {n : ℕ} (z c : Fin (n+1) → ℂ) (M : ℕ) :
    powerSum (fun j : Fin n => z j.succ)
      (fun j => c j.succ * (z j.succ - z 0)) M =
        powerSum z c (M+1) - z 0 * powerSum z c M := by
  unfold powerSum
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, mul_add,
    Finset.mul_sum, add_sub_add_comm]
  have hhead : c 0 * z 0 ^ (M+1) - z 0 * (c 0 * z 0 ^ M) = 0 := by
    rw [pow_succ]
    ring
  rw [hhead, zero_add, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

/-- Genuine extrapolation for a finite power sum. The coefficient has exact
polynomial degree `n - 1` in the extrapolation index. -/
theorem unit_powerSum_norm_le {n : ℕ} (z c : Fin n → ℂ)
    (hz : ∀ j, ‖z j‖ ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hinitial : ∀ k < n, ‖powerSum z c k‖ ≤ B) (M : ℕ) :
    ‖powerSum z c M‖ ≤ B * majorant n M := by
  induction n generalizing B M with
  | zero => simp [powerSum, majorant]
  | succ n ih =>
    let z' : Fin n → ℂ := fun j => z j.succ
    let c' : Fin n → ℂ := fun j => c j.succ * (z j.succ-z 0)
    have hdiff (k : ℕ) :
        powerSum z' c' k = powerSum z c (k+1)-z 0*powerSum z c k :=
      powerSum_difference z c k
    have hinit' : ∀ k < n, ‖powerSum z' c' k‖ ≤ 2*B := by
      intro k hk
      rw [hdiff]
      calc
        _ ≤ ‖powerSum z c (k+1)‖ + ‖z 0*powerSum z c k‖ := norm_sub_le _ _
        _ ≤ B + ‖powerSum z c k‖ := by
          apply add_le_add (hinitial (k+1) (by omega))
          rw [norm_mul]
          simpa using mul_le_mul_of_nonneg_right (hz 0) (norm_nonneg (powerSum z c k))
        _ ≤ B+B := add_le_add le_rfl (hinitial k (by omega))
        _ = 2*B := by ring
    have hg (k : ℕ) : ‖powerSum z' c' k‖ ≤ (2*B)*majorant n k :=
      ih z' c' (fun j => hz j.succ) (by positivity) hinit' k
    induction M with
    | zero => simpa using hinitial 0 (by omega)
    | succ M hM =>
      have hstep : powerSum z c (M+1) = z 0*powerSum z c M+powerSum z' c' M := by
        rw [hdiff]
        ring
      rw [hstep]
      calc
        _ ≤ ‖z 0*powerSum z c M‖ + ‖powerSum z' c' M‖ := norm_add_le _ _
        _ ≤ ‖powerSum z c M‖ + ‖powerSum z' c' M‖ := by
          rw [norm_mul]
          exact add_le_add (by
            simpa using mul_le_mul_of_nonneg_right (hz 0) (norm_nonneg (powerSum z c M))) le_rfl
        _ ≤ B*majorant (n+1) M+(2*B)*majorant n M := add_le_add hM (hg M)
        _ = B*majorant (n+1) (M+1) := by rw [majorant_succ]; ring

end
end LeanNumDetect.MultiTuran.TuranRecurrence
