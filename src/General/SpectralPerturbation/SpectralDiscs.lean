import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Tactic

/-!
# Spectral discs for a perturbed diagonal matrix

The resolvent of a diagonal matrix, followed by the Neumann series criterion,
gives the Euclidean spectral-disc bound for an arbitrary complex perturbation.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace LeanNumDetect

/-- Each characteristic-polynomial root of a perturbed diagonal matrix lies
within the spectral norm of the perturbation of a diagonal entry. -/
theorem diagonal_perturbation_root_disc {n : ℕ}
    (a : Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) (w : ℂ)
    (hw : (diagonal a + G).charpoly.IsRoot w) :
    ∃ i, ‖a i - w‖ ≤ ‖G‖ := by
  classical
  by_contra h
  push Not at h
  have hdist (i) : ‖G‖ < ‖w - a i‖ := by simpa only [norm_sub_rev] using h i
  have hne (i) : w - a i ≠ 0 := norm_pos_iff.mp ((norm_nonneg G).trans_lt (hdist i))
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => w - a i)
  let B : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (w - a i)⁻¹)
  have hDB : D * B = 1 := by
    simp only [D, B, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hne]
    · simp [hij]
  have hD : IsUnit D := by
    simp only [D, Matrix.isUnit_diagonal, Pi.isUnit_iff, isUnit_iff_ne_zero]
    exact hne
  have hBG : ‖B * G‖ < 1 := by
    by_cases hG : ‖G‖ = 0
    · have := norm_mul_le B G
      rw [hG, mul_zero] at this
      linarith
    · have hGpos : 0 < ‖G‖ := (norm_nonneg G).lt_of_ne' hG
      have hB : ‖B‖ < ‖G‖⁻¹ := by
        change ‖diagonal (fun i => (w - a i)⁻¹)‖ < _
        rw [Matrix.l2_opNorm_diagonal]
        apply (pi_norm_lt_iff (inv_pos.mpr hGpos)).mpr
        intro i
        rw [norm_inv]
        exact (inv_lt_inv₀ (hGpos.trans (hdist i)) hGpos).mpr (hdist i)
      calc
        ‖B * G‖ ≤ ‖B‖ * ‖G‖ := norm_mul_le _ _
        _ < ‖G‖⁻¹ * ‖G‖ := mul_lt_mul_of_pos_right hB hGpos
        _ = 1 := inv_mul_cancel₀ hG
  have hu := hD.mul (isUnit_one_sub_of_norm_lt_one hBG)
  have heq : D * (1 - B * G) = Matrix.scalar (Fin n) w - (diagonal a + G) := by
    rw [mul_sub, mul_one, ← mul_assoc, hDB, one_mul]
    dsimp [D]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.sub_apply, diagonal_apply_eq, Matrix.add_apply]
      ring
    · simp [hij]
  rw [heq, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
  exact hu (by simpa only [Polynomial.IsRoot, Matrix.eval_charpoly] using hw)

end LeanNumDetect
