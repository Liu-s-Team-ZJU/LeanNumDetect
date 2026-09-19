import General.SpectralPerturbation.SpectralDiscMatching
import General.SpectralPerturbation.SpectralDiscs
import General.SpectralPerturbation.SpectralEnumeration
import Mathlib.Topology.Instances.Matrix

/-!
# Spectral variation of a perturbed diagonal matrix

The Euclidean norm specialization of Stewart--Sun, *Matrix Perturbation
Theory*, IV.3.3, is proved here. The proof uses the homotopy $D+tG$ and the
spectral-disc grouping argument of IV.1.5, retaining algebraic multiplicities.
There is no separation assumption or restriction on the perturbation size.
-/

noncomputable section
open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace LeanNumDetect

/-- Full-multiplicity eigenvalue matching for an arbitrary complex perturbation
of a diagonal matrix, in Euclidean operator norm. -/
theorem diagonal_perturbation_spectral_matching {n : ℕ}
    (a z : Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ)
    (hz : EigenvalueEnumeration (diagonal a + G) z) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i,
      ‖a i - z (σ i)‖ ≤ (2 * (n : ℝ) - 1) * ‖G‖ := by
  let H (t : ℝ) : Matrix (Fin n) (Fin n) ℂ := diagonal a + (t : ℂ) • G
  let p (t : ℝ) : ℂ → ℂ := (H t).charpoly.eval
  have hp : Continuous p := by
    apply continuous_pi
    intro w
    change Continuous (fun t : ℝ => (H t).charpoly.eval w)
    simp only [Matrix.eval_charpoly]
    unfold H
    fun_prop
  have hp0 : p 0 = rootProduct a := by
    simpa [p, H] using (diagonal_eigenvalueEnumeration a).eval_eq_rootProduct
  have hp1 : p 1 = rootProduct z := by
    simpa [p, H] using hz.eval_eq_rootProduct
  apply spectral_disc_homotopy_matching a z ‖G‖ (norm_nonneg G) p hp.continuousOn hp0 hp1
  intro t ht
  obtain ⟨b, hb⟩ := exists_eigenvalueEnumeration (H t)
  refine ⟨b, hb.eval_eq_rootProduct, fun j => ?_⟩
  obtain ⟨i, hi⟩ := diagonal_perturbation_root_disc a ((t : ℂ) • G) (b j) (hb.isRoot j)
  refine ⟨i, ?_⟩
  have hnorm : ‖(t : ℂ) • G‖ ≤ ‖G‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg G) ht.2
  simpa only [dist_eq_norm, norm_sub_rev] using hi.trans hnorm

end LeanNumDetect
