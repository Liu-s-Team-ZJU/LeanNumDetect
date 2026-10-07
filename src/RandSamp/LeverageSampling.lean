import RandSamp.OffGridSignal
import General.Probability.RelativeMatrixSampling
import General.MatrixAnalysis.RelativeSingularValues

/-!
# Fixed-support relative sampling from a deterministic row leverage bound

Uniform fixed-cardinality subsets are sampled without replacement.  The
population is whitened by its actual Gram matrix, so the sampling threshold
contains the leverage radius and no inverse minimum source distance.  The
deterministic conversion controls every singular value in the same event.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder

namespace LeanNumDetect.RandSamp

open FiniteMatrixSampling

noncomputable section

/-- The normalized consecutive-frequency matrix `A_M` in the manuscript. -/
def fullVandermonde {s : ℕ} (M : ℕ) (Y : Fin s → ℝ) :
    Matrix (Fin (M + 1)) (Fin s) ℂ :=
  fun k j => (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ * fourierRow Y k.val j

theorem fullVandermonde_energy {s : ℕ} (M : ℕ) (Y : Fin s → ℝ)
    (z : EuclideanSpace ℂ (Fin s)) :
    ‖(fullVandermonde M Y).toEuclideanLin z‖ ^ 2 = FiniteMatrixSampling.quadratic (fullGram M Y) z := by
  have he : (fullVandermonde M Y).toEuclideanLin z = fullFourierSignal M Y z := by
    change toLp 2 ((fullVandermonde M Y) *ᵥ ofLp z) =
      toLp 2 (fun k => (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
        ∑ j, fourierRow Y k.val j * ofLp z j)
    congr 1
    funext k
    simp [fullVandermonde, Matrix.mulVec, dotProduct,
      ← Finset.mul_sum, mul_assoc]
  rw [he, norm_fullFourierSignal_sq]

/-- Every singular value is compared with the same ordered singular value
of the full normalized matrix. Finite indices are zero-based in Lean. -/
def AllSingularValueEvent {M s m : ℕ} (Y : Fin s → ℝ) (ρ : ℝ)
    (Ω : Sample (M + 1) m) : Prop :=
  ∀ j : Fin s,
    Real.sqrt (1 - ρ) * matrixSingularValue (fullVandermonde M Y) j.val ≤
      matrixSingularValue (sampledVandermonde m Y Ω.val) j.val ∧
    matrixSingularValue (sampledVandermonde m Y Ω.val) j.val ≤
      Real.sqrt (1 + ρ) * matrixSingularValue (fullVandermonde M Y) j.val

/-- Relative Gram order controls all ordered singular values. This conversion
does not require positive definiteness or a lower singular-value estimate. -/
theorem allSingularValueEvent_of_relativeGramEvent {M s m : ℕ}
    (Y : Fin s → ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (Ω : Sample (M + 1) m) (hrelative : RelativeGramEvent Y ρ Ω) :
    AllSingularValueEvent Y ρ Ω := by
  let A := (fullVandermonde M Y).toEuclideanLin
  let B := (sampledVandermonde m Y Ω.val).toEuclideanLin
  have hlower (z : EuclideanSpace ℂ (Fin s)) :
      Real.sqrt (1 - ρ) * ‖A z‖ ≤ ‖B z‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).1
    rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hρ1)]
    change (1 - ρ) * ‖(fullVandermonde M Y).toEuclideanLin z‖ ^ 2 ≤
      ‖(sampledVandermonde m Y Ω.val).toEuclideanLin z‖ ^ 2
    rw [fullVandermonde_energy, ← quadratic_fourier_sampleMean]
    exact (hrelative z).1
  have hupper (z : EuclideanSpace ℂ (Fin s)) :
      ‖B z‖ ≤ Real.sqrt (1 + ρ) * ‖A z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + ρ)]
    change ‖(sampledVandermonde m Y Ω.val).toEuclideanLin z‖ ^ 2 ≤
      (1 + ρ) * ‖(fullVandermonde M Y).toEuclideanLin z‖ ^ 2
    rw [fullVandermonde_energy, ← quadratic_fourier_sampleMean]
    exact (hrelative z).2
  intro j
  exact singularValues_relative_bounds A B (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hlower hupper j.val

/-- Fixed-node uniform sampling with a deterministic leverage radius. The
node tuple is fixed outside the sampling probability; the result quantifies
over every coefficient vector inside one event. -/
theorem fixedSupport_relativeGram_of_leverage {M s m : ℕ}
    (hs : 0 < s) (hm : 1 ≤ m) (hmM : m ≤ M + 1)
    (Y : Fin s → ℝ) {R ρ δ : ℝ}
    (hR : 0 < R) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hδ0 : 0 < δ) (_hδ1 : δ < 1) (hG : (fullGram M Y).PosDef)
    (hleverage : ∀ (k : Fin (M + 1)) (z : EuclideanSpace ℂ (Fin s)),
      fourierRowEnergy Y k.val (ofLp z) ≤ R * FiniteMatrixSampling.quadratic (fullGram M Y) z)
    (hsample : 3 * R / ρ ^ 2 * Real.log (2 * (s : ℝ) / δ) ≤ (m : ℝ)) :
    1 - δ ≤ probability (fun Ω : Sample (M + 1) m => RelativeGramEvent Y ρ Ω) := by
  have hprob := sampleMean_relative_bounds_probability (by omega : 0 < M + 1)
    hs hm hmM (fourierPopulation Y) hR hρ0 hρ1
    (fun k => fourierRowGram_posSemidef Y k.val) hG
    (fun k z => by
      rw [fourierPopulation, quadratic_fourierRowGram]
      exact hleverage k z)
  have htail := chernoff_failure_bound_of_sample_size (Nat.cast_nonneg m)
    (by exact_mod_cast hs : (0 : ℝ) < s) hR (a := 1) (b := 1)
    (by norm_num) (le_refl 1) hρ0 hδ0
    (by simpa only [one_mul] using hsample)
  simp only [mul_one] at htail
  exact (sub_le_sub_left htail 1).trans hprob

/-- The relative Gram estimate and all singular-value comparisons hold in
the same fixed-support sampling event. -/
theorem fixedSupport_relativeGram_allSingularValues_of_leverage {M s m : ℕ}
    (hs : 0 < s) (hm : 1 ≤ m) (hmM : m ≤ M + 1)
    (Y : Fin s → ℝ) {R ρ δ : ℝ}
    (hR : 0 < R) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hG : (fullGram M Y).PosDef)
    (hleverage : ∀ (k : Fin (M + 1)) (z : EuclideanSpace ℂ (Fin s)),
      fourierRowEnergy Y k.val (ofLp z) ≤ R * FiniteMatrixSampling.quadratic (fullGram M Y) z)
    (hsample : 3 * R / ρ ^ 2 * Real.log (2 * (s : ℝ) / δ) ≤ (m : ℝ)) :
    1 - δ ≤ probability (fun Ω : Sample (M + 1) m =>
      RelativeGramEvent Y ρ Ω ∧ AllSingularValueEvent Y ρ Ω) := by
  apply (fixedSupport_relativeGram_of_leverage hs hm hmM Y hR hρ0 hρ1 hδ0 hδ1
    hG hleverage hsample).trans
  apply probability_mono
  intro Ω hΩ
  exact ⟨hΩ, allSingularValueEvent_of_relativeGramEvent Y hρ0.le hρ1.le Ω hΩ⟩

end

end LeanNumDetect.RandSamp
