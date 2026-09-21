import General.Fourier.BartonCubeFrame
import NumDetect.MatrixFacts
import NumDetect.SegmentedVandermonde

/-!
The complete well-separated segmented Vandermonde estimate from manuscript
Theorem `thm:well_separated_segmented`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- The coarse-block label in the Cartesian segmented grid. -/
abbrev SegmentedCoarseIndex (d r : ℕ) := Fin d → Fin (r + 1)

/-- Separate a segmented row into its coarse block and fine-cube offset. -/
def segmentedIndexEquivBlocks (d m r : ℕ) :
    SegmentedIndex d m r ≃ SegmentedCoarseIndex d r × UniformIndex d m where
  toFun α := (fun k => (α k).1, fun k => (α k).2)
  invFun p k := (p.1 k, p.2 k)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Modulation of source coefficients contributed by one coarse block. -/
def segmentedBlockCoefficients
    {d n r : ℕ} (D : ℕ) (s : SegmentedCoarseIndex d r)
    (x : Fin n → Point d) (c : Fin n → ℂ) : Fin n → ℂ :=
  fun j => c j * Complex.exp
    (Complex.I *
      ((∑ k, ((D * (s k : ℕ) : ℕ) : ℝ) * x j k : ℝ) : ℂ))

theorem segmentedBlockCoefficients_energy
    {d n r : ℕ} (D : ℕ) (s : SegmentedCoarseIndex d r)
    (x : Fin n → Point d) (c : Fin n → ℂ) :
    SegmentedVDM.energy (segmentedBlockCoefficients D s x c) =
      SegmentedVDM.energy c := by
  unfold SegmentedVDM.energy segmentedBlockCoefficients
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.norm_exp, Complex.mul_re]

theorem segmentedVandermonde_energy_eq_sum_fineCubeEnergy
    {d n m r : ℕ} (D : ℕ) (x : Fin n → Point d) (c : Fin n → ℂ) :
    SegmentedVDM.energy (segmentedVandermonde m r D x *ᵥ c) =
      ∑ s : SegmentedCoarseIndex d r,
        FineCubeFrame.fineCubeFourierEnergy m x
          (segmentedBlockCoefficients D s x c) := by
  classical
  unfold SegmentedVDM.energy FineCubeFrame.fineCubeFourierEnergy
  calc
    (∑ i, ‖(segmentedVandermonde m r D x *ᵥ c) i‖ ^ 2) =
        ∑ p : SegmentedCoarseIndex d r × UniformIndex d m,
          ‖∑ j, segmentedBlockCoefficients D p.1 x c j *
            Complex.exp (Complex.I *
              ∑ k, (((p.2 k : Fin (m + 1)) : ℕ) : ℂ) * x j k)‖ ^ 2 := by
      apply Fintype.sum_equiv (segmentedIndexEquivBlocks d m r)
      intro α
      apply congrArg (fun z : ℝ => z ^ 2)
      apply congrArg norm
      unfold segmentedVandermonde generalizedVandermonde steeringVector
        Matrix.mulVec dotProduct segmentedFrequency segmentedBlockCoefficients
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm (Complex.exp _) (c j), mul_assoc]
      apply congrArg (fun z : ℂ => c j * z)
      rw [← Complex.exp_add, ← mul_add]
      apply congrArg Complex.exp
      apply congrArg (fun z : ℂ => Complex.I * z)
      unfold dot
      push_cast
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      have hcoarse : ((segmentedIndexEquivBlocks d m r α).1 k) = (α k).1 := rfl
      have hfine : ((segmentedIndexEquivBlocks d m r α).2 k) = (α k).2 := rfl
      rw [hcoarse, hfine]
      ring
    _ = ∑ s : SegmentedCoarseIndex d r, ∑ α : UniformIndex d m,
          ‖∑ j, segmentedBlockCoefficients D s x c j *
            Complex.exp (Complex.I *
              ∑ k, (((α k : Fin (m + 1)) : ℕ) : ℂ) * x j k)‖ ^ 2 := by
      rw [Fintype.sum_prod_type]

theorem periodicMinimumLInfSeparation_le
    {d n : ℕ} (x : Fin n → Point d) (hn : 2 ≤ n)
    {i j : Fin n} (hij : i ≠ j) :
    periodicMinimumLInfSeparation x hn ≤ periodicLInfDistance (x i) (x j) := by
  unfold periodicMinimumLInfSeparation minimumOverDistinctPairs
  exact Finset.inf'_le
    (fun ij : Fin n × Fin n => periodicLInfDistance (x ij.1) (x ij.2))
    (show (i, j) ∈ distinctPairs n from by
      rw [distinctPairs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hij⟩)

/-- The segmented Vandermonde energy is the sum of `(r+1)^d` unitary
modulations of the fine-cube energy. -/
theorem segmentedVandermonde_energy_bounds
    {d n m r D : ℕ} {β : ℝ}
    (x : Fin n → Point d)
    (hd : 1 ≤ d) (hm : 1 ≤ m)
    (hβ : 1 / (2 * Real.log 2) ≤ β)
    (hx : ∀ j, InAngularCube (x j))
    (hsep : ∀ i j, i ≠ j →
      4 * Real.pi * β * d / (m + 1) ≤ periodicLInfDistance (x i) (x j)) :
    ∀ c,
      (2 - Real.exp (1 / (2 * β))) *
          (((segmentedLength m r) ^ d : ℕ) : ℝ) * SegmentedVDM.energy c ≤
        SegmentedVDM.energy (segmentedVandermonde m r D x *ᵥ c) ∧
      SegmentedVDM.energy (segmentedVandermonde m r D x *ᵥ c) ≤
        Real.exp (1 / (2 * β)) *
          (((segmentedLength m r) ^ d : ℕ) : ℝ) * SegmentedVDM.energy c := by
  intro c
  have hblock (s : SegmentedCoarseIndex d r) :=
    BartonCubeFrame.fineCubeFourier_bounds_of_translatedCube β x hd hm hβ hx
      (by
        intro i j hij
        simpa [FineCubeFrame.angularPeriodicLInfDistance,
          FineCubeFrame.angularPeriodicCoordinateDistance,
          periodicLInfDistance, periodicCoordinateDistance] using hsep i j hij)
      (segmentedBlockCoefficients D s x c)
  have hcard : Fintype.card (SegmentedCoarseIndex d r) = (r + 1) ^ d := by
    simp
  have hsumLower :
      ∑ s : SegmentedCoarseIndex d r,
          ((2 - Real.exp (1 / (2 * β))) * (((m + 1) ^ d : ℕ) : ℝ) *
            SegmentedVDM.energy c) ≤
        ∑ s : SegmentedCoarseIndex d r,
          FineCubeFrame.fineCubeFourierEnergy m x
            (segmentedBlockCoefficients D s x c) := by
    apply Finset.sum_le_sum
    intro s _
    rw [← segmentedBlockCoefficients_energy D s x c]
    simpa [External.coefficientEnergy, SegmentedVDM.energy] using (hblock s).1
  have hsumUpper :
      ∑ s : SegmentedCoarseIndex d r,
          FineCubeFrame.fineCubeFourierEnergy m x
            (segmentedBlockCoefficients D s x c) ≤
        ∑ s : SegmentedCoarseIndex d r,
          (Real.exp (1 / (2 * β)) * (((m + 1) ^ d : ℕ) : ℝ) *
            SegmentedVDM.energy c) := by
    apply Finset.sum_le_sum
    intro s _
    rw [← segmentedBlockCoefficients_energy D s x c]
    simpa [External.coefficientEnergy, SegmentedVDM.energy] using (hblock s).2
  rw [segmentedVandermonde_energy_eq_sum_fineCubeEnergy D x c]
  constructor
  · calc
      (2 - Real.exp (1 / (2 * β))) *
            (((segmentedLength m r) ^ d : ℕ) : ℝ) * SegmentedVDM.energy c =
          ∑ _s : SegmentedCoarseIndex d r,
            ((2 - Real.exp (1 / (2 * β))) * (((m + 1) ^ d : ℕ) : ℝ) *
              SegmentedVDM.energy c) := by
            simp [segmentedLength, hcard, mul_pow]
            ring
      _ ≤ _ := hsumLower
  · calc
      _ ≤ ∑ _s : SegmentedCoarseIndex d r,
            (Real.exp (1 / (2 * β)) * (((m + 1) ^ d : ℕ) : ℝ) *
              SegmentedVDM.energy c) := hsumUpper
      _ = Real.exp (1 / (2 * β)) *
            (((segmentedLength m r) ^ d : ℕ) : ℝ) * SegmentedVDM.energy c := by
          simp [segmentedLength, hcard, mul_pow]
          ring

theorem matrixSingularValue_sq_bounds_of_energy
    {ρ : Type*} [Fintype ρ] {n : ℕ}
    (V : Matrix ρ (Fin n) ℂ) (hn : 0 < n) {L U : ℝ}
    (henergy : ∀ c,
      L * SegmentedVDM.energy c ≤ SegmentedVDM.energy (V *ᵥ c) ∧
      SegmentedVDM.energy (V *ᵥ c) ≤ U * SegmentedVDM.energy c) :
    L ≤ matrixSingularValue V (n - 1) ^ 2 ∧
      matrixSingularValue V 0 ^ 2 ≤ U := by
  constructor
  · obtain ⟨v, hv, he⟩ :=
      singularValue_gram_eigenvector V (by omega : n - 1 < n)
    have hp := SegmentedVDM.energy_pos v hv
    have h := (henergy v).1
    rw [SegmentedVDM.gram_eigenvector_energy V v _ he] at h
    nlinarith
  · obtain ⟨v, hv, he⟩ := singularValue_gram_eigenvector V hn
    have hp := SegmentedVDM.energy_pos v hv
    have h := (henergy v).2
    rw [SegmentedVDM.gram_eigenvector_energy V v _ he] at h
    nlinarith

/-- Manuscript Theorem `thm:well_separated_segmented`: the complete lower and
upper singular-value estimate for a well-separated segmented grid. -/
theorem wellSeparatedSegmented_singularValue_bounds
    {d n m r D : ℕ} {β : ℝ}
    (x : Fin n → Point d)
    (hd : 1 ≤ d) (hn : 0 < n) (hm : 1 ≤ m) (_hD : m < D)
    (hβ : 1 / (2 * Real.log 2) ≤ β)
    (hx : ∀ j, InAngularCube (x j))
    (hsep : ∀ hn2 : 2 ≤ n,
      4 * Real.pi * β * d / (m + 1) ≤
        periodicMinimumLInfSeparation x hn2) :
    (2 - Real.exp (1 / (2 * β))) *
          ((((r + 1) * (m + 1)) ^ d : ℕ) : ℝ) ≤
        matrixSingularValue (segmentedVandermonde m r D x) (n - 1) ^ 2 ∧
      matrixSingularValue (segmentedVandermonde m r D x) (n - 1) ^ 2 ≤
        matrixSingularValue (segmentedVandermonde m r D x) 0 ^ 2 ∧
      matrixSingularValue (segmentedVandermonde m r D x) 0 ^ 2 ≤
        Real.exp (1 / (2 * β)) *
          ((((r + 1) * (m + 1)) ^ d : ℕ) : ℝ) := by
  have hpair : ∀ i j, i ≠ j →
      4 * Real.pi * β * d / (m + 1) ≤
        periodicLInfDistance (x i) (x j) := by
    intro i j hij
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn1 : n = 1 := by omega
      subst n
      exact hij (Subsingleton.elim i j)
    exact (hsep hn2).trans (periodicMinimumLInfSeparation_le x hn2 hij)
  have hframe := segmentedVandermonde_energy_bounds
    (r := r) (D := D) x hd hm hβ hx hpair
  have hsv := matrixSingularValue_sq_bounds_of_energy
    (segmentedVandermonde m r D x) hn hframe
  refine ⟨hsv.1, ?_, hsv.2⟩
  have hmono := matrixSingularValue_antitone
    (segmentedVandermonde m r D x) (Nat.zero_le (n - 1))
  exact (sq_le_sq₀
    (matrixSingularValue_nonneg _ _) (matrixSingularValue_nonneg _ _)).2 hmono

end

end NumDetect
end LeanNumDetect
