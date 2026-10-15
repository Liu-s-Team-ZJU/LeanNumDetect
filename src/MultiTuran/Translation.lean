import MultiTuran.Energy

/-! # Common node translation

A common translation multiplies every sampled row and every continuous
exponential sum by a phase of modulus one. These equalities justify the
"after a common translation" convention in `lem:sv-md-array` without
altering any singular value or either norm in the norming inequality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators

namespace LeanNumDetect.MultiTuran
noncomputable section

def translateNodes {d n : ℕ} (Y : Fin n → Point d) (center : Point d) :
    Fin n → Point d := fun j q => Y j q - center q

@[simp] theorem torusCoordinateDistance_sub_common (x y a : ℝ) :
    torusCoordinateDistance (x - a) (y - a) = torusCoordinateDistance x y := by
  unfold torusCoordinateDistance
  congr 2
  ring

@[simp] theorem torusLInfDistance_sub_common {d : ℕ} (x y a : Point d) :
    torusLInfDistance (x - a) (y - a) = torusLInfDistance x y := by
  simp only [torusLInfDistance, Pi.sub_apply, torusCoordinateDistance_sub_common]

@[simp] theorem nodeSeparation_translateNodes {d n : ℕ}
    (Y : Fin n → Point d) (center : Point d) :
    nodeSeparation (translateNodes Y center) = nodeSeparation Y := by
  have h (j : Fin n) : translateNodes Y center j = Y j - center := rfl
  simp only [nodeSeparation, h, torusLInfDistance_sub_common]

@[simp] theorem nodeDiameter_translateNodes {d n : ℕ}
    (Y : Fin n → Point d) (center : Point d) :
    nodeDiameter (translateNodes Y center) = nodeDiameter Y := by
  have h (j : Fin n) : translateNodes Y center j = Y j - center := rfl
  simp only [nodeDiameter, h, torusLInfDistance_sub_common]

/-- The exact common phase introduced by a node translation. -/
theorem exponentialSum_translateNodes {d n : ℕ} (Y : Fin n → Point d)
    (c : Fin n → ℂ) (center t : Point d) :
    exponentialSum (translateNodes Y center) c t =
      Complex.exp (Complex.I * ((-∑ q, t q * center q : ℝ) : ℂ)) *
        exponentialSum Y c t := by
  unfold exponentialSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : Complex.exp (Complex.I * ((∑ q, t q * translateNodes Y center j q : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((-∑ q, t q * center q : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((∑ q, t q * Y j q : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [translateNodes, mul_sub, Finset.sum_sub_distrib]
    push_cast
    ring
  rw [he]
  ring

@[simp] theorem norm_exponentialSum_translateNodes {d n : ℕ}
    (Y : Fin n → Point d) (c : Fin n → ℂ) (center t : Point d) :
    ‖exponentialSum (translateNodes Y center) c t‖ = ‖exponentialSum Y c t‖ := by
  rw [exponentialSum_translateNodes, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

@[simp] theorem setEnergy_translateNodes {d n : ℕ} (Y : Fin n → Point d)
    (c : Fin n → ℂ) (center : Point d) (S : Set (Point d)) :
    setEnergy (translateNodes Y center) c S = setEnergy Y c S := by
  simp only [setEnergy, norm_exponentialSum_translateNodes]

@[simp] theorem continuousEnergy_translateNodes {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (c : Fin n → ℂ) (center : Point d) :
    continuousEnergy G (translateNodes Y center) c = continuousEnergy G Y c := by
  exact setEnergy_translateNodes Y c center G.thickening

@[simp] theorem discreteEnergy_translateNodes {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (c : Fin n → ℂ) (center : Point d) :
    discreteEnergy G (translateNodes Y center) c = discreteEnergy G Y c := by
  simp only [discreteEnergy, norm_exponentialSum_translateNodes]

@[simp] theorem continuousNorming_translateNodes_iff {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (center : Point d) (η : ℝ) :
    ContinuousNorming G (translateNodes Y center) η ↔ ContinuousNorming G Y η := by
  simp only [ContinuousNorming, continuousEnergy_translateNodes, discreteEnergy_translateNodes]

/-- Generalized Vandermonde evaluation agrees with the article's sum. -/
theorem vandermondeMatrix_mulVec {ι : Type*} [Fintype ι] {d n : ℕ}
    (frequency : ι → Point d) (Y : Fin n → Point d) (c : Fin n → ℂ) (k : ι) :
    (vandermondeMatrix frequency Y *ᵥ c) k = exponentialSum Y c (frequency k) := by
  simp only [Matrix.mulVec, dotProduct, vandermondeMatrix, exponentialSum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- All singular values, including the least column singular value, are
invariant under common translation of the nodes. -/
theorem vandermondeMatrix_singularValues_translateNodes
    {ι : Type*} [Fintype ι] {d n : ℕ} (frequency : ι → Point d)
    (Y : Fin n → Point d) (center : Point d) :
    (vandermondeMatrix frequency (translateNodes Y center)).toEuclideanLin.singularValues =
      (vandermondeMatrix frequency Y).toEuclideanLin.singularValues := by
  apply singularValues_eq_of_norm_eq
  intro z
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro k _
  change ‖(vandermondeMatrix frequency (translateNodes Y center) *ᵥ ofLp z) k‖ ^ 2 =
    ‖(vandermondeMatrix frequency Y *ᵥ ofLp z) k‖ ^ 2
  simp only [vandermondeMatrix_mulVec, norm_exponentialSum_translateNodes]

end
end LeanNumDetect.MultiTuran
