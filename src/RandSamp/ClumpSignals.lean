import RandSamp.ClumpSubspaceGeometry
import RandSamp.LeverageSampling

/-! Exact coefficient and signal decomposition along a nonempty clump partition. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect.RandSamp
noncomputable section

namespace ClumpPartition
variable {n A : ℕ} (P : ClumpPartition n A)

theorem sum_enumeration {β : Type*} [AddCommMonoid β] (a : Fin A) (f : Fin n → β) :
    (∑ j : Fin (P.size a), f (P.enumeration a j).val) = ∑ j ∈ P.members a, f j := by
  rw [← Finset.sum_coe_sort (P.members a) f]
  exact (P.enumeration a).sum_comp (fun j => f j.val)

/-- Every coefficient appears exactly once in the partition. -/
theorem sum_clumps {β : Type*} [AddCommMonoid β] (f : Fin n → β) :
    (∑ a : Fin A, ∑ j : Fin (P.size a), f (P.enumeration a j).val) = ∑ j, f j := by
  simp_rw [P.sum_enumeration]
  have h := Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin A)) P.label f
  simpa only [members, Finset.mem_univ, Finset.filter_true] using h

/-- Restriction of a Euclidean coefficient vector to a clump. -/
def coefficients (a : Fin A) (z : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin (P.size a)) :=
  toLp 2 (fun j => z (P.enumeration a j).val)

theorem sum_coefficients_norm_sq (z : EuclideanSpace ℂ (Fin n)) :
    (∑ a, ‖P.coefficients a z‖ ^ 2) = ‖z‖ ^ 2 := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  exact P.sum_clumps (fun j => ‖z j‖ ^ 2)

/-- Normalized full-frequency signal from just one clump. -/
def signal (M : ℕ) (Y : Fin n → ℝ) (z : EuclideanSpace ℂ (Fin n)) (a : Fin A) :
    EuclideanSpace ℂ (Fin (M + 1)) :=
  fullFourierSignal M (P.nodes Y a) (P.coefficients a z)

theorem sum_signals (M : ℕ) (Y : Fin n → ℝ) (z : EuclideanSpace ℂ (Fin n)) :
    (∑ a, P.signal M Y z a) = fullFourierSignal M Y z := by
  ext k
  change (∑ a, P.signal M Y z a) k = _
  simp only [WithLp.ofLp_sum, Finset.sum_apply, signal, fullFourierSignal,
    coefficients, ofLp_toLp]
  change (∑ a, (Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ *
    ∑ j : Fin (P.size a), fourierRow Y k.val (P.enumeration a j).val *
      z (P.enumeration a j).val) = _
  rw [← Finset.mul_sum, P.sum_clumps (fun j => fourierRow Y k.val j * z j)]

theorem signal_mem_columnSubspace (M : ℕ) (Y : Fin n → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (a : Fin A) :
    P.signal M Y z a ∈ P.columnSubspace M Y a := by
  have he : P.signal M Y z a = ∑ j : Fin (P.size a),
      ((Real.sqrt ((M + 1 : ℕ) : ℝ) : ℂ)⁻¹ * z (P.enumeration a j).val) •
        toLp 2 (fun k : Fin (M + 1) => fourierRow (P.nodes Y a) k.val j) := by
    ext k
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul, signal, fullFourierSignal, coefficients, ofLp_toLp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨j, rfl⟩

end ClumpPartition
end
end LeanNumDetect.RandSamp
