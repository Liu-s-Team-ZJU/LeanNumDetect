import General.Fourier.ExponentialSums
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic

/-! # The finite-dimensional space of restricted exponential sums

The carrier is the actual range in continuous functions on `[0,1]`. Linear
coefficient representatives are chosen only to define convenient formulas;
the differentiation endomorphism is proved independent of that choice.
This module installs no norm or inner product on the range carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set

namespace LeanNumDetect.MultiTuran.ExponentialInterval
noncomputable section

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

/-- Restriction of an actual exponential sum to the closed unit interval. -/
def coefficientMap {n : ℕ} (frequency : Fin n → ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] C(UnitInterval, ℂ) where
  toFun c := ⟨fun t => ExponentialSumEstimates.exponentialSum frequency c t.val,
    (ExponentialSumEstimates.continuous_exponentialSum frequency c).comp continuous_subtype_val⟩
  map_add' c z := by
    ext t
    change ExponentialSumEstimates.exponentialSum frequency (c+z) t.val =
      ExponentialSumEstimates.exponentialSum frequency c t.val +
        ExponentialSumEstimates.exponentialSum frequency z t.val
    simp only [ExponentialSumEstimates.exponentialSum,
      Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    ext t
    change ExponentialSumEstimates.exponentialSum frequency (a • c) t.val =
      a * ExponentialSumEstimates.exponentialSum frequency c t.val
    simp only [ExponentialSumEstimates.exponentialSum,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- A separate algebraic carrier, allowing a subsequent genuine `L²` norm. -/
def Space {n : ℕ} (frequency : Fin n → ℝ) : Type :=
  (coefficientMap frequency).range

instance {n : ℕ} (frequency : Fin n → ℝ) : AddCommGroup (Space frequency) :=
  inferInstanceAs (AddCommGroup (coefficientMap frequency).range)

instance {n : ℕ} (frequency : Fin n → ℝ) : Module ℂ (Space frequency) :=
  inferInstanceAs (Module ℂ (coefficientMap frequency).range)

instance {n : ℕ} (frequency : Fin n → ℝ) : FiniteDimensional ℂ (Space frequency) :=
  inferInstanceAs (FiniteDimensional ℂ (coefficientMap frequency).range)

def toContinuousMap {n : ℕ} (frequency : Fin n → ℝ) :
    Space frequency →ₗ[ℂ] C(UnitInterval, ℂ) := (coefficientMap frequency).range.subtype

instance {n : ℕ} (frequency : Fin n → ℝ) : CoeFun (Space frequency) (fun _ => UnitInterval → ℂ) :=
  ⟨fun f => toContinuousMap frequency f⟩

theorem toContinuousMap_injective {n : ℕ} (frequency : Fin n → ℝ) :
    Function.Injective (toContinuousMap frequency) := Subtype.val_injective

private instance projective_range {n : ℕ} (frequency : Fin n → ℝ) :
    Module.Projective ℂ (coefficientMap frequency).range :=
  Module.Projective.of_basis (Module.Basis.ofVectorSpace ℂ (coefficientMap frequency).range)

/-- A linear choice of coefficients, with no frequency separation assumption. -/
def coefficients {n : ℕ} (frequency : Fin n → ℝ) : Space frequency →ₗ[ℂ] (Fin n → ℂ) :=
  Classical.choose ((coefficientMap frequency).rangeRestrict.exists_rightInverse_of_surjective
    (coefficientMap frequency).range_rangeRestrict)

theorem reconstruct {n : ℕ} (frequency : Fin n → ℝ) (f : Space frequency) :
    (coefficientMap frequency).rangeRestrict (coefficients frequency f) = f := by
  exact LinearMap.congr_fun (Classical.choose_spec
    ((coefficientMap frequency).rangeRestrict.exists_rightInverse_of_surjective
      (coefficientMap frequency).range_rangeRestrict)) f

/-- The chosen representative is an actual exponential sum on the whole line. -/
def representative {n : ℕ} (frequency : Fin n → ℝ) (f : Space frequency) : ℝ → ℂ :=
  ExponentialSumEstimates.exponentialSum frequency (coefficients frequency f)

theorem continuous_representative {n : ℕ} (frequency : Fin n → ℝ) (f : Space frequency) :
    Continuous (representative frequency f) :=
  ExponentialSumEstimates.continuous_exponentialSum frequency _

theorem differentiable_representative {n : ℕ} (frequency : Fin n → ℝ) (f : Space frequency) :
    Differentiable ℝ (representative frequency f) :=
  ExponentialSumEstimates.differentiable_exponentialSum frequency _

theorem representative_eq_value {n : ℕ} (frequency : Fin n → ℝ) (f : Space frequency)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : representative frequency f t = f ⟨t,ht⟩ := by
  have h := congrArg (fun g : Space frequency => g ⟨t,ht⟩) (reconstruct frequency f)
  exact h

theorem representative_coefficientMap {n : ℕ} (frequency : Fin n → ℝ) (c : Fin n → ℂ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    representative frequency ((coefficientMap frequency).rangeRestrict c) t =
      ExponentialSumEstimates.exponentialSum frequency c t :=
  representative_eq_value frequency _ ht

/-- Evaluation at an interval point is a complex linear functional. -/
def evaluation {n : ℕ} (frequency : Fin n → ℝ) (t : UnitInterval) :
    Space frequency →ₗ[ℂ] ℂ where
  toFun f := f t
  map_add' f g := rfl
  map_smul' a f := rfl

/-- Multiplying coefficients by their purely imaginary frequencies. -/
def coefficientDerivative {n : ℕ} (frequency : Fin n → ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun c j := (Complex.I * (frequency j : ℂ)) * c j
  map_add' c z := by ext j; simp [mul_add]
  map_smul' a c := by ext j; simp [mul_comm, mul_left_comm]

/-- Differentiation on the actual finite-dimensional range. -/
def derivative {n : ℕ} (frequency : Fin n → ℝ) : Space frequency →ₗ[ℂ] Space frequency :=
  (coefficientMap frequency).rangeRestrict.comp
    ((coefficientDerivative frequency).comp (coefficients frequency))

theorem hasDerivAt_exponentialSum {n : ℕ} (frequency : Fin n → ℝ) (c : Fin n → ℂ) (t : ℝ) :
    HasDerivAt (ExponentialSumEstimates.exponentialSum frequency c)
      (ExponentialSumEstimates.exponentialSum frequency (coefficientDerivative frequency c) t) t := by
  convert ExponentialSumEstimates.hasDerivAt_exponentialSum frequency c t using 1
  unfold ExponentialSumEstimates.exponentialSum
  apply Finset.sum_congr rfl
  intro j _
  change (Complex.I * (frequency j : ℂ)) * c j * _ = _
  ring

/-- The representative has the derivative prescribed by the endomorphism,
including the one-sided meanings at both endpoints. -/
theorem hasDerivWithinAt_representative {n : ℕ} (frequency : Fin n → ℝ)
    (f : Space frequency) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (representative frequency f)
      (representative frequency (derivative frequency f) t) (Icc (0 : ℝ) 1) t := by
  have h := (hasDerivAt_exponentialSum frequency (coefficients frequency f) t).hasDerivWithinAt
    (s := Icc (0 : ℝ) 1)
  have he : representative frequency (derivative frequency f) t =
      ExponentialSumEstimates.exponentialSum frequency
        (coefficientDerivative frequency (coefficients frequency f)) t :=
    representative_coefficientMap frequency _ ht
  rw [he]
  exact h

/-- Differentiation is independent of the chosen coefficient representative. -/
theorem derivative_of_coefficients {n : ℕ} (frequency : Fin n → ℝ) (c : Fin n → ℂ) :
    derivative frequency ((coefficientMap frequency).rangeRestrict c) =
      (coefficientMap frequency).rangeRestrict (coefficientDerivative frequency c) := by
  apply toContinuousMap_injective frequency
  ext t
  have h₁ := hasDerivWithinAt_representative frequency
    ((coefficientMap frequency).rangeRestrict c) t.property
  have h₁' := h₁.congr_of_mem
    (fun u hu => (representative_coefficientMap frequency c hu).symm) t.property
  have h₂ := (hasDerivAt_exponentialSum frequency c t.val).hasDerivWithinAt
    (s := Icc (0 : ℝ) 1)
  have hu := uniqueDiffOn_Icc_zero_one t.val t.property
  have he := (h₁'.derivWithin hu).symm.trans (h₂.derivWithin hu)
  rw [representative_eq_value frequency _ t.property] at he
  exact he

theorem finrank_le {n : ℕ} (frequency : Fin n → ℝ) :
    Module.finrank ℂ (Space frequency) ≤ n := by
  change Module.finrank ℂ (coefficientMap frequency).range ≤ n
  simpa only [Module.finrank_fin_fun] using (coefficientMap frequency).finrank_range_le

/-- The original exponential generators, allowing repeated frequencies. -/
def generator {n : ℕ} (frequency : Fin n → ℝ) (j : Fin n) : Space frequency :=
  (coefficientMap frequency).rangeRestrict (Pi.single j 1)

theorem derivative_generator {n : ℕ} (frequency : Fin n → ℝ) (j : Fin n) :
    derivative frequency (generator frequency j) =
      (Complex.I * (frequency j : ℂ)) • generator frequency j := by
  unfold generator
  rw [derivative_of_coefficients]
  have he : coefficientDerivative frequency (Pi.single j 1) =
      (Complex.I * (frequency j : ℂ)) • Pi.single j 1 := by
    ext k
    by_cases hk : k = j
    · subst k; simp [coefficientDerivative]
    · simp [coefficientDerivative, Pi.single_apply, hk]
  rw [he, map_smul]

theorem coefficient_expansion {n : ℕ} (frequency : Fin n → ℝ) (c : Fin n → ℂ) :
    (coefficientMap frequency).rangeRestrict c = ∑ j, c j • generator frequency j := by
  classical
  have hc : c = ∑ j, c j • Pi.single j (1 : ℂ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  conv_lhs => rw [hc, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact map_smul (coefficientMap frequency).rangeRestrict (c j) (Pi.single j 1)

/-- The generating exponentials span the entire function space, also when
some generators coincide. -/
theorem span_generator_eq_top {n : ℕ} (frequency : Fin n → ℝ) :
    Submodule.span ℂ (Set.range (generator frequency)) = ⊤ := by
  apply top_unique
  intro f _
  obtain ⟨c,rfl⟩ := (coefficientMap frequency).surjective_rangeRestrict f
  rw [coefficient_expansion]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

end
end LeanNumDetect.MultiTuran.ExponentialInterval
