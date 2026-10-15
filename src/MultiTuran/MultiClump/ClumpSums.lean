import MultiTuran.MultiClump.ClumpRiemann
import NumDetect.Segmented.ClumpBasics
import Mathlib.Algebra.Order.Chebyshev

/-! # Actual clump sums, their cardinalities, energies, and Riemann norming

Each label fiber is reindexed by its true cardinality, without padding.
The filtered coefficients on the original node family agree exactly with
that local exponential sum. All energy statements concern the project's
actual integrals and sampled sums.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Set MeasureTheory

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

/-- The actual number of indices in a label fiber. -/
def clumpSize {n A : ℕ} (label : Fin n → Fin A) (a : Fin A) : ℕ :=
  Fintype.card {j : Fin n // label j = a}

/-- Reindex one fiber by its actual size, rather than by a padded size. -/
def clumpEnumeration {n A : ℕ} (label : Fin n → Fin A) (a : Fin A) :
    Fin (clumpSize label a) ≃ {j : Fin n // label j = a} :=
  (Fintype.equivFin _).symm

def clumpNodes {d n A : ℕ} (Y : Fin n → Point d) (label : Fin n → Fin A) (a : Fin A) :
    Fin (clumpSize label a) → Point d := fun i => Y (clumpEnumeration label a i).val

def clumpCoefficients {n A : ℕ} (c : Fin n → ℂ) (label : Fin n → Fin A) (a : Fin A) :
    Fin (clumpSize label a) → ℂ := fun i => c (clumpEnumeration label a i).val

theorem clumpEnumeration_label {n A : ℕ} (label : Fin n → Fin A)
    (a : Fin A) (i : Fin (clumpSize label a)) :
    label (clumpEnumeration label a i).val = a := (clumpEnumeration label a i).property

theorem clumpSize_eq_filter_card {n A : ℕ} (label : Fin n → Fin A) (a : Fin A) :
    clumpSize label a = (Finset.univ.filter fun j => label j = a).card := by
  classical
  simp [clumpSize, Fintype.card_subtype]

/-- Slot injectivity bounds each actual fiber by the largest clump size. -/
theorem clumpSize_le {d n A nStar : ℕ} {Y : Fin n → Point d}
    (C : NumDetect.ClumpSlots (A := A) (nStar := nStar) Y) (a : Fin A) :
    clumpSize C.label a ≤ nStar := by
  let f : {j : Fin n // C.label j = a} → Fin nStar := fun j => C.slot j.val
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply C.injective
    exact Prod.ext (i.property.trans j.property.symm) hij
  simpa [clumpSize] using Fintype.card_le_of_injective f hf

theorem clumpSize_pos_of_surjective {n A : ℕ} (label : Fin n → Fin A)
    (hsurj : Function.Surjective label) (a : Fin A) : 0 < clumpSize label a := by
  obtain ⟨j,hj⟩ := hsurj a
  exact Fintype.card_pos_iff.mpr ⟨⟨j,hj⟩⟩

theorem clumpCount_le_nodeCount {n A : ℕ} (label : Fin n → Fin A)
    (hsurj : Function.Surjective label) : A ≤ n := by
  simpa using Fintype.card_le_of_surjective label hsurj

/-- Filtering the original coefficients is exactly the reindexed clump sum. -/
theorem exponentialSum_filtered_eq_clump {d n A : ℕ} (Y : Fin n → Point d)
    (label : Fin n → Fin A) (a : Fin A) (c : Fin n → ℂ) (t : Point d) :
    exponentialSum Y (fun j => if label j = a then c j else 0) t =
      exponentialSum (clumpNodes Y label a) (clumpCoefficients c label a) t := by
  classical
  unfold exponentialSum clumpNodes clumpCoefficients
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_subtype_eq_sum_filter]
  simpa only [Finset.subtype_univ] using
    ((clumpEnumeration label a).sum_comp
      (fun j : {j : Fin n // label j = a} =>
        c j.val * Complex.exp (Complex.I * ((∑ q, t q * Y j.val q : ℝ) : ℂ)))).symm

/-- No cancellation assumption is needed for the exact decomposition. -/
theorem exponentialSum_eq_sum_clumps {d n A : ℕ} (Y : Fin n → Point d)
    (label : Fin n → Fin A) (c : Fin n → ℂ) (t : Point d) :
    exponentialSum Y c t =
      ∑ a : Fin A, exponentialSum Y (fun j => if label j = a then c j else 0) t := by
  classical
  symm
  unfold exponentialSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul]

/-- Pointwise finite Cauchy--Schwarz with the actual number of clumps. -/
theorem exponentialSum_norm_sq_le_clump_sum {d n A : ℕ} (Y : Fin n → Point d)
    (label : Fin n → Fin A) (c : Fin n → ℂ) (t : Point d) :
    ‖exponentialSum Y c t‖^2 ≤ (A : ℝ)*
      ∑ a : Fin A, ‖exponentialSum Y (fun j => if label j = a then c j else 0) t‖^2 := by
  rw [exponentialSum_eq_sum_clumps Y label c t]
  calc
    _ ≤ (∑ a : Fin A, ‖exponentialSum Y (fun j => if label j = a then c j else 0) t‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa using (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin A)))
        (f := fun a => ‖exponentialSum Y (fun j => if label j = a then c j else 0) t‖))

/-- Integrating the actual pointwise Cauchy--Schwarz inequality. -/
theorem setEnergy_le_clump_sum {d n A : ℕ} (Y : Fin n → Point d)
    (label : Fin n → Fin A) (c : Fin n → ℂ) (S : Set (Point d)) (hS : IsCompact S) :
    setEnergy Y c S ≤ (A : ℝ)*
      ∑ a : Fin A, setEnergy Y (fun j => if label j = a then c j else 0) S := by
  classical
  have hi (a : Fin A) : IntegrableOn
      (fun t => ‖exponentialSum Y (fun j => if label j = a then c j else 0) t‖^2) S :=
    exponentialSum_energy_integrableOn Y _ hS
  have hsum : IntegrableOn
      (fun t => ∑ a : Fin A, ‖exponentialSum Y (fun j => if label j = a then c j else 0) t‖^2) S :=
    integrable_finsetSum _ (fun a _ => hi a)
  unfold setEnergy
  calc
    _ ≤ ∫ t in S, (A : ℝ)*
        ∑ a : Fin A, ‖exponentialSum Y (fun j => if label j = a then c j else 0) t‖^2 := by
      apply setIntegral_mono_on (exponentialSum_energy_integrableOn Y c hS)
        (hsum.const_mul (A : ℝ)) hS.measurableSet
      intro t _
      exact exponentialSum_norm_sq_le_clump_sum Y label c t
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum]
      exact fun a _ => hi a

theorem continuousEnergy_le_clump_sum {d n A : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (label : Fin n → Fin A) (c : Fin n → ℂ) :
    continuousEnergy G Y c ≤ (A : ℝ)*
      ∑ a : Fin A, continuousEnergy G Y (fun j => if label j = a then c j else 0) :=
  setEnergy_le_clump_sum Y label c G.thickening G.thickening_isCompact

/-- One clump has uniform norming under the common `nStar` threshold, using
its actual cardinality and a center in that same clump. -/
theorem filtered_clump_norming_half {d n A nStar : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (C : NumDetect.ClumpSlots (A := A) (nStar := nStar) Y)
    (hd : 2 ≤ d) (hsurj : Function.Surjective C.label) {τ : ℝ} (hτ : 0 ≤ τ)
    (hsame : ∀ i j, C.label i = C.label j → ∀ q, |Y i q-Y j q| ≤ τ)
    (hcondition : 48*(d : ℝ)*(Real.pi/2)^(2*d)*(G.rowCount : ℝ)*
      ((nStar : ℝ)^(4*d+5)/(G.minThickLength : ℝ)^(d+1)+
        (nStar : ℝ)^(4*d+1)*τ/(G.minThickLength : ℝ)^d) ≤ 1)
    (a : Fin A) (c : Fin n → ℂ) :
    (1/2 : ℝ)*continuousEnergy G Y (fun j => if C.label j = a then c j else 0) ≤
      discreteEnergy G Y (fun j => if C.label j = a then c j else 0) := by
  classical
  obtain ⟨j,hj⟩ := hsurj a
  have hv : 0 < clumpSize C.label a := clumpSize_pos_of_surjective C.label hsurj a
  have hvle : (clumpSize C.label a : ℝ) ≤ nStar := by exact_mod_cast clumpSize_le C a
  have hY : ∀ i q, |clumpNodes Y C.label a i q-Y j q| ≤ τ := by
    intro i q
    exact hsame (clumpEnumeration C.label a i).val j
      ((clumpEnumeration_label C.label a i).trans hj.symm) q
  have hL : (0 : ℝ) < G.minThickLength := by exact_mod_cast minThickLength_pos G
  have hpow₁ : (clumpSize C.label a : ℝ)^(4*d+5) ≤ (nStar : ℝ)^(4*d+5) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hvle _
  have hpow₂ : (clumpSize C.label a : ℝ)^(4*d+1) ≤ (nStar : ℝ)^(4*d+1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hvle _
  have hlocal : 48*(d : ℝ)*(Real.pi/2)^(2*d)*(G.rowCount : ℝ)*
      ((clumpSize C.label a : ℝ)^(4*d+5)/(G.minThickLength : ℝ)^(d+1)+
        (clumpSize C.label a : ℝ)^(4*d+1)*τ/(G.minThickLength : ℝ)^d) ≤ 1 := by
    apply le_trans _ hcondition
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add
    · exact div_le_div_of_nonneg_right hpow₁ (by positivity)
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow₂ hτ) (by positivity)
  have hnorm := continuousNorming_half_of_centered_frequency_bound G
    (clumpNodes Y C.label a) (Y j) hd hv hτ hY hlocal
    (clumpCoefficients c C.label a)
  have hcont : continuousEnergy G Y (fun j => if C.label j = a then c j else 0) =
      continuousEnergy G (clumpNodes Y C.label a) (clumpCoefficients c C.label a) := by
    unfold continuousEnergy setEnergy
    simp_rw [exponentialSum_filtered_eq_clump]
  have hdisc : discreteEnergy G Y (fun j => if C.label j = a then c j else 0) =
      discreteEnergy G (clumpNodes Y C.label a) (clumpCoefficients c C.label a) := by
    unfold discreteEnergy
    simp_rw [exponentialSum_filtered_eq_clump]
  rw [hcont,hdisc]
  exact hnorm

end
end LeanNumDetect.MultiTuran.MultiClump
