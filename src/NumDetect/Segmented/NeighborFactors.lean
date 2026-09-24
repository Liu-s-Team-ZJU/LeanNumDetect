import NumDetect.Basic
import NumDetect.Segmented.Polynomial
import General.Finite.FiniteRealGeometry
import SegmentedVDM.Quantization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators ENNReal NNReal

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- `lem:freq_quantization` in the manuscript, with its natural-number
frequency step. The scale hypothesis itself forces `D > 0`. -/
theorem frequency_quantization_manuscript {d D : ℕ} {p q : ℝ≥0∞}
    (hpq : ENNReal.HolderConjugate p q) {α : ℝ} (hα : 0 < α)
    (u : Fin d → ℝ) (hu : ∀ j, u j ∈ Set.Ioc (-Real.pi) Real.pi)
    (hun : 0 < LeanNumDetect.lpNorm q u)
    (_huUpper : LeanNumDetect.lpNorm q u ≤
      Real.pi / (2 * (D : ℝ) * (d : ℝ) ^ p.toReal⁻¹))
    (huα : LeanNumDetect.lpNorm q u ≤ 2 * Real.pi * α)
    (hαD : 2 * Real.pi * α ≤
      Real.pi / (2 * (D : ℝ) * (d : ℝ) ^ p.toReal⁻¹)) :
    ∃ k : Fin d → ℤ,
      LeanNumDetect.lpNorm p (fun j => (k j : ℝ)) ≤ 1 / (2 * (D : ℝ) * α) ∧
      LeanNumDetect.lpNorm q u / (4 * α) ≤
        (D : ℝ) * |∑ j, (k j : ℝ) * u j| ∧
      (D : ℝ) * |∑ j, (k j : ℝ) * u j| ≤ Real.pi ∧
      Real.sqrt 2 / (2 * Real.pi * α) * LeanNumDetect.lpNorm q u ≤
        ‖1 - Complex.exp (Complex.I *
          (((D : ℝ) * ∑ j, (k j : ℝ) * u j : ℝ) : ℂ))‖ := by
  have hD : 0 < D := by
    by_contra h
    have hzero : D = 0 := Nat.eq_zero_of_not_pos h
    subst D
    have hnonpos : 2 * Real.pi * α ≤ (0 : ℝ) := by simpa using hαD
    have hpos : (0 : ℝ) < 2 * Real.pi * α := by positivity
    exact (not_lt_of_ge hnonpos) hpos
  exact SegmentedVDM.frequency_quantization_of_shortest_representative hpq
    (by exact_mod_cast hD) hα u hu hun huα hαD

/-- The coordinatewise shortest representative of an angular difference. -/
def wrappedCoordinateDifference (u v : ℝ) : ℝ :=
  if Real.pi < u - v then u - v - 2 * Real.pi
  else if u - v ≤ -Real.pi then u - v + 2 * Real.pi
  else u - v

/-- The integer number of periods removed by `wrappedCoordinateDifference`. -/
def wrappedCoordinateTurns (u v : ℝ) : ℤ :=
  if Real.pi < u - v then 1
  else if u - v ≤ -Real.pi then -1
  else 0

theorem sub_eq_wrappedCoordinateDifference_add
    (u v : ℝ) :
    u - v =
      wrappedCoordinateDifference u v +
        2 * Real.pi * wrappedCoordinateTurns u v := by
  unfold wrappedCoordinateDifference wrappedCoordinateTurns
  split_ifs <;> push_cast <;> ring

/-- Coordinatewise shortest representative of a torus difference. -/
def wrappedDifference {d : ℕ} (u v : Point d) : Point d :=
  fun k => wrappedCoordinateDifference (u k) (v k)

theorem sub_eq_wrappedDifference_add
    {d : ℕ} (u v : Point d) (k : Fin d) :
    u k - v k =
      wrappedDifference u v k +
        2 * Real.pi * wrappedCoordinateTurns (u k) (v k) :=
  sub_eq_wrappedCoordinateDifference_add _ _

theorem abs_wrappedCoordinateDifference
    {u v : ℝ}
    (hu : -Real.pi < u ∧ u ≤ Real.pi)
    (hv : -Real.pi < v ∧ v ≤ Real.pi) :
    |wrappedCoordinateDifference u v| =
      periodicCoordinateDistance u v := by
  unfold wrappedCoordinateDifference periodicCoordinateDistance
  have hdiffLower : -2 * Real.pi < u - v := by linarith
  have hdiffUpper : u - v < 2 * Real.pi := by linarith
  by_cases hupper : Real.pi < u - v
  · rw [if_pos hupper]
    have hpos : 0 < u - v := hupper.trans' Real.pi_pos
    have hwrap : u - v - 2 * Real.pi < 0 := by linarith
    rw [abs_of_pos hpos, abs_of_nonpos hwrap.le, min_eq_right]
    · ring
    · linarith
  · rw [if_neg hupper]
    by_cases hlower : u - v ≤ -Real.pi
    · rw [if_pos hlower]
      have hneg : u - v ≤ 0 := hlower.trans (neg_nonpos.mpr Real.pi_pos.le)
      have hwrap : 0 < u - v + 2 * Real.pi := by linarith
      rw [abs_of_nonpos hneg, abs_of_pos hwrap, min_eq_right]
      · ring
      · linarith
    · rw [if_neg hlower]
      have hlow : -Real.pi < u - v := lt_of_not_ge hlower
      have habs : |u - v| ≤ Real.pi := (abs_le).2 ⟨by linarith, by linarith⟩
      rw [min_eq_left (by linarith)]

theorem l1Norm_wrappedDifference
    {d : ℕ} {u v : Point d}
    (hu : InAngularCube u) (hv : InAngularCube v) :
    l1Norm (wrappedDifference u v) = periodicL1Distance u v := by
  unfold l1Norm periodicL1Distance
  apply Finset.sum_congr rfl
  intro k _
  exact abs_wrappedCoordinateDifference (hu k) (hv k)

theorem l1Norm_wrappedDifference_le
    {d : ℕ} {u v : Point d}
    (hu : InAngularCube u) (hv : InAngularCube v) :
    l1Norm (wrappedDifference u v) ≤
      d * periodicLInfDistance u v := by
  rw [l1Norm_wrappedDifference hu hv]
  unfold periodicL1Distance periodicLInfDistance
  calc
    (∑ k, periodicCoordinateDistance (u k) (v k))
        ≤ ∑ _k : Fin d, ‖fun k => periodicCoordinateDistance (u k) (v k)‖ :=
      Finset.sum_le_sum fun k _ =>
        (le_abs_self _).trans (by
          simpa only [Real.norm_eq_abs] using
            norm_le_pi_norm
              (fun k => periodicCoordinateDistance (u k) (v k)) k)
    _ = d * ‖fun k => periodicCoordinateDistance (u k) (v k)‖ := by simp

/-- Integer frequencies make the canonical polynomial periodic, so angular
evaluation on a difference agrees with evaluation on its shortest representative. -/
theorem SegmentedPolynomial.angularValue_sub_eq_wrappedDifference
    {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (u v : Point d) :
    P.angularValue (u - v) = P.angularValue (wrappedDifference u v) := by
  classical
  rw [SegmentedPolynomial.angularValue_eq_angularTrigPolynomial,
    SegmentedPolynomial.angularValue_eq_angularTrigPolynomial]
  unfold angularTrigPolynomial
  apply Finset.sum_congr rfl
  intro a _
  let z : ℤ :=
    ∑ k, segmentedPolynomialFrequency d m r D a k *
      wrappedCoordinateTurns (u k) (v k)
  have hphase :
      (∑ k, (segmentedPolynomialFrequency d m r D a k : ℝ) *
          (u - v) k) =
        (∑ k, (segmentedPolynomialFrequency d m r D a k : ℝ) *
          wrappedDifference u v k) +
        2 * Real.pi * (z : ℝ) := by
    simp only [Pi.sub_apply, sub_eq_wrappedDifference_add]
    dsimp [z]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  congr 1
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨z, ?_⟩
  rw [hphase]
  push_cast
  ring


theorem periodicMinimumL1Separation_le
    {d n : ℕ} {x : Fin n → Point d} (hn : 2 ≤ n)
    {i j : Fin n} (hij : i ≠ j) :
    periodicMinimumL1Separation x hn ≤ periodicL1Distance (x i) (x j) := by
  unfold periodicMinimumL1Separation minimumOverDistinctPairs
  exact Finset.inf'_le
    (fun ij : Fin n × Fin n => periodicL1Distance (x ij.1) (x ij.2))
    (by
      change (i, j) ∈ distinctPairs n
      rw [distinctPairs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hij⟩)

theorem segmented_periodicMinimumL1Separation_pos
    {d n : ℕ} (μ : AtomicMeasure d n) (hn : 2 ≤ n)
    (hcube : ∀ j, InAngularCube (μ.node j)) :
    0 < periodicMinimumL1Separation μ.node hn := by
  rw [periodicMinimumL1Separation, minimumOverDistinctPairs,
    Finset.lt_inf'_iff]
  intro ij hij
  have hne : ij.1 ≠ ij.2 := by
    simpa [distinctPairs] using hij
  obtain ⟨k, hk⟩ : ∃ k, μ.node ij.1 k ≠ μ.node ij.2 k := by
    by_contra h
    apply hne
    apply μ.node_injective
    funext k
    exact not_ne_iff.mp (not_exists.mp h k)
  unfold periodicL1Distance
  apply Finset.sum_pos'
  · intro k _
    rw [← abs_wrappedCoordinateDifference (hcube ij.1 k) (hcube ij.2 k)]
    exact abs_nonneg _
  · refine ⟨k, Finset.mem_univ k, ?_⟩
    unfold periodicCoordinateDistance
    rw [lt_min_iff]
    constructor
    · exact abs_pos.mpr (sub_ne_zero.mpr hk)
    · rw [sub_pos, abs_lt]
      constructor <;>
        linarith [(hcube ij.1 k).1, (hcube ij.1 k).2,
          (hcube ij.2 k).1, (hcube ij.2 k).2, Real.pi_pos]


end
end NumDetect
end LeanNumDetect

/-! Canonical two-point factors for Appendix B's neighbor interpolation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section

namespace SegmentedPolynomial

/-- A single canonical coarse-frequency atom. -/
def coarseMonomial {d K D : ℕ} (hD : 0 < D)
    (a : SegmentedIndex d 0 K) (c : ℂ) :
    SegmentedPolynomial d 0 K D :=
  ⟨hD, fun b => if b = a then c else 0⟩

@[simp] theorem angularValue_coarseMonomial {d K D : ℕ} (hD : 0 < D)
    (a : SegmentedIndex d 0 K) (c : ℂ) (y : Point d) :
    (coarseMonomial hD a c).angularValue y =
      c * Complex.exp
        (Complex.I * ((∑ j, ((D * (a j).1 : ℕ) : ℝ) * y j : ℝ) : ℂ)) := by
  classical
  rw [angularValue_eq_angularTrigPolynomial]
  unfold angularTrigPolynomial
  simp only [coarseMonomial]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ a]
  simp [segmentedPolynomialFrequency]

@[simp] theorem mass_coarseMonomial {d K D : ℕ} (hD : 0 < D)
    (a : SegmentedIndex d 0 K) (c : ℂ) :
    (coarseMonomial hD a c).mass = ‖c‖ := by
  classical
  change (∑ b : SegmentedIndex d 0 K,
    ‖if b = a then c else 0‖) = ‖c‖
  calc
    _ = ∑ b : SegmentedIndex d 0 K,
        if b = a then ‖c‖ else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          split_ifs <;> simp
    _ = ‖c‖ := by rw [Finset.sum_ite_eq' Finset.univ a]; simp

@[simp] theorem angularValue_add {d m r D : ℕ}
    (P Q : SegmentedPolynomial d m r D) (y : Point d) :
    (P + Q).angularValue y = P.angularValue y + Q.angularValue y :=
  eval_add P Q _

theorem mass_add_le {d m r D : ℕ}
    (P Q : SegmentedPolynomial d m r D) :
    (P + Q).mass ≤ P.mass + Q.mass := by
  unfold mass
  calc
    (∑ a, ‖(P + Q).coeff a‖) ≤ ∑ a, (‖P.coeff a‖ + ‖Q.coeff a‖) :=
      Finset.sum_le_sum fun a _ => norm_add_le _ _
    _ = P.mass + Q.mass := by rw [Finset.sum_add_distrib]; rfl

/-- Positive and negative parts of an integer vector as canonical coarse
indices. -/
def coarsePositiveIndex {d K : ℕ} (k : Fin d → ℤ)
    (hk : ∀ j, (k j).natAbs ≤ K) : SegmentedIndex d 0 K :=
  fun j => (⟨(k j).toNat, by
      have hle : (k j : ℤ) ≤ (K : ℤ) :=
        (Int.le_natAbs (a := k j)).trans (by exact_mod_cast hk j)
      exact Nat.lt_succ_of_le (Int.toNat_le.mpr hle)⟩,
    ⟨0, by omega⟩)

def coarseNegativeIndex {d K : ℕ} (k : Fin d → ℤ)
    (hk : ∀ j, (k j).natAbs ≤ K) : SegmentedIndex d 0 K :=
  fun j => (⟨(-k j).toNat, by
      have hkneg : (-k j).natAbs ≤ K := by simpa using hk j
      have hle : (-k j : ℤ) ≤ (K : ℤ) :=
        (Int.le_natAbs (a := -k j)).trans (by exact_mod_cast hkneg)
      exact Nat.lt_succ_of_le (Int.toNat_le.mpr hle)⟩,
    ⟨0, by omega⟩)

/-- The recentered two-point quotient, with equal frequencies already merged
by the canonical coefficient function. -/
def twoPointRecentered {d K D : ℕ} (hD : 0 < D)
    (k : Fin d → ℤ) (hk : ∀ j, (k j).natAbs ≤ K) (z : ℂ) :
    SegmentedPolynomial d 0 K D :=
  coarseMonomial hD (coarsePositiveIndex k hk) (1 - z)⁻¹ +
    coarseMonomial hD (coarseNegativeIndex k hk) (-z / (1 - z))

theorem angularValue_twoPointRecentered {d K D : ℕ} (hD : 0 < D)
    (k : Fin d → ℤ) (hk : ∀ j, (k j).natAbs ≤ K)
    (z : ℂ) (y : Point d) :
    (twoPointRecentered hD k hk z).angularValue y =
      Complex.exp (Complex.I *
        (((D : ℝ) * ∑ j, ((-k j).toNat : ℝ) * y j : ℝ) : ℂ)) *
        ((Complex.exp (Complex.I *
          (((D : ℝ) * ∑ j, (k j : ℝ) * y j : ℝ) : ℂ)) - z) /
          (1 - z)) := by
  classical
  have htoNat (j : Fin d) : ((k j).toNat : ℝ) =
      ((-k j).toNat : ℝ) + (k j : ℝ) := by
    have h : ((k j).toNat : ℤ) = ((-k j).toNat : ℤ) + k j := by omega
    exact_mod_cast h
  have hθp : (∑ j, ((D * (k j).toNat : ℕ) : ℝ) * y j) =
      (D : ℝ) * ∑ j, ((-k j).toNat : ℝ) * y j +
        (D : ℝ) * ∑ j, (k j : ℝ) * y j := by
    calc
      _ = ∑ j, ((D : ℝ) * ((-k j).toNat : ℝ) * y j +
          (D : ℝ) * (k j : ℝ) * y j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Nat.cast_mul, htoNat j]
            ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        simp only [mul_assoc]
  have hθm : (∑ j, ((D * (-k j).toNat : ℕ) : ℝ) * y j) =
      (D : ℝ) * ∑ j, ((-k j).toNat : ℝ) * y j := by
    simp only [Nat.cast_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [twoPointRecentered, angularValue_add]
  simp only [angularValue_coarseMonomial, coarsePositiveIndex,
    coarseNegativeIndex, Fin.val_mk, Nat.cast_mul]
  have hθp' : (∑ j, (D : ℝ) * ((k j).toNat : ℝ) * y j) =
      (D : ℝ) * ∑ j, ((-k j).toNat : ℝ) * y j +
        (D : ℝ) * ∑ j, (k j : ℝ) * y j := by
    simpa only [Nat.cast_mul] using hθp
  have hθm' : (∑ j, (D : ℝ) * ((-k j).toNat : ℝ) * y j) =
      (D : ℝ) * ∑ j, ((-k j).toNat : ℝ) * y j := by
    simpa only [Nat.cast_mul] using hθm
  rw [hθp', hθm']
  rw [show Complex.exp (Complex.I *
      (((D : ℝ) * ∑ j, ((-k j).toNat : ℝ) * y j +
        (D : ℝ) * ∑ j, (k j : ℝ) * y j : ℝ) : ℂ)) =
      Complex.exp (Complex.I *
        (((D : ℝ) * ∑ j, ((-k j).toNat : ℝ) * y j : ℝ) : ℂ)) *
      Complex.exp (Complex.I *
        (((D : ℝ) * ∑ j, (k j : ℝ) * y j : ℝ) : ℂ)) by
        rw [Complex.ofReal_add, mul_add, Complex.exp_add]]
  ring

theorem angularValue_twoPointRecentered_zero {d K D : ℕ} (hD : 0 < D)
    (k : Fin d → ℤ) (hk : ∀ j, (k j).natAbs ≤ K)
    (z : ℂ) (hz : z ≠ 1) :
    (twoPointRecentered hD k hk z).angularValue 0 = 1 := by
  rw [angularValue_twoPointRecentered]
  simp [sub_ne_zero.mpr (Ne.symm hz)]

theorem angularValue_twoPointRecentered_vanishes {d K D : ℕ} (hD : 0 < D)
    (k : Fin d → ℤ) (hk : ∀ j, (k j).natAbs ≤ K)
    (z : ℂ) (u : Point d)
    (hz : z = Complex.exp (Complex.I *
      (((D : ℝ) * ∑ j, (k j : ℝ) * u j : ℝ) : ℂ))) :
    (twoPointRecentered hD k hk z).angularValue u = 0 := by
  rw [angularValue_twoPointRecentered, hz, sub_self, zero_div, mul_zero]

theorem mass_twoPointRecentered_le {d K D : ℕ} (hD : 0 < D)
    (k : Fin d → ℤ) (hk : ∀ j, (k j).natAbs ≤ K)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (twoPointRecentered hD k hk z).mass ≤ 2 / ‖1 - z‖ := by
  unfold twoPointRecentered
  calc
    (coarseMonomial hD (coarsePositiveIndex k hk) (1 - z)⁻¹ +
      coarseMonomial hD (coarseNegativeIndex k hk) (-z / (1 - z))).mass
        ≤ (coarseMonomial hD (coarsePositiveIndex k hk) (1 - z)⁻¹).mass +
          (coarseMonomial hD (coarseNegativeIndex k hk) (-z / (1 - z))).mass :=
            mass_add_le _ _
    _ = 2 / ‖1 - z‖ := by
      simp [norm_inv, norm_div, hz, norm_sub_rev]
      ring

/-- A canonical two-point factor annihilating one nonzero neighbor, with the
quantized frequency and coefficient-mass bound of Appendix B. -/
theorem neighborNodeFactor {d D : ℕ} {p q : ENNReal}
    (hpq : ENNReal.HolderConjugate p q)
    (hD : 0 < D) (hdim : 0 < (d : ℝ) ^ p.toReal⁻¹)
    {t : ℝ} (ht : 2 * (d : ℝ) ^ p.toReal⁻¹ ≤ t)
    (u : Point d) (hun : 0 < LeanNumDetect.lpNorm q u)
    (hut : LeanNumDetect.lpNorm q u ≤ Real.pi / (D * t)) :
    ∃ P : SegmentedPolynomial d 0 ⌊t⌋₊ D,
      P.angularValue 0 = 1 ∧ P.angularValue u = 0 ∧
      P.mass ≤ Real.sqrt 2 * Real.pi /
        (D * t * LeanNumDetect.lpNorm q u) := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have htpos : 0 < t := by
    have h1 : 0 < Real.pi / (D * t) := lt_of_lt_of_le hun hut
    have h2 : 0 < D * t := (div_pos_iff_of_pos_left Real.pi_pos).mp h1
    exact pos_of_mul_pos_right h2 hDpos.le
  obtain ⟨k, hk, hden⟩ := SegmentedVDM.frequency_quantization_of_budgetScale hpq hDpos
    hdim ht u hun hut
  set z : ℂ := Complex.exp (Complex.I *
    (((D : ℝ) * ∑ j, (k j : ℝ) * u j : ℝ) : ℂ)) with hzdef
  have hzn : ‖z‖ = 1 := by simp [z, Complex.norm_exp]
  have hden' : Real.sqrt 2 * (D * t * LeanNumDetect.lpNorm q u / Real.pi) ≤
      ‖1 - z‖ := by
    have he : Real.sqrt 2 * (D * t * LeanNumDetect.lpNorm q u / Real.pi)
        = Real.sqrt 2 * D * t * LeanNumDetect.lpNorm q u / Real.pi := by ring
    rw [he, hzdef]
    exact hden
  have hzne : z ≠ 1 := by
    intro h
    have hp : 0 < Real.sqrt 2 *
        (D * t * LeanNumDetect.lpNorm q u / Real.pi) := by positivity
    simp [h] at hden'
    linarith
  have hkabs (j : Fin d) : |(k j : ℝ)| ≤ t :=
    (LeanNumDetect.lpNorm_apply_le (holderConjugate_ne_zero hpq).1
      (fun j => (k j : ℝ)) j).trans hk
  have hkK (j : Fin d) : (k j).natAbs ≤ ⌊t⌋₊ := by
    apply Nat.le_floor
    have h1 : ((k j).natAbs : ℝ) = |(k j : ℝ)| :=
      (Nat.cast_natAbs (k j)).trans Int.cast_abs
    rw [h1]
    exact hkabs j
  refine ⟨twoPointRecentered hD k hkK z, ?_, ?_, ?_⟩
  · exact angularValue_twoPointRecentered_zero hD k hkK z hzne
  · exact angularValue_twoPointRecentered_vanishes hD k hkK z u hzdef
  · have hmass := mass_twoPointRecentered_le hD k hkK z hzn
    have hpos : 0 < Real.sqrt 2 *
        (D * t * LeanNumDetect.lpNorm q u / Real.pi) := by positivity
    calc
      (twoPointRecentered hD k hkK z).mass ≤ 2 / ‖1 - z‖ := hmass
      _ ≤ 2 / (Real.sqrt 2 *
          (D * t * LeanNumDetect.lpNorm q u / Real.pi)) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hden'
      _ = Real.sqrt 2 * Real.pi /
          (D * t * LeanNumDetect.lpNorm q u) := by
        have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        field_simp
        nlinarith

end SegmentedPolynomial
end
end NumDetect
end LeanNumDetect

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LeanNumDetect
namespace NumDetect

noncomputable section
namespace SegmentedPolynomial

theorem segmentedNeighborProduct
    {d q D : ℕ} {T Δ : ℝ}
    (hT : 2 ≤ T) (hD : 0 < D) (hΔ : 0 < Δ)
    (u : Fin q → Point d)
    (hΔu : ∀ i, Δ ≤ l1Norm (u i))
    (hu : ∀ i, l1Norm (u i) ≤ Real.pi / (2 * D))
    (hscale : T * D * Δ ≤ Real.pi) :
    ∃ P : SegmentedPolynomial d 0 (q * ⌊T⌋₊) D,
      P.angularValue 0 = 1 ∧
      (∀ i, P.angularValue (u i) = 0) ∧
      P.mass ≤
        (Real.sqrt 2 / (T * D * Δ / Real.pi)) ^ q := by
  classical
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hpq : ENNReal.HolderConjugate ⊤ 1 := inferInstance
  have hdim : (0 : ℝ) < (d : ℝ) ^ ((⊤ : ENNReal).toReal)⁻¹ := by simp
  have hL1 (i : Fin q) : LeanNumDetect.lpNorm 1 (u i) = l1Norm (u i) := by
    rw [LeanNumDetect.lpNorm_one]
    rfl
  have hLpos (i : Fin q) : 0 < LeanNumDetect.lpNorm 1 (u i) := by
    rw [hL1 i]
    exact lt_of_lt_of_le hΔ (hΔu i)
  have hLΔ (i : Fin q) : Δ ≤ LeanNumDetect.lpNorm 1 (u i) := by
    rw [hL1 i]
    exact hΔu i
  have htu (i : Fin q) : 2 ≤ Real.pi / (D * LeanNumDetect.lpNorm 1 (u i)) := by
    rw [hL1 i]
    apply (le_div_iff₀ (mul_pos hDR (lt_of_lt_of_le hΔ (hΔu i)))).2
    have h2 : l1Norm (u i) * (2 * (D : ℝ)) ≤ Real.pi :=
      (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hDR)).mp (hu i)
    have he : 2 * ((D : ℝ) * l1Norm (u i)) = l1Norm (u i) * (2 * (D : ℝ)) := by ring
    rw [he]
    exact h2
  choose F hF1 hF0 hFm using fun i =>
    neighborNodeFactor hpq hD hdim
      (t := min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))))
      (by
        have h1 : 2 * (d : ℝ) ^ ((⊤ : ENNReal).toReal)⁻¹ = 2 := by simp
        rw [h1]
        exact le_min hT (htu i))
      (u i) (hLpos i)
      (by
        have h1 := min_le_right T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i)))
        have h2 : min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
            (D * LeanNumDetect.lpNorm 1 (u i)) ≤ Real.pi :=
          (le_div_iff₀ (mul_pos hDR (hLpos i))).mp h1
        have h3 : LeanNumDetect.lpNorm 1 (u i) *
            (D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))))
            = min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
              (D * LeanNumDetect.lpNorm 1 (u i)) := by ring
        have h3' : LeanNumDetect.lpNorm 1 (u i) *
            (D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i)))) ≤ Real.pi := by
          rw [h3]
          exact h2
        have hminpos : 0 < D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) :=
          mul_pos hDR (lt_min_iff.mpr ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hT,
            div_pos Real.pi_pos (mul_pos hDR (hLpos i))⟩)
        exact (le_div_iff₀ hminpos).2 h3')
  have htd (i : Fin q) : T * D * Δ ≤
      D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
        LeanNumDetect.lpNorm 1 (u i) := by
    have h0 : T * D * Δ ≤ min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) * D *
        LeanNumDetect.lpNorm 1 (u i) := by
      rw [min_mul_of_nonneg _ _ hDR.le,
        min_mul_of_nonneg _ _ (hLpos i).le]
      apply le_min
      · have h := hLΔ i
        gcongr
      · have he : Real.pi / (D * LeanNumDetect.lpNorm 1 (u i)) * D *
            LeanNumDetect.lpNorm 1 (u i) = Real.pi := by
          rw [mul_assoc, div_mul_cancel₀ Real.pi (mul_ne_zero hDR.ne' (hLpos i).ne')]
        rwa [he]
    have he : D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
        LeanNumDetect.lpNorm 1 (u i)
        = min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) * D *
          LeanNumDetect.lpNorm 1 (u i) := by ring
    rw [he]
    exact h0
  have hfac (i : Fin q) : Real.sqrt 2 * Real.pi /
      (D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) * LeanNumDetect.lpNorm 1 (u i))
      ≤ Real.sqrt 2 / (T * D * Δ / Real.pi) := by
    have hnum : 0 ≤ Real.sqrt 2 * Real.pi := by positivity
    have hTDΔpos : 0 < T * D * Δ :=
      mul_pos (mul_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hT) hDR) hΔ
    have hdenpos : 0 < D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
        LeanNumDetect.lpNorm 1 (u i) :=
      mul_pos (mul_pos hDR (lt_min_iff.mpr ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hT,
        div_pos Real.pi_pos (mul_pos hDR (hLpos i))⟩)) (hLpos i)
    calc
      Real.sqrt 2 * Real.pi /
          (D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
            LeanNumDetect.lpNorm 1 (u i))
          ≤ Real.sqrt 2 * Real.pi / (T * D * Δ) :=
        div_le_div_of_nonneg_left hnum hTDΔpos (htd i)
      _ = Real.sqrt 2 / (T * D * Δ / Real.pi) := by
        field_simp [(hLpos i).ne', hDR.ne', hΔ.ne',
          (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hT).ne'] <;> try ring
  have hpos (i : Fin q) : 0 ≤ Real.sqrt 2 * Real.pi /
      (D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) * LeanNumDetect.lpNorm 1 (u i)) := by
    refine div_nonneg (by positivity) ?_
    have hmin : 0 ≤ min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) :=
      le_min (le_of_lt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hT))
        (div_nonneg Real.pi_pos.le (mul_nonneg hDR.le (hLpos i).le))
    exact mul_nonneg (mul_nonneg hDR.le hmin) (hLpos i).le
  let Q (i : Fin q) : SegmentedPolynomial d 0 ⌊T⌋₊ D :=
    (F i).widen le_rfl (Nat.floor_mono (min_le_left _ _)) hD
  have hqD : 0 * q < D := by simpa using hD
  let P : SegmentedPolynomial d 0 (q * ⌊T⌋₊) D :=
    (SegmentedPolynomial.prod q Q hqD).widen (by simp)
      (by simp [Nat.mul_comm]) hD
  have hQ (x : Point d) : P.angularValue x = ∏ i, (F i).angularValue x := by
    simp only [P, Q, SegmentedPolynomial.angularValue_widen,
      SegmentedPolynomial.angularValue_prod]
  have hmassQ : P.mass ≤ ∏ i, (F i).mass := by
    calc
      P.mass = (SegmentedPolynomial.prod q Q hqD).mass :=
        SegmentedPolynomial.mass_widen _ _ _ _
      _ ≤ ∏ i, (Q i).mass := SegmentedPolynomial.mass_prod_le Q hqD
      _ = ∏ i, (F i).mass := by
        apply Finset.prod_congr rfl
        intro i _
        exact SegmentedPolynomial.mass_widen _ _ _ _
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hQ]
    exact Finset.prod_eq_one fun i _ => hF1 i
  · intro j
    rw [hQ]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact hF0 j
  · calc
      P.mass ≤ ∏ i : Fin q, (F i).mass := hmassQ
      _ ≤ ∏ i : Fin q, Real.sqrt 2 * Real.pi /
            (D * min T (Real.pi / (D * LeanNumDetect.lpNorm 1 (u i))) *
              LeanNumDetect.lpNorm 1 (u i)) :=
        Finset.prod_le_prod (fun i _ => (F i).mass_nonneg) (fun i _ => hFm i)
      _ ≤ ∏ _i : Fin q, Real.sqrt 2 / (T * D * Δ / Real.pi) :=
        Finset.prod_le_prod (fun i _ => hpos i) (fun i _ => hfac i)
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end SegmentedPolynomial
end
end NumDetect
end LeanNumDetect
