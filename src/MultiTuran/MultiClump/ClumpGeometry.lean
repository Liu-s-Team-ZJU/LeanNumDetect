import MultiTuran.Preliminaries.Geometry
import NumDetect.Segmented.ClumpBasics
import General.Finite.PeriodicClumpLift
import General.Fourier.PhaseEstimates

/-!
# Geometry bridges for multi-clump block bounds

The MultiTuran distances use the genuine angular quotient.  The existing
constructive clump interpolation API uses representatives in `(-π,π]`.  This
file proves the agreement on that chart, without imposing a global clump
localization condition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open LeanNumDetect.NumDetect

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

/-- On a principal angular chart the coordinate formula used by the existing
clump API is the genuine quotient distance. -/
theorem torusCoordinateDistance_eq_periodicCoordinateDistance
    {x y : ℝ} (hx : -Real.pi < x ∧ x ≤ Real.pi)
    (hy : -Real.pi < y ∧ y ≤ Real.pi) :
    torusCoordinateDistance x y = periodicCoordinateDistance x y := by
  have hupper : |x - y| ≤ 2 * Real.pi := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hcomp : torusCoordinateDistance x y ≤ 2 * Real.pi - |x - y| := by
    by_cases hxy : 0 ≤ x - y
    · have h := torusCoordinateDistance_le_winding x y 1
      have hneg : x - y - 2 * Real.pi ≤ 0 := by
        rw [abs_of_nonneg hxy] at hupper
        linarith
      simpa only [Int.cast_one, mul_one, abs_of_nonpos hneg,
        abs_of_nonneg hxy, neg_sub] using h
    · have hxy' : x - y ≤ 0 := le_of_lt (lt_of_not_ge hxy)
      have h := torusCoordinateDistance_le_winding x y (-1)
      have hpos : 0 ≤ x - y + 2 * Real.pi := by
        rw [abs_of_nonpos hxy'] at hupper
        linarith
      have he : |x - y - 2 * Real.pi * (-1 : ℤ)| = 2 * Real.pi - |x - y| := by
        rw [abs_of_nonpos hxy']
        norm_num
        rw [abs_of_nonneg hpos]
        ring
      exact he ▸ h
  apply le_antisymm
  · exact le_min (torusCoordinateDistance_le_abs x y) hcomp
  · obtain ⟨p, hp⟩ := exists_winding_eq_torusCoordinateDistance x y
    rw [hp]
    exact NumDetect.periodicCoordinateDistance_le_integerTranslate hx hy p

/-- Principal-chart conversion of the complete angular `ℓ∞` quotient metric. -/
theorem torusLInfDistance_eq_periodicLInfDistance
    {d : ℕ} {x y : Point d} (hx : InAngularCube x) (hy : InAngularCube y) :
    torusLInfDistance x y = periodicLInfDistance x y := by
  unfold torusLInfDistance periodicLInfDistance
  congr 1
  funext q
  exact torusCoordinateDistance_eq_periodicCoordinateDistance (hx q) (hy q)

/-- Principal-chart coordinate distances are nonnegative. -/
theorem periodicCoordinateDistance_nonneg_of_chart
    {x y : ℝ} (hx : -Real.pi < x ∧ x ≤ Real.pi)
    (hy : -Real.pi < y ∧ y ≤ Real.pi) :
    0 ≤ periodicCoordinateDistance x y := by
  rw [← torusCoordinateDistance_eq_periodicCoordinateDistance hx hy]
  exact torusCoordinateDistance_nonneg x y

/-- The angular `ℓ∞` metric is bounded by the periodic `ℓ1` metric used in the
short-distance product of the full-cube construction. -/
theorem torusLInfDistance_le_periodicL1Distance
    {d : ℕ} {x y : Point d} (hx : InAngularCube x) (hy : InAngularCube y) :
    torusLInfDistance x y ≤ periodicL1Distance x y := by
  apply (pi_norm_le_iff_of_nonneg (show 0 ≤ periodicL1Distance x y by
    exact Finset.sum_nonneg (fun q _ => periodicCoordinateDistance_nonneg_of_chart
      (hx q) (hy q)))).2
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg (torusCoordinateDistance_nonneg _ _),
    torusCoordinateDistance_eq_periodicCoordinateDistance (hx q) (hy q)]
  exact Finset.single_le_sum
    (fun r _ => periodicCoordinateDistance_nonneg_of_chart (hx r) (hy r))
    (Finset.mem_univ q)

/-- The manuscript separation is an admissible lower bound for every periodic
`ℓ1` pair distance in the interpolation construction. -/
theorem nodeSeparation_le_periodicL1Distance
    {d n : ℕ} {Y : Fin n → Point d} (hcube : ∀ j, InAngularCube (Y j))
    (i j : Fin n) (hij : i ≠ j) :
    nodeSeparation Y ≤ periodicL1Distance (Y i) (Y j) :=
  (nodeSeparation_le_pair Y i j hij).trans
    (torusLInfDistance_le_periodicL1Distance (hcube i) (hcube j))


/-- Canonical principal angular representative, chosen separately in every
coordinate.  This is a chart choice rather than a source localization. -/
def principalAngularPoint {d : ℕ} (x : Point d) : Point d :=
  fun q => toIocMod Real.two_pi_pos (-Real.pi) (x q)

theorem principalAngularPoint_mem {d : ℕ} (x : Point d) :
    InAngularCube (principalAngularPoint x) := by
  intro q
  have h := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) (x q)
  constructor
  · exact h.1
  · change toIocMod Real.two_pi_pos (-Real.pi) (x q) ≤ Real.pi
    linarith [h.2]

/-- The winding number of the canonical chart. -/
def principalAngularWinding {d : ℕ} (x : Point d) : Fin d → ℤ :=
  fun q => toIocDiv Real.two_pi_pos (-Real.pi) (x q)

theorem principalAngularPoint_eq_sub_winding {d : ℕ} (x : Point d) (q : Fin d) :
    principalAngularPoint x q = x q - 2 * Real.pi * principalAngularWinding x q := by
  simp only [principalAngularPoint, principalAngularWinding, toIocMod, zsmul_eq_mul]
  ring

theorem principalAngularPoint_coe {d : ℕ} (x : Point d) (q : Fin d) :
    (principalAngularPoint x q : AddCircle (2 * Real.pi)) =
      (x q : AddCircle (2 * Real.pi)) := by
  rw [principalAngularPoint_eq_sub_winding, AddCircle.coe_sub]
  have hz : ((2 * Real.pi * principalAngularWinding x q : ℝ) :
      AddCircle (2 * Real.pi)) = 0 := by
    rw [mul_comm (2 * Real.pi), ← zsmul_eq_mul, AddCircle.coe_zsmul,
      AddCircle.coe_period, smul_zero]
  rw [hz, sub_zero]

@[simp] theorem torusCoordinateDistance_principalAngularPoint {d : ℕ}
    (x y : Point d) (q : Fin d) :
    torusCoordinateDistance (principalAngularPoint x q) (principalAngularPoint y q) =
      torusCoordinateDistance (x q) (y q) := by
  unfold torusCoordinateDistance
  rw [AddCircle.coe_sub, AddCircle.coe_sub,
    principalAngularPoint_coe, principalAngularPoint_coe]

@[simp] theorem torusLInfDistance_principalAngularPoint {d : ℕ}
    (x y : Point d) :
    torusLInfDistance (principalAngularPoint x) (principalAngularPoint y) =
      torusLInfDistance x y := by
  unfold torusLInfDistance
  simp only [torusCoordinateDistance_principalAngularPoint]

@[simp] theorem nodeSeparation_principalAngularPoint {d n : ℕ}
    (Y : Fin n → Point d) :
    nodeSeparation (fun j => principalAngularPoint (Y j)) = nodeSeparation Y := by
  unfold nodeSeparation
  simp only [torusLInfDistance_principalAngularPoint]

/-- Exact periodicity of every finite integer-frequency Fourier phase under
independent choices of node representatives. -/
theorem integerFourierPhase_sub_winding {d : ℕ}
    (k p : Fin d → ℤ) (x : Point d) :
    Complex.exp (Complex.I * ((∑ q, (k q : ℝ) *
      (x q - 2 * Real.pi * p q) : ℝ) : ℂ)) =
    Complex.exp (Complex.I * ((∑ q, (k q : ℝ) * x q : ℝ) : ℂ)) := by
  have hreal : (∑ q, (k q : ℝ) * (x q - 2 * Real.pi * p q)) =
      (∑ q, (k q : ℝ) * x q) - ((∑ q, k q * p q : ℤ) : ℝ) * (2 * Real.pi) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hreal]
  have he : Complex.I * (((∑ q, (k q : ℝ) * x q) -
      ((∑ q, k q * p q : ℤ) : ℝ) * (2 * Real.pi) : ℝ) : ℂ) =
      Complex.I * ((∑ q, (k q : ℝ) * x q : ℝ) : ℂ) -
      ((∑ q, k q * p q : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

@[simp] theorem integerFourierPhase_principalAngularPoint {d : ℕ}
    (k : Fin d → ℤ) (x : Point d) :
    Complex.exp (Complex.I * ((∑ q, (k q : ℝ) * principalAngularPoint x q : ℝ) : ℂ)) =
    Complex.exp (Complex.I * ((∑ q, (k q : ℝ) * x q : ℝ) : ℂ)) := by
  simp_rw [principalAngularPoint_eq_sub_winding]
  exact integerFourierPhase_sub_winding k (principalAngularWinding x) x

@[simp] theorem angularTrigPolynomial_principalAngularPoint
    {d : ℕ} {ι : Type*} [Fintype ι] (frequency : ι → Fin d → ℤ)
    (coefficient : ι → ℂ) (x : Point d) :
    angularTrigPolynomial frequency coefficient (principalAngularPoint x) =
      angularTrigPolynomial frequency coefficient x := by
  unfold angularTrigPolynomial
  simp only [integerFourierPhase_principalAngularPoint]

@[simp] theorem segmentedPolynomial_angularValue_principalAngularPoint
    {d m r D : ℕ} (P : NumDetect.SegmentedPolynomial d m r D) (x : Point d) :
    P.angularValue (principalAngularPoint x) = P.angularValue x := by
  simp only [NumDetect.SegmentedPolynomial.angularValue_eq_angularTrigPolynomial,
    angularTrigPolynomial_principalAngularPoint]


@[simp] theorem angularTrigPolynomial_sub_winding
    {d : ℕ} {ι : Type*} [Fintype ι] (frequency : ι → Fin d → ℤ)
    (coefficient : ι → ℂ) (x : Point d) (p : Fin d → ℤ) :
    angularTrigPolynomial frequency coefficient (fun q => x q - 2 * Real.pi * p q) =
      angularTrigPolynomial frequency coefficient x := by
  unfold angularTrigPolynomial
  simp only [integerFourierPhase_sub_winding]

@[simp] theorem segmentedPolynomial_angularValue_sub_winding
    {d m r D : ℕ} (P : NumDetect.SegmentedPolynomial d m r D)
    (x : Point d) (p : Fin d → ℤ) :
    P.angularValue (fun q => x q - 2 * Real.pi * p q) = P.angularValue x := by
  simp only [NumDetect.SegmentedPolynomial.angularValue_eq_angularTrigPolynomial,
    angularTrigPolynomial_sub_winding]

/-- Integer-frequency Vandermonde matrices are exactly unchanged by arbitrary
independent coordinate windings of each source node. -/
theorem integerVandermonde_sub_winding {ι : Type*} {d n : ℕ}
    (frequency : ι → Fin d → ℤ) (Y : Fin n → Point d)
    (p : Fin n → Fin d → ℤ) :
    vandermondeMatrix (fun k q => (frequency k q : ℝ))
      (fun j q => Y j q - 2 * Real.pi * p j q) =
      vandermondeMatrix (fun k q => (frequency k q : ℝ)) Y := by
  funext k j
  exact integerFourierPhase_sub_winding (frequency k) (p j) (Y j)

@[simp] theorem integerVandermonde_principalAngularPoint {ι : Type*} {d n : ℕ}
    (frequency : ι → Fin d → ℤ) (Y : Fin n → Point d) :
    vandermondeMatrix (fun k q => (frequency k q : ℝ))
      (fun j => principalAngularPoint (Y j)) =
      vandermondeMatrix (fun k q => (frequency k q : ℝ)) Y := by
  funext k j
  exact integerFourierPhase_principalAngularPoint (frequency k) (Y j)

end
end LeanNumDetect.MultiTuran.MultiClump
