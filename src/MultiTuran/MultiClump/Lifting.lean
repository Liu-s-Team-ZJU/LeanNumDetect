import MultiTuran.MultiClump.ClumpLifts
import MultiTuran.MultiClump.ClumpGeometry
import MultiTuran.MultiClump.BoundFormula

/-! # Returning from short real clump lifts to the measured torus matrix -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace LeanNumDetect.MultiTuran.MultiClump
noncomputable section

def liftNodes {d n : ℕ} (Y : Fin n → Point d) (p : Fin n → Fin d → ℤ) :
    Fin n → Point d := fun j q => Y j q - 2*Real.pi*p j q

@[simp] theorem torusCoordinateDistance_sub_windings (x y : ℝ) (p q : ℤ) :
    torusCoordinateDistance (x-2*Real.pi*p) (y-2*Real.pi*q) =
      torusCoordinateDistance x y := by
  have hz (k : ℤ) : ((2*Real.pi*k : ℝ) : AddCircle (2*Real.pi)) = 0 := by
    rw [mul_comm (2*Real.pi), ← zsmul_eq_mul, AddCircle.coe_zsmul,
      AddCircle.coe_period, smul_zero]
  unfold torusCoordinateDistance
  congr 1
  simp only [AddCircle.coe_sub, hz, sub_zero]

@[simp] theorem torusLInfDistance_liftNodes {d n : ℕ} (Y : Fin n → Point d)
    (p : Fin n → Fin d → ℤ) (i j : Fin n) :
    torusLInfDistance (liftNodes Y p i) (liftNodes Y p j) =
      torusLInfDistance (Y i) (Y j) := by
  simp only [torusLInfDistance, liftNodes, torusCoordinateDistance_sub_windings]

@[simp] theorem nodeSeparation_liftNodes {d n : ℕ} (Y : Fin n → Point d)
    (p : Fin n → Fin d → ℤ) : nodeSeparation (liftNodes Y p) = nodeSeparation Y := by
  simp only [nodeSeparation, torusLInfDistance_liftNodes]

@[simp] theorem generalizedVandermonde_liftNodes {d n : ℕ} (G : SegmentedGrid d)
    (Y : Fin n → Point d) (p : Fin n → Fin d → ℤ) :
    generalizedVandermonde G (liftNodes Y p) = generalizedVandermonde G Y := by
  funext k j
  exact integerFourierPhase_sub_winding (fun q => (G.rowVector k q : ℤ)) (p j) (Y j)

@[simp] theorem multiClumpArrayLowerBound_liftNodes {d n : ℕ}
    (C_T : ℝ) (G : SegmentedGrid d) (Y : Fin n → Point d)
    (p : Fin n → Fin d → ℤ) (nStar : ℕ) :
    multiClumpArrayLowerBound C_T G (liftNodes Y p) nStar =
      multiClumpArrayLowerBound C_T G Y nStar := by
  simp only [multiClumpArrayLowerBound, nodeSeparation_liftNodes]

end
end LeanNumDetect.MultiTuran.MultiClump
