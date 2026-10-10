import General.MatrixAnalysis.FiniteFrameGram
import General.MatrixAnalysis.PositiveDefiniteDeterminant
import General.Probability.RestrictedQuadraticMoments
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix

/-! Smooth logarithmic row weights and the precision-matrix frame potential.
The potential is minimized on the positive-definite cone; no covariance
iteration is part of this construction. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.FiniteMatrixSampling

open FrameMatrixBounds
noncomputable section

/-- A smooth entropy whose derivative is the auxiliary row weight. -/
def smoothEntropy (R t : ℝ) : ℝ := R * Real.log (1 + t / R)

/-- The weight associated with a row's precision-matrix energy. -/
def smoothWeight (R t : ℝ) : ℝ := R / (R + t)

/-- The variational potential in the precision matrix, before inversion. -/
def smoothFramePotential {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → EuclideanSpace ℂ (Fin n)) (R : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  -Real.log (A.det.re) +
    (Fintype.card ι : ℝ)⁻¹ * ∑ k, smoothEntropy R (quadratic A (f k))

theorem smoothWeight_pos_le_one {R t : ℝ} (hR : 0 < R) (ht : 0 ≤ t) :
    0 < smoothWeight R t ∧ smoothWeight R t ≤ 1 := by
  have hden : 0 < R + t := by linarith
  exact ⟨div_pos hR hden, (div_le_one hden).mpr (by linarith)⟩

theorem smoothWeight_mul_le {R t : ℝ} (hR : 0 < R) (ht : 0 ≤ t) :
    smoothWeight R t * t ≤ R := by
  have hden : 0 < R + t := by linarith
  unfold smoothWeight
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith

theorem smoothEntropy_nonneg {R t : ℝ} (hR : 0 < R) (ht : 0 ≤ t) :
    0 ≤ smoothEntropy R t := by
  unfold smoothEntropy
  apply mul_nonneg hR.le
  exact Real.log_nonneg (le_add_of_nonneg_right (div_nonneg ht hR.le))

theorem smoothEntropy_le {R t : ℝ} (hR : 0 < R) (ht : 0 ≤ t) :
    smoothEntropy R t ≤ t := by
  have harg : 0 < 1 + t / R := by positivity
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos harg) hR.le
  have he : R * (1 + t / R - 1) = t := by field_simp; ring
  simpa only [smoothEntropy, he] using h

/-- The logarithmic tail needed by the finite spectral-thickness estimate. -/
theorem smoothEntropy_log_lower {R t : ℝ} (hR : 0 < R) (ht : 0 ≤ t) :
    R * max 0 (Real.log (t / R)) ≤ smoothEntropy R t := by
  have harg : 0 < 1 + t / R := by positivity
  have h0 : 0 ≤ Real.log (1 + t / R) := Real.log_nonneg (le_add_of_nonneg_right (div_nonneg ht hR.le))
  have hl : Real.log (t / R) ≤ Real.log (1 + t / R) := by
    by_cases ht0 : t = 0
    · simp [ht0]
    · exact (Real.log_le_log_iff (div_pos (lt_of_le_of_ne ht (Ne.symm ht0)) hR) harg).mpr
        (by linarith)
  exact mul_le_mul_of_nonneg_left (max_le h0 hl) hR.le

theorem smoothEntropy_hasDerivAt {R t : ℝ} (hR : 0 < R) (ht : 0 ≤ t) :
    HasDerivAt (smoothEntropy R) (smoothWeight R t) t := by
  have harg : 0 < 1 + t / R := by positivity
  have hbase : HasDerivAt (fun u : ℝ => 1 + u / R) (1 / R) t := by
    convert! (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).div_const R) using 1
    simp
  have h := (hbase.log harg.ne').const_mul R
  have he : R * (1 / R / (1 + t / R)) = R / (R + t) := by
    field_simp
  rw [he] at h
  convert! h using 1

/-- The identity is a comparison point with potential at most the dimension. -/
theorem smoothFramePotential_one_le {N n : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin n)) {R : ℝ} (hR : 0 < R)
    (hfull : mean (framePopulation f) = 1) :
    smoothFramePotential f R 1 ≤ (n : ℝ) := by
  have hpop : weightedPopulation (framePopulation f) (fun _ => (1 : ℝ)) = framePopulation f := by
    funext k
    simp [weightedPopulation]
  have ht := trace_mul_weightedMean f (fun _ => (1 : ℝ)) (1 : Matrix (Fin n) (Fin n) ℂ)
  rw [hpop, hfull, Matrix.one_mul] at ht
  simp only [Matrix.trace_one, Fintype.card_fin, Complex.natCast_re, one_mul] at ht
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
    (fun k _ => smoothEntropy_le hR (quadratic_nonneg Matrix.PosSemidef.one (f k)))
  have h := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg N))
  simpa only [smoothFramePotential, Matrix.det_one, Complex.one_re, Real.log_one,
    neg_zero, zero_add, Fintype.card_fin, ← ht] using h

/-- The potential is continuous throughout the positive-definite cone. -/
theorem continuousOn_smoothFramePotential {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → EuclideanSpace ℂ (Fin n)) {R : ℝ} (hR : 0 < R) :
    ContinuousOn (smoothFramePotential f R)
      {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef} := by
  have hd : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => A.det.re) := by fun_prop
  have hl := hd.continuousOn.log (s := {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef})
    (fun A hA => (realDet_pos hA).ne')
  have hq (k : ι) : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => quadratic A (f k)) := by
    exact (quadraticTestLinearMap (f k)).continuous_of_finiteDimensional
  have he (k : ι) : ContinuousOn
      (fun A : Matrix (Fin n) (Fin n) ℂ => smoothEntropy R (quadratic A (f k)))
      {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef} := by
    have ha := ((hq k).div_const R).const_add 1
    have hlog := ha.continuousOn.log (s := {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef})
      (fun A hA => (show 0 < 1 + quadratic A (f k) / R from by
        have ht := quadratic_nonneg hA.posSemidef (f k)
        positivity).ne')
    exact hlog.const_mul R
  exact hl.neg.add ((continuousOn_finsetSum _ (fun k _ => he k)).const_mul _)

end
end LeanNumDetect.FiniteMatrixSampling
