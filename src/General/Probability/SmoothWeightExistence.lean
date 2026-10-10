import General.Probability.SmoothFramePotential
import General.MatrixAnalysis.HermitianOperatorNorm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Order.Compact

/-!
# Coercivity and minimizers of the smooth precision potential

A logarithmic entropy lower bound makes the precision potential coercive and
provides a global minimum on the positive-definite cone. At a stationary point,
the precision spectrum directly bounds its inverse.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace LeanNumDetect.FiniteMatrixSampling

open FrameMatrixBounds

noncomputable section
attribute [local instance] Classical.propDecidable


/-- The scalar estimate controls both ends of the positive spectrum. -/
theorem smooth_spectral_scalar_coercivity (D t : ℝ) (hD : 0 ≤ D) :
    |t| / 5 - 6 * D / 5 ≤ -t + (6 / 5 : ℝ) * max 0 (t - D) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    nlinarith [le_max_right 0 (t - D)]
  · rw [abs_of_nonpos (le_of_not_ge ht)]
    nlinarith [le_max_left 0 (t - D)]

/-- Spectral expansion of the real log determinant, independent of any iteration. -/
theorem smooth_log_det_eq_sum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) :
    Real.log (A.det.re) = ∑ j, Real.log (hA.isHermitian.eigenvalues j) := by
  have hdet : A.det.re = ∏ j, hA.isHermitian.eigenvalues j := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues]
    have hp : (∏ j, (hA.isHermitian.eigenvalues j : ℂ)) =
        ((∏ j, hA.isHermitian.eigenvalues j : ℝ) : ℂ) := by norm_cast
    change (∏ j, (hA.isHermitian.eigenvalues j : ℂ)).re = _
    rw [hp]
    rfl
  rw [hdet]
  exact Real.log_prod (fun j _ => (hA.eigenvalues_pos j).ne')

/-- Every potential sublevel has a uniform bound on the absolute log spectrum. -/
theorem smoothFramePotential_logEigenvalues_abs_sum_le_of_entropy {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (_hι : 0 < Fintype.card ι)
    (f : ι → EuclideanSpace ℂ (Fin n)) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) {θ : ℝ} (hθ : 0 < θ)
    (hentropy : (6 / 5 : ℝ) * (∑ j,
      Real.log (1 + θ ^ 2 * hA.isHermitian.eigenvalues j / ((12 / 5 : ℝ) * n))) ≤
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ i, smoothEntropy ((12 / 5 : ℝ) * n) (quadratic A (f i)))
    (hpotential : smoothFramePotential f ((12 / 5 : ℝ) * n) A ≤ (n : ℝ)) :
    (∑ j, |Real.log (hA.isHermitian.eigenvalues j)|) ≤
      5 * (n : ℝ) + 6 * (n : ℝ) * max 0 (Real.log (((12 / 5 : ℝ) * n) / θ ^ 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let R := (12 / 5 : ℝ) * n
  have hR : 0 < R := by dsimp [R]; positivity
  let C := Real.log (R / θ ^ 2)
  let D := max 0 C
  let t := fun j => Real.log (hA.isHermitian.eigenvalues j)
  let hmean := (Fintype.card ι : ℝ)⁻¹ * ∑ i, smoothEntropy R (quadratic A (f i))
  have hlog (j : Fin n) :
      max 0 (t j - D) ≤ Real.log (1 + θ ^ 2 * hA.isHermitian.eigenvalues j / R) := by
    have hp := hA.eigenvalues_pos j
    have hx : 0 < θ ^ 2 * hA.isHermitian.eigenvalues j / R := by positivity
    have he : Real.log (θ ^ 2 * hA.isHermitian.eigenvalues j / R) = t j - C := by
      dsimp [t, C]
      rw [Real.log_div (by positivity) hR.ne', Real.log_mul (by positivity) hp.ne',
        Real.log_div hR.ne' (by positivity)]
      ring
    apply max_le
    · apply Real.log_nonneg
      linarith
    · calc
        t j - D ≤ t j - C := sub_le_sub_left (le_max_right 0 C) _
        _ = Real.log (θ ^ 2 * hA.isHermitian.eigenvalues j / R) := he.symm
        _ ≤ Real.log (1 + θ ^ 2 * hA.isHermitian.eigenvalues j / R) :=
          Real.log_le_log hx (by linarith)
  have hentropy : (6 / 5 : ℝ) * (∑ j, max 0 (t j - D)) ≤ hmean := by
    exact (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hlog j))
      (by norm_num)).trans (hentropy)
  have hupper : -(∑ j, t j) + hmean ≤ (n : ℝ) := by
    simpa only [smoothFramePotential, smooth_log_det_eq_sum hA] using hpotential
  have hscalar := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun j _ => smooth_spectral_scalar_coercivity D (t j) (le_max_left 0 C))
  have hscalar' : (∑ j, |t j|) / 5 - 6 * (n : ℝ) * D / 5 ≤
      -(∑ j, t j) + (6 / 5 : ℝ) * (∑ j, max 0 (t j - D)) := by
    have hl : (∑ j, (|t j| / 5 - 6 * D / 5)) =
        (∑ j, |t j|) / 5 - 6 * (n : ℝ) * D / 5 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hr : (∑ j, (-t j + (6 / 5 : ℝ) * max 0 (t j - D))) =
        -(∑ j, t j) + (6 / 5 : ℝ) * (∑ j, max 0 (t j - D)) := by
      rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rwa [hl, hr] at hscalar
  have hb : (∑ j, |t j|) ≤ 5 * (n : ℝ) + 6 * (n : ℝ) * D := by linarith
  exact hb


/-- A closed matrix interval described by real quadratic forms. -/
def hermitianQuadraticInterval (n : ℕ) (c C : ℝ) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  {A | A.IsHermitian ∧ ∀ x : EuclideanSpace ℂ (Fin n),
    c * ‖x‖ ^ 2 ≤ quadratic A x ∧ quadratic A x ≤ C * ‖x‖ ^ 2}

theorem isClosed_hermitianQuadraticInterval (n : ℕ) (c C : ℝ) :
    IsClosed (hermitianQuadraticInterval n c C) := by
  have hh : IsClosed {A : Matrix (Fin n) (Fin n) ℂ | A.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hq : IsClosed {A : Matrix (Fin n) (Fin n) ℂ |
      ∀ x : EuclideanSpace ℂ (Fin n),
        c * ‖x‖ ^ 2 ≤ quadratic A x ∧ quadratic A x ≤ C * ‖x‖ ^ 2} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro x
    have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => quadratic A x) :=
      (quadraticTestLinearMap x).continuous_of_finiteDimensional
    exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
  exact hh.inter hq

theorem isCompact_hermitianQuadraticInterval (n : ℕ) {c C : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) :
    IsCompact (hermitianQuadraticInterval n c C) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_hermitianQuadraticInterval n c C, ?_⟩
  apply (Metric.isBounded_iff_subset_closedBall (0 : Matrix (Fin n) (Fin n) ℂ)).mpr
  refine ⟨C, ?_⟩
  intro A hA
  rw [Metric.mem_closedBall, dist_zero_right, Matrix.l2_opNorm_def]
  apply (hermitian_operatorNorm_le_iff_quadratic_abs_le A hA.1 hC).mpr
  intro x
  apply abs_le.mpr
  have hlo := (hA.2 x).1
  have hhi := (hA.2 x).2
  constructor
  · have hnon : 0 ≤ quadratic A x := (mul_nonneg hc (sq_nonneg _)).trans hlo
    have hnon' := mul_nonneg hC (sq_nonneg ‖x‖)
    linarith
  · exact hhi

theorem posDef_of_mem_hermitianQuadraticInterval {n : ℕ} {c C : ℝ}
    (hc : 0 < c) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ hermitianQuadraticInterval n c C) : A.PosDef := by
  apply hA.1.posDef_iff_eigenvalues_pos.mpr
  intro j
  have hh := (hA.2 (hA.1.eigenvectorBasis j)).1
  rw [TraceExponential.quadratic_eigenvector,
    hA.1.eigenvectorBasis.orthonormal.1 j, one_pow, mul_one] at hh
  exact hc.trans_le hh

/-- Spectral bounds imply the corresponding quadratic-form bounds. -/
theorem mem_hermitianQuadraticInterval_of_eigenvalues_bounds {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) {c C : ℝ}
    (hbound : ∀ j, c ≤ hA.eigenvalues j ∧ hA.eigenvalues j ≤ C) :
    A ∈ hermitianQuadraticInterval n c C := by
  refine ⟨hA, fun x => ?_⟩
  rw [TraceExponential.quadratic_eq_sum hA,
    ← hA.eigenvectorBasis.sum_sq_norm_inner_right x, Finset.mul_sum, Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (hbound j).1 (sq_nonneg _))
  · exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (hbound j).2 (sq_nonneg _))

/-- A potential sublevel lies inside a compact interval strictly above zero. -/
theorem smoothFramePotential_sublevel_mem_interval_of_entropy {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι)
    (f : ι → EuclideanSpace ℂ (Fin n)) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) {θ : ℝ} (hθ : 0 < θ)
    (hentropy : (6 / 5 : ℝ) * (∑ j,
      Real.log (1 + θ ^ 2 * hA.isHermitian.eigenvalues j / ((12 / 5 : ℝ) * n))) ≤
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ i, smoothEntropy ((12 / 5 : ℝ) * n) (quadratic A (f i)))
    (hpotential : smoothFramePotential f ((12 / 5 : ℝ) * n) A ≤ (n : ℝ)) :
    A ∈ hermitianQuadraticInterval n
      (Real.exp (-(5 * (n : ℝ) +
        6 * (n : ℝ) * max 0 (Real.log (((12 / 5 : ℝ) * n) / θ ^ 2)))))
      (Real.exp (5 * (n : ℝ) +
        6 * (n : ℝ) * max 0 (Real.log (((12 / 5 : ℝ) * n) / θ ^ 2)))) := by
  let K := 5 * (n : ℝ) + 6 * (n : ℝ) * max 0 (Real.log (((12 / 5 : ℝ) * n) / θ ^ 2))
  have hs := smoothFramePotential_logEigenvalues_abs_sum_le_of_entropy hn hι f A hA hθ hentropy hpotential
  apply mem_hermitianQuadraticInterval_of_eigenvalues_bounds hA.isHermitian
  intro j
  have hsingle : |Real.log (hA.isHermitian.eigenvalues j)| ≤
      ∑ i, |Real.log (hA.isHermitian.eigenvalues i)| :=
    Finset.single_le_sum (f := fun i : Fin n => |Real.log (hA.isHermitian.eigenvalues i)|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  have hb : |Real.log (hA.isHermitian.eigenvalues j)| ≤ K := hsingle.trans hs
  have hh := abs_le.mp hb
  constructor
  · have he := Real.exp_le_exp.mpr hh.1
    rwa [Real.exp_log (hA.eigenvalues_pos j)] at he
  · have he := Real.exp_le_exp.mpr hh.2
    rwa [Real.exp_log (hA.eigenvalues_pos j)] at he


/-- The smooth precision potential attains a global minimum on the full
positive-definite cone, using only the supplied logarithmic entropy estimate. -/
theorem exists_smoothFramePotential_minimizer_of_entropy {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    (f : Fin N → EuclideanSpace ℂ (Fin n)) (hfull : mean (framePopulation f) = 1)
    {θ : ℝ} (hθ : 0 < θ)
    (hentropy : ∀ (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef),
      (6 / 5 : ℝ) * (∑ j,
        Real.log (1 + θ ^ 2 * hH.isHermitian.eigenvalues j / ((12 / 5 : ℝ) * n))) ≤
        (N : ℝ)⁻¹ *
          ∑ i, smoothEntropy ((12 / 5 : ℝ) * n) (quadratic H (f i))) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosDef ∧
      ∀ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef →
        smoothFramePotential f ((12 / 5 : ℝ) * n) A ≤
          smoothFramePotential f ((12 / 5 : ℝ) * n) H := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : (0 : ℝ) < (12 / 5 : ℝ) * n := by positivity
  let K := 5 * (n : ℝ) + 6 * (n : ℝ) * max 0 (Real.log (((12 / 5 : ℝ) * n) / θ ^ 2))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let s := hermitianQuadraticInterval n (Real.exp (-K)) (Real.exp K)
  have hs : IsCompact s :=
    isCompact_hermitianQuadraticInterval n (Real.exp_pos _).le (Real.exp_pos _).le
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ s := by
    refine ⟨Matrix.isHermitian_one, fun x => ?_⟩
    rw [quadratic_identity]
    have hlo : Real.exp (-K) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr hK)
    have hhi : 1 ≤ Real.exp K := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hK
    constructor
    · simpa using mul_le_mul_of_nonneg_right hlo (sq_nonneg ‖x‖)
    · simpa using mul_le_mul_of_nonneg_right hhi (sq_nonneg ‖x‖)
  have hpos : ∀ A ∈ s, A.PosDef := fun A hA =>
    posDef_of_mem_hermitianQuadraticInterval (Real.exp_pos _) hA
  have hcont : ContinuousOn (smoothFramePotential f ((12 / 5 : ℝ) * n)) s :=
    (continuousOn_smoothFramePotential f hR).mono (fun A hA => hpos A hA)
  obtain ⟨A, hAs, hmin⟩ := hs.exists_isMinOn ⟨1, hone⟩ hcont
  refine ⟨A, hpos A hAs, fun H hH => ?_⟩
  by_cases hHsub : smoothFramePotential f ((12 / 5 : ℝ) * n) H ≤ (n : ℝ)
  · have hHmem : H ∈ s := smoothFramePotential_sublevel_mem_interval_of_entropy hn
      (by simpa using hN) f H hH hθ (by simpa using hentropy H hH) hHsub
    exact hmin hHmem
  · have hAupper := (hmin hone).trans (smoothFramePotential_one_le f hR hfull)
    exact hAupper.trans (le_of_not_ge hHsub)


/-- The stationary inverse is bounded directly from the precision spectrum;
no determinant bound for the inverse matrix is used. -/
theorem smoothFramePotential_inverse_quadratic_lower_of_entropy {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι]
    (f : ι → EuclideanSpace ℂ (Fin n)) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) {θ : ℝ} (hθ : 0 < θ)
    (hentropy : (6 / 5 : ℝ) * (∑ j,
      Real.log (1 + θ ^ 2 * hA.isHermitian.eigenvalues j / ((12 / 5 : ℝ) * n))) ≤
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ i, smoothEntropy ((12 / 5 : ℝ) * n) (quadratic A (f i)))
    (hpotential : smoothFramePotential f ((12 / 5 : ℝ) * n) A ≤ (n : ℝ))
    (hinv : ∀ x : EuclideanSpace ℂ (Fin n), quadratic A⁻¹ x ≤ ‖x‖ ^ 2) :
    ∀ x : EuclideanSpace ℂ (Fin n),
      Real.exp (-(5 * (n : ℝ) +
        6 * (n : ℝ) * Real.log (((12 / 5 : ℝ) * n) / θ ^ 2))) * ‖x‖ ^ 2 ≤
        quadratic A⁻¹ x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let R := (12 / 5 : ℝ) * n
  have hR : 0 < R := by dsimp [R]; positivity
  let C := Real.log (R / θ ^ 2)
  let K := 5 * (n : ℝ) + 6 * (n : ℝ) * C
  let t := fun j => Real.log (hA.isHermitian.eigenvalues j)
  let hmean := (Fintype.card ι : ℝ)⁻¹ * ∑ i, smoothEntropy R (quadratic A (f i))
  have hAlo (x : EuclideanSpace ℂ (Fin n)) : ‖x‖ ^ 2 ≤ quadratic A x := by
    have hh := inverse_quadratic_antitone hA.inv Matrix.PosDef.one
      (by simpa only [quadratic_identity] using hinv) x
    letI := hA.isUnit.invertible
    simpa only [inv_one, quadratic_identity, Matrix.inv_inv_of_invertible] using hh
  have heig (j : Fin n) : 1 ≤ hA.isHermitian.eigenvalues j := by
    have hh := hAlo (hA.isHermitian.eigenvectorBasis j)
    simpa only [TraceExponential.quadratic_eigenvector,
      hA.isHermitian.eigenvectorBasis.orthonormal.1 j, one_pow] using hh
  have ht (j : Fin n) : 0 ≤ t j := Real.log_nonneg (heig j)
  have hlog (j : Fin n) :
      t j - C ≤ Real.log (1 + θ ^ 2 * hA.isHermitian.eigenvalues j / R) := by
    have hp := hA.eigenvalues_pos j
    have hx : 0 < θ ^ 2 * hA.isHermitian.eigenvalues j / R := by positivity
    have he : Real.log (θ ^ 2 * hA.isHermitian.eigenvalues j / R) = t j - C := by
      dsimp [t, C]
      rw [Real.log_div (by positivity) hR.ne', Real.log_mul (by positivity) hp.ne',
        Real.log_div hR.ne' (by positivity)]
      ring
    rw [← he]
    exact Real.log_le_log hx (by linarith)
  have hsum : (∑ j, t j) - (n : ℝ) * C ≤
      ∑ j, Real.log (1 + θ ^ 2 * hA.isHermitian.eigenvalues j / R) := by
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun j _ => hlog j)
  have hupper : -(∑ j, t j) + hmean ≤ (n : ℝ) := by
    simpa only [smoothFramePotential, smooth_log_det_eq_sum hA] using hpotential
  have hs : (∑ j, t j) ≤ K := by
    change (6 / 5 : ℝ) * (∑ j,
      Real.log (1 + θ ^ 2 * hA.isHermitian.eigenvalues j / R)) ≤ hmean at hentropy
    dsimp [K]
    linarith
  have hinterval : A ∈ hermitianQuadraticInterval n 1 (Real.exp K) := by
    apply mem_hermitianQuadraticInterval_of_eigenvalues_bounds hA.isHermitian
    intro j
    refine ⟨heig j, ?_⟩
    have hsingle : t j ≤ ∑ i, t i :=
      Finset.single_le_sum (f := t) (fun i _ => ht i) (Finset.mem_univ j)
    have hh := Real.exp_le_exp.mpr (hsingle.trans hs)
    simpa only [t, Real.exp_log (hA.eigenvalues_pos j)] using hh
  let D : Matrix (Fin n) (Fin n) ℂ := (Real.exp K : ℂ) • 1
  have hD : D.PosDef := Matrix.PosDef.one.smul (by exact_mod_cast Real.exp_pos K)
  have hAD (x : EuclideanSpace ℂ (Fin n)) : quadratic A x ≤ quadratic D x := by
    simpa only [D, quadratic_smul_matrix, quadratic_identity] using (hinterval.2 x).2
  intro x
  have hh := inverse_quadratic_antitone hA hD hAD x
  have hDi : D⁻¹ = (Real.exp (-K) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    apply Matrix.inv_eq_left_inv
    simp only [D, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    have he : (Real.exp K : ℂ) * (Real.exp (-K) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      simp
    rw [he, one_smul]
  rw [hDi, quadratic_smul_matrix, quadratic_identity] at hh
  simpa only [K, C, R] using hh

end
end LeanNumDetect.FiniteMatrixSampling
