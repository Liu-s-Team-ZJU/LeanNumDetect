import General.MatrixAnalysis.TraceExponential
import General.Probability.FiniteAverage

/-! Spectral chord bounds for positive semidefinite matrix exponentials. -/

set_option autoImplicit false

open Matrix NormedSpace
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

namespace LeanNumDetect.TraceExponential

open FiniteMatrixSampling

variable {d : ℕ}

theorem exp_real_smul_eq_cfc {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (θ : ℝ) :
    exp (θ • A) = cfc (fun t : ℝ => Real.exp (θ * t)) A := by
  change exp (θ • A) = cfc (Real.exp ∘ (fun t : ℝ => θ * t)) A
  rw [cfc_comp Real.exp (fun t : ℝ => θ * t) A hA.isSelfAdjoint,
    cfc_const_mul_id θ A hA.isSelfAdjoint, CFC.real_exp_eq_normedSpace_exp]

theorem quadratic_exp_smul_eq_sum {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (θ : ℝ) (x : EuclideanSpace ℂ (Fin d)) :
    FiniteMatrixSampling.quadratic (exp (θ • A)) x =
      ∑ i, Real.exp (θ * hA.eigenvalues i) * ‖⟪hA.eigenvectorBasis i, x⟫_ℂ‖ ^ 2 := by
  apply quadratic_eq_sum_of_eigenbasis (exp (θ • A))
    (hA.smul (isSelfAdjoint_iff.mpr (star_trivial θ))).exp
  intro i
  rw [exp_real_smul_eq_cfc hA θ]
  exact cfc_apply_eigenvector hA (fun t => Real.exp (θ * t)) i

theorem exp_chord {R t θ : ℝ} (hR : 0 < R) (ht0 : 0 ≤ t) (htR : t ≤ R) :
    Real.exp (θ * t) ≤ 1 + (Real.exp (θ * R) - 1) * t / R := by
  have ht : 0 ≤ t / R := div_nonneg ht0 hR.le
  have ht' : t / R ≤ 1 := (div_le_one hR).mpr htR
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (θ * R))
    (sub_nonneg.mpr ht') ht (show (1 - t / R) + t / R = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  calc
    Real.exp (θ * t) = Real.exp (t / R * (θ * R)) := by
      congr 1
      field_simp
    _ ≤ 1 - t / R + t / R * Real.exp (θ * R) := h
    _ = _ := by ring

/-- The scalar exponential chord lifted through the Hermitian spectral theorem. -/
theorem quadratic_exp_smul_le_chord {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ x : EuclideanSpace ℂ (Fin d),
      FiniteMatrixSampling.quadratic A x ≤ R * ‖x‖ ^ 2)
    (θ : ℝ) (x : EuclideanSpace ℂ (Fin d)) :
    FiniteMatrixSampling.quadratic (exp (θ • A)) x ≤
      ‖x‖ ^ 2 + ((Real.exp (θ * R) - 1) / R) * FiniteMatrixSampling.quadratic A x := by
  have he (i : Fin d) : hA.isHermitian.eigenvalues i ≤ R := by
    have h := hbound (hA.isHermitian.eigenvectorBasis i)
    rwa [quadratic_eigenvector, hA.isHermitian.eigenvectorBasis.orthonormal.1,
      one_pow, mul_one] at h
  rw [quadratic_exp_smul_eq_sum hA.isHermitian,
    quadratic_eq_sum hA.isHermitian, ← hA.isHermitian.eigenvectorBasis.sum_sq_norm_inner_right x]
  calc
    _ ≤ ∑ i, (1 + (Real.exp (θ * R) - 1) * hA.isHermitian.eigenvalues i / R) *
        ‖⟪hA.isHermitian.eigenvectorBasis i, x⟫_ℂ‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (exp_chord hR (hA.eigenvalues_nonneg i) (he i))
        (sq_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem trace_exp_mul_eq_sum {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) (B : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.trace (exp H * B)).re =
      ∑ i, Real.exp (hH.eigenvalues i) *
        FiniteMatrixSampling.quadratic B (hH.eigenvectorBasis i) := by
  rw [trace_eq_sum_quadratic (exp H * B) hH.eigenvectorBasis]
  apply Finset.sum_congr rfl
  intro i _
  unfold FiniteMatrixSampling.quadratic
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH.exp
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, ← hs,
    exp_apply_eigenvector hH, inner_smul_left]
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- A quadratic bound on a mean controls its trace against every exponential. -/
theorem finiteAverage_trace_exp_mul_le {α : Type*} [Fintype α]
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (Y : α → Matrix (Fin d) (Fin d) ℂ) {c : ℝ}
    (hY : ∀ x : EuclideanSpace ℂ (Fin d),
      finiteAverage (fun k => FiniteMatrixSampling.quadratic (Y k) x) ≤ c * ‖x‖ ^ 2) :
    finiteAverage (fun k => (Matrix.trace (exp H * Y k)).re) ≤ c * traceExp H := by
  simp_rw [trace_exp_mul_eq_sum hH]
  rw [finiteAverage_sum]
  calc
    _ = ∑ i, Real.exp (hH.eigenvalues i) *
        finiteAverage (fun k => FiniteMatrixSampling.quadratic (Y k) (hH.eigenvectorBasis i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact finiteAverage_smul (Real.exp (hH.eigenvalues i)) _
    _ ≤ ∑ i, Real.exp (hH.eigenvalues i) * c := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [hH.eigenvectorBasis.orthonormal.1, one_pow, mul_one] using
        hY (hH.eigenvectorBasis i)
    _ = _ := by rw [traceExp_eq_sum hH, Finset.mul_sum]; congr 1; funext i; ring

theorem quadratic_sum {α : Type*} [Fintype α]
    (Y : α → Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    FiniteMatrixSampling.quadratic (∑ k, Y k) x =
      ∑ k, FiniteMatrixSampling.quadratic (Y k) x := by
  simp [FiniteMatrixSampling.quadratic, map_sum, inner_sum]

theorem finiteAverage_quadratic {α : Type*} [Fintype α]
    (Y : α → Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    finiteAverage (fun k => FiniteMatrixSampling.quadratic (Y k) x) =
      FiniteMatrixSampling.quadratic (finiteAverage Y) x := by
  simp [finiteAverage, quadratic_real_smul, quadratic_sum]

theorem finiteAverage_eq_mean {N : ℕ} (Y : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    finiteAverage Y = mean Y := by
  unfold finiteAverage mean
  simp only [Fintype.card_fin]
  ext i j
  simp [Complex.real_smul]

theorem finiteAverage_quadratic_exp_le_chord {N : ℕ} (hN : 0 < N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ k, (X k).PosSemidef) {R : ℝ} (hR : 0 < R)
    (hbound : ∀ k (x : EuclideanSpace ℂ (Fin d)),
      FiniteMatrixSampling.quadratic (X k) x ≤ R * ‖x‖ ^ 2)
    (θ : ℝ) (x : EuclideanSpace ℂ (Fin d)) :
    finiteAverage (fun k => FiniteMatrixSampling.quadratic (exp (θ • X k)) x) ≤
      ‖x‖ ^ 2 + ((Real.exp (θ * R) - 1) / R) *
        FiniteMatrixSampling.quadratic (mean X) x := by
  letI : NeZero N := ⟨hN.ne'⟩
  calc
    _ ≤ finiteAverage (fun k => ‖x‖ ^ 2 + ((Real.exp (θ * R) - 1) / R) *
        FiniteMatrixSampling.quadratic (X k) x) :=
      finiteAverage_mono fun k => quadratic_exp_smul_le_chord (hX k) hR (hbound k) θ x
    _ = _ := by
      simp only [finiteAverage, Finset.sum_add_distrib, smul_eq_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.mul_sum]
      rw [← finiteAverage_eq_mean, ← finiteAverage_quadratic]
      simp only [finiteAverage, smul_eq_mul, Fintype.card_fin]
      field_simp

/-- Exponentiating the affine chord produces the one-draw Chernoff bound.
The weighted mean hypothesis accommodates either sign of the Laplace parameter. -/
theorem finiteAverage_quadratic_exp_le_exponential {N : ℕ} (hN : 0 < N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ k, (X k).PosSemidef) {R μ θ : ℝ} (hR : 0 < R)
    (hbound : ∀ k (x : EuclideanSpace ℂ (Fin d)),
      FiniteMatrixSampling.quadratic (X k) x ≤ R * ‖x‖ ^ 2)
    (hmean : ∀ x : EuclideanSpace ℂ (Fin d),
      ((Real.exp (θ * R) - 1) / R) * FiniteMatrixSampling.quadratic (mean X) x ≤
      ((Real.exp (θ * R) - 1) / R) * μ * ‖x‖ ^ 2)
    (x : EuclideanSpace ℂ (Fin d)) :
    finiteAverage (fun k => FiniteMatrixSampling.quadratic (exp (θ • X k)) x) ≤
      Real.exp (((Real.exp (θ * R) - 1) / R) * μ) * ‖x‖ ^ 2 := by
  calc
    _ ≤ ‖x‖ ^ 2 + ((Real.exp (θ * R) - 1) / R) *
        FiniteMatrixSampling.quadratic (mean X) x :=
      finiteAverage_quadratic_exp_le_chord hN X hX hR hbound θ x
    _ ≤ (1 + ((Real.exp (θ * R) - 1) / R) * μ) * ‖x‖ ^ 2 := by
      nlinarith [hmean x]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (((Real.exp (θ * R) - 1) / R) * μ)])
      (sq_nonneg _)

end LeanNumDetect.TraceExponential
