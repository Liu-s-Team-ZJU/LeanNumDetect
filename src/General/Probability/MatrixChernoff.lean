import General.Probability.FiniteLaplace
import General.Probability.MatrixLaplace
import General.MatrixAnalysis.GoldenThompson
import General.MatrixAnalysis.TraceExponentialBounds

/-!
The matrix Chernoff bounds for sampling without replacement, with complete
proofs. The exact factors and parameter ranges are those of Tropp (2011),
*Improved analysis of the subsampled randomized Hadamard transform*, Theorem 2.2,
https://arxiv.org/pdf/1011.1595 . The proof combines the proved finite convex
comparison, Golden--Thompson inequality, spectral chord bound, and scalar
Laplace optimization. Repeated population values retain their multiplicities.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix NormedSpace
open scoped BigOperators InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
open LeanNumDetect.TraceExponential

namespace LeanNumDetect.FiniteMatrixSampling

/-- The trace exponential moment of a uniform subset sum. The weighted mean
condition treats positive and negative Laplace parameters in the same proof. -/
theorem sampleSum_traceExp_moment
    {N d m : ℕ} (hN : 0 < N) (hmN : m ≤ N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) {R μ θ : ℝ}
    (hR : 0 < R) (hX : ∀ k, (X k).PosSemidef)
    (hbound : ∀ k (x : EuclideanSpace ℂ (Fin d)),
      quadratic (X k) x ≤ R * ‖x‖ ^ 2)
    (hmean : ∀ x : EuclideanSpace ℂ (Fin d),
      ((Real.exp (θ * R) - 1) / R) * quadratic (mean X) x ≤
      ((Real.exp (θ * R) - 1) / R) * μ * ‖x‖ ^ 2) :
    finiteAverage (fun Ω : Sample N m => traceExp (θ • sampleSum X Ω)) ≤
      (d : ℝ) * Real.exp ((m : ℝ) * (Real.exp (θ * R) - 1) * μ / R) := by
  let Y : Fin N → selfAdjoint (Matrix (Fin d) (Fin d) ℂ) := fun k =>
    ⟨θ • X k, (hX k).isHermitian.smul (isSelfAdjoint_iff.mpr (star_trivial θ))⟩
  let c : ℝ := Real.exp (((Real.exp (θ * R) - 1) / R) * μ)
  have hstep (H : selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :
      finiteAverage (fun k => traceExp ((H + Y k).val)) ≤ c * traceExp H.val := by
    calc
      _ ≤ finiteAverage (fun k => (Matrix.trace (exp H.val * exp (θ • X k))).re) := by
        apply finiteAverage_mono
        intro k
        exact GoldenThompson.trace_exp_add_le H.property (Y k).property
      _ ≤ _ := finiteAverage_trace_exp_mul_le H.property (fun k => exp (θ • X k))
        (finiteAverage_quadratic_exp_le_exponential hN X hX hR hbound hmean)
  have h := traceExp_subset_sum_le hN hmN Y (c := c) (Real.exp_pos _).le hstep
  have hsum (Ω : Sample N m) :
      (∑ k ∈ Ω.val, Y k).val = θ • sampleSum X Ω := by
    simp [Y, sampleSum, Finset.smul_sum]
  simp only [hsum] at h
  have hc : c ^ m * (d : ℝ) =
      (d : ℝ) * Real.exp ((m : ℝ) * (Real.exp (θ * R) - 1) * μ / R) := by
    dsimp [c]
    rw [← Real.exp_nat_mul, mul_comm]
    congr 2
    ring
  exact h.trans_eq hc

theorem sampleSum_isHermitian {N d m : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ k, (X k).IsHermitian)
    (Ω : Sample N m) : (sampleSum X Ω).IsHermitian := by
  simp only [Matrix.IsHermitian, sampleSum, Matrix.conjTranspose_sum, (hX _).eq]

set_option linter.unusedVariables false in
/-- Tropp's exact lower tail, proved for every labelled finite PSD population.
The source's nonempty-sample hypothesis `hm` is retained in the interface,
although the proof also covers an empty sample. -/
theorem matrixChernoff_withoutReplacement_lower
    {N d m : ℕ} (hN : 0 < N) (hd : 0 < d) (hm : 1 ≤ m) (hmN : m ≤ N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) {R l δ : ℝ}
    (hR : 0 < R) (hX : ∀ k, (X k).PosSemidef)
    (hbound : ∀ k (x : EuclideanSpace ℂ (Fin d)),
      quadratic (X k) x ≤ R * ‖x‖ ^ 2)
    (hl : IsLeast (rayleighValues (mean X)) l)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    probability (fun Ω : Sample N m => ∃ x : EuclideanSpace ℂ (Fin d),
      ‖x‖ = 1 ∧ quadratic (sampleSum X Ω) x ≤ (1 - δ) * (m : ℝ) * l) ≤
    (d : ℝ) * (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ ((m : ℝ) * l / R) := by
  letI : Nonempty (Sample N m) := sample_nonempty hmN
  obtain ⟨_, u, _, hu⟩ := exists_rayleigh_extrema hd (mean X)
  have hmean := bounds_of_unit_bounds (mean X) (a := l) (b := u) (fun x hx =>
    ⟨hl.2 ⟨x, hx, rfl⟩, hu.2 ⟨x, hx, rfl⟩⟩)
  apply lower_chernoff_of_finite_laplace _ (by exact_mod_cast hd) hR hδ0 hδ1
    (fun θ Ω => traceExp ((-θ) • sampleSum X Ω))
  · intro θ _ Ω
    exact traceExp_nonneg ((sampleSum_isHermitian X (fun k => (hX k).isHermitian) Ω).smul
      (isSelfAdjoint_iff.mpr (star_trivial (-θ))))
  · intro θ hθ Ω hΩ
    obtain ⟨x, hx, hq⟩ := hΩ
    calc
      _ ≤ Real.exp (quadratic ((-θ) • sampleSum X Ω) x) := by
        rw [TraceExponential.quadratic_real_smul]
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ _ := exp_quadratic_le_traceExp
        ((sampleSum_isHermitian X (fun k => (hX k).isHermitian) Ω).smul
          (isSelfAdjoint_iff.mpr (star_trivial (-θ)))) x hx
  · intro θ hθ
    apply sampleSum_traceExp_moment hN hmN X hR hX hbound
    intro x
    have hc : (Real.exp (-θ * R) - 1) / R ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ hR.le
      have := Real.exp_le_one_iff.mpr (show -θ * R ≤ 0 by nlinarith)
      linarith
    simpa only [mul_assoc] using mul_le_mul_of_nonpos_left (hmean x).1 hc

set_option linter.unusedVariables false in
/-- Tropp's exact upper tail, including the full range `0 ≤ δ`.
As in the lower tail, `hm` preserves the source's original hypotheses. -/
theorem matrixChernoff_withoutReplacement_upper
    {N d m : ℕ} (hN : 0 < N) (hd : 0 < d) (hm : 1 ≤ m) (hmN : m ≤ N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) {R u δ : ℝ}
    (hR : 0 < R) (hX : ∀ k, (X k).PosSemidef)
    (hbound : ∀ k (x : EuclideanSpace ℂ (Fin d)),
      quadratic (X k) x ≤ R * ‖x‖ ^ 2)
    (hu : IsGreatest (rayleighValues (mean X)) u)
    (hδ : 0 ≤ δ) :
    probability (fun Ω : Sample N m => ∃ x : EuclideanSpace ℂ (Fin d),
      ‖x‖ = 1 ∧ (1 + δ) * (m : ℝ) * u ≤ quadratic (sampleSum X Ω) x) ≤
    (d : ℝ) * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ ((m : ℝ) * u / R) := by
  letI : Nonempty (Sample N m) := sample_nonempty hmN
  obtain ⟨l, _, hl, _⟩ := exists_rayleigh_extrema hd (mean X)
  have hmean := bounds_of_unit_bounds (mean X) (a := l) (b := u) (fun x hx =>
    ⟨hl.2 ⟨x, hx, rfl⟩, hu.2 ⟨x, hx, rfl⟩⟩)
  apply upper_chernoff_of_finite_laplace _ (by exact_mod_cast hd) hR hδ
    (fun θ Ω => traceExp (θ • sampleSum X Ω))
  · intro θ _ Ω
    exact traceExp_nonneg ((sampleSum_isHermitian X (fun k => (hX k).isHermitian) Ω).smul
      (isSelfAdjoint_iff.mpr (star_trivial θ)))
  · intro θ hθ Ω hΩ
    obtain ⟨x, hx, hq⟩ := hΩ
    calc
      _ ≤ Real.exp (quadratic (θ • sampleSum X Ω) x) := by
        rw [TraceExponential.quadratic_real_smul]
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ _ := exp_quadratic_le_traceExp
        ((sampleSum_isHermitian X (fun k => (hX k).isHermitian) Ω).smul
          (isSelfAdjoint_iff.mpr (star_trivial θ))) x hx
  · intro θ hθ
    apply sampleSum_traceExp_moment hN hmN X hR hX hbound
    intro x
    have hc : 0 ≤ (Real.exp (θ * R) - 1) / R := by
      apply div_nonneg _ hR.le
      have := Real.one_le_exp_iff.mpr (show 0 ≤ θ * R by positivity)
      linarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hmean x).2 hc


/-- The least eigenvalue of a nonempty Hermitian matrix. This definition uses
its spectral eigenvalues, rather than defining it as a Rayleigh infimum. -/
noncomputable def matrixMinimumEigenvalue {d : ℕ} (hd : 0 < d)
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℝ :=
  Finset.univ.inf' ⟨⟨0, hd⟩, Finset.mem_univ _⟩ hA.eigenvalues

/-- The greatest eigenvalue of a nonempty Hermitian matrix. -/
noncomputable def matrixMaximumEigenvalue {d : ℕ} (hd : 0 < d)
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hd⟩, Finset.mem_univ _⟩ hA.eigenvalues

theorem matrixMinimumEigenvalue_le_eigenvalue {d : ℕ} (hd : 0 < d)
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (i : Fin d) :
    matrixMinimumEigenvalue hd hA ≤ hA.eigenvalues i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem eigenvalue_le_matrixMaximumEigenvalue {d : ℕ} (hd : 0 < d)
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (i : Fin d) :
    hA.eigenvalues i ≤ matrixMaximumEigenvalue hd hA :=
  Finset.le_sup' _ (Finset.mem_univ i)

/-- The spectral minimum is attained by a unit eigenvector and bounds every
unit-vector quadratic form. -/
theorem matrixMinimumEigenvalue_isLeast_rayleigh {d : ℕ} (hd : 0 < d)
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    IsLeast (rayleighValues A) (matrixMinimumEigenvalue hd hA) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf'
    (s := Finset.univ) ⟨⟨0, hd⟩, Finset.mem_univ _⟩ hA.eigenvalues
  constructor
  · refine ⟨hA.eigenvectorBasis i, hA.eigenvectorBasis.orthonormal.1 i, ?_⟩
    rw [quadratic_eigenvector]
    exact hi.symm
  · rintro q ⟨x, hx, rfl⟩
    rw [quadratic_eq_sum hA]
    calc
      matrixMinimumEigenvalue hd hA =
          ∑ i, matrixMinimumEigenvalue hd hA *
            ‖⟪hA.eigenvectorBasis i, x⟫_ℂ‖ ^ 2 := by
        rw [← Finset.mul_sum, hA.eigenvectorBasis.sum_sq_norm_inner_right, hx,
          one_pow, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (matrixMinimumEigenvalue_le_eigenvalue hd hA i)
          (sq_nonneg _)

/-- The spectral maximum bounds the quadratic form on every vector. -/
theorem quadratic_le_matrixMaximumEigenvalue {d : ℕ} (hd : 0 < d)
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℂ (Fin d)) :
    quadratic A x ≤ matrixMaximumEigenvalue hd hA * ‖x‖ ^ 2 := by
  rw [quadratic_eq_sum hA, ← hA.eigenvectorBasis.sum_sq_norm_inner_right,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (eigenvalue_le_matrixMaximumEigenvalue hd hA i)
      (sq_nonneg _)

theorem mean_isHermitian {N d : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ k, (X k).IsHermitian) : (mean X).IsHermitian := by
  have hs : (∑ k, X k).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_sum, (hX _).eq]
  exact hs.smul (by simp : IsSelfAdjoint ((N : ℂ)⁻¹))

theorem sampleMean_isHermitian {N d m : ℕ}
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ k, (X k).IsHermitian) (Ω : Sample N m) :
    (sampleMean X Ω).IsHermitian :=
  (sampleSum_isHermitian X hX Ω).smul (by simp : IsSelfAdjoint ((m : ℂ)⁻¹))

/-- The manuscript's minimum-eigenvalue event is exactly the sum Rayleigh
lower-tail event; division by the positive sample size introduces no loss. -/
theorem sampleMean_minimumEigenvalue_le_iff {N d m : ℕ}
    (hd : 0 < d) (hm : 1 ≤ m)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ k, (X k).IsHermitian) (Ω : Sample N m) (t : ℝ) :
    matrixMinimumEigenvalue hd (sampleMean_isHermitian X hX Ω) ≤ t ↔
      ∃ x : EuclideanSpace ℂ (Fin d), ‖x‖ = 1 ∧
        quadratic (sampleSum X Ω) x ≤ (m : ℝ) * t := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hleast := matrixMinimumEigenvalue_isLeast_rayleigh hd
    (sampleMean_isHermitian X hX Ω)
  have hq (x : EuclideanSpace ℂ (Fin d)) :
      quadratic (sampleMean X Ω) x = (m : ℝ)⁻¹ * quadratic (sampleSum X Ω) x := by
    simpa only [sampleMean, Complex.ofReal_inv, Complex.ofReal_natCast] using
      quadratic_smul_matrix (sampleSum X Ω) (m : ℝ)⁻¹ x
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := hleast.1
    refine ⟨x, hx, ?_⟩
    rw [← he, hq] at h
    exact (inv_mul_le_iff₀ hmpos).mp h
  · rintro ⟨x, hx, h⟩
    apply (hleast.2 ⟨x, hx, rfl⟩).trans
    rw [hq]
    exact (inv_mul_le_iff₀ hmpos).mpr h

/-- The real-power lower Chernoff factor equals the exact exponential factor
in the sample-mean formulation. -/
theorem lower_chernoff_factor_eq_exp {u t : ℝ} (hu : u < 1) :
    (Real.exp (-u) / (1 - u) ^ (1 - u)) ^ t =
      Real.exp (-t * (u + (1 - u) * Real.log (1 - u))) := by
  have hp : 0 < 1 - u := sub_pos.mpr hu
  rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hp _)),
    Real.log_div (Real.exp_ne_zero _) (ne_of_gt (Real.rpow_pos_of_pos hp _)),
    Real.log_exp, Real.log_rpow hp]
  congr 1
  ring

set_option linter.unusedVariables false in
/-- Exact manuscript Matrix Chernoff lemma for a uniform subset: the average
minimum-eigenvalue event and the logarithmic exponential factor are retained.
Only the stated Hermitian spectral bounds and positivity assumptions occur. -/
theorem matrixChernoff_sampleMean_minimumEigenvalue_lower
    {N d m : ℕ} (hN : 0 < N) (hd : 0 < d) (hm : 1 ≤ m) (hmN : m ≤ N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ k, (X k).IsHermitian) {b u : ℝ} (hb : 0 < b)
    (hbound : ∀ k, 0 ≤ matrixMinimumEigenvalue hd (hX k) ∧
      matrixMinimumEigenvalue hd (hX k) ≤ matrixMaximumEigenvalue hd (hX k) ∧
      matrixMaximumEigenvalue hd (hX k) ≤ b)
    (hμ : 0 < matrixMinimumEigenvalue hd (mean_isHermitian X hX))
    (hu0 : 0 < u) (hu1 : u < 1) :
    let μ := matrixMinimumEigenvalue hd (mean_isHermitian X hX)
    probability (fun Ω : Sample N m =>
      matrixMinimumEigenvalue hd (sampleMean_isHermitian X hX Ω) ≤ (1 - u) * μ) ≤
      (d : ℝ) * Real.exp (-((m : ℝ) * μ / b) *
        (u + (1 - u) * Real.log (1 - u))) := by
  dsimp only
  have hPSD (k : Fin N) : (X k).PosSemidef :=
    (hX k).posSemidef_iff_eigenvalues_nonneg.mpr fun i =>
      (hbound k).1.trans (matrixMinimumEigenvalue_le_eigenvalue hd (hX k) i)
  have hquadratic (k : Fin N) (x : EuclideanSpace ℂ (Fin d)) :
      quadratic (X k) x ≤ b * ‖x‖ ^ 2 :=
    (quadratic_le_matrixMaximumEigenvalue hd (hX k) x).trans
      (mul_le_mul_of_nonneg_right (hbound k).2.2 (sq_nonneg _))
  have h := matrixChernoff_withoutReplacement_lower hN hd hm hmN X hb hPSD
    hquadratic (matrixMinimumEigenvalue_isLeast_rayleigh hd (mean_isHermitian X hX))
    hu0.le hu1
  rw [lower_chernoff_factor_eq_exp hu1] at h
  convert h using 1
  apply congrArg probability
  funext Ω
  apply propext
  rw [sampleMean_minimumEigenvalue_le_iff hd hm X hX Ω]
  have he : (m : ℝ) * ((1 - u) *
      matrixMinimumEigenvalue hd (mean_isHermitian X hX)) =
      (1 - u) * (m : ℝ) * matrixMinimumEigenvalue hd (mean_isHermitian X hX) :=
    (mul_left_comm (m : ℝ) (1 - u) _).trans (mul_assoc _ _ _).symm
  rw [he]

end LeanNumDetect.FiniteMatrixSampling
