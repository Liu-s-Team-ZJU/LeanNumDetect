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
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
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

end LeanNumDetect.FiniteMatrixSampling
