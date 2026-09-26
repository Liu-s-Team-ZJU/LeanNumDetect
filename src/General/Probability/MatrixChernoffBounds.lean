import General.Probability.MatrixChernoff
import General.Probability.ChernoffFactors

/-! Conversion of the original matrix Chernoff inequalities to simultaneous
quadratic-form bounds, including the union bound and all normalizations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ComplexOrder
namespace LeanNumDetect.FiniteMatrixSampling

/-- Uniform sampling preserves a fixed positive definite population mean with
an explicit two-tail probability bound. The same lower mean bound is used in
both tail exponents; no Fourier or separation hypothesis occurs here. -/
theorem sampleMean_bounds_probability
    {N d m : ℕ} (hN : 0 < N) (hd : 0 < d) (hm : 1 ≤ m) (hmN : m ≤ N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) {R a b δ : ℝ}
    (hR : 0 < R) (ha : 0 < a) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hX : ∀ k, (X k).PosSemidef)
    (hbound : ∀ k (x : EuclideanSpace ℂ (Fin d)),
      quadratic (X k) x ≤ R * ‖x‖ ^ 2)
    (hmean : ∀ x : EuclideanSpace ℂ (Fin d),
      a * ‖x‖ ^ 2 ≤ quadratic (mean X) x ∧ quadratic (mean X) x ≤ b * ‖x‖ ^ 2) :
    1 - ((d : ℝ) * Real.exp (-((m : ℝ) * a * δ ^ 2) / (2 * R)) +
      (d : ℝ) * Real.exp (-((m : ℝ) * a * δ ^ 2) / (3 * R))) ≤
    probability (fun Ω : Sample N m => ∀ x : EuclideanSpace ℂ (Fin d),
      (1 - δ) * a * ‖x‖ ^ 2 ≤ quadratic (sampleMean X Ω) x ∧
      quadratic (sampleMean X Ω) x ≤ (1 + δ) * b * ‖x‖ ^ 2) := by
  classical
  letI : Nonempty (Sample N m) := sample_nonempty hmN
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨l, u, hl, hu⟩ := exists_rayleigh_extrema hd (mean X)
  have hal : a ≤ l := by
    obtain ⟨x, hx, hq⟩ := hl.1
    simpa only [hx, one_pow, mul_one, hq] using (hmean x).1
  have hub : u ≤ b := by
    obtain ⟨x, hx, hq⟩ := hu.1
    simpa only [hx, one_pow, mul_one, hq] using (hmean x).2
  have hlu : l ≤ u := hl.2 hu.1
  have hau : a ≤ u := hal.trans hlu
  let L : Sample N m → Prop := fun Ω => ∃ x : EuclideanSpace ℂ (Fin d),
    ‖x‖ = 1 ∧ quadratic (sampleSum X Ω) x ≤ (1 - δ) * (m : ℝ) * l
  let U : Sample N m → Prop := fun Ω => ∃ x : EuclideanSpace ℂ (Fin d),
    ‖x‖ = 1 ∧ (1 + δ) * (m : ℝ) * u ≤ quadratic (sampleSum X Ω) x
  have hL : probability L ≤ (d : ℝ) * Real.exp (-((m : ℝ) * a * δ ^ 2) / (2 * R)) := by
    apply (matrixChernoff_withoutReplacement_lower hN hd hm hmN X hR hX hbound hl
      hδ0.le hδ1).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    apply (lower_chernoff_factor_le hδ0.le hδ1
      (div_nonneg (mul_nonneg hmpos.le (ha.le.trans hal)) hR.le)).trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hal
      (show 0 ≤ (m : ℝ) * δ ^ 2 / (2 * R) by positivity)
    convert! neg_le_neg hh using 1 <;> ring
  have hU : probability U ≤ (d : ℝ) * Real.exp (-((m : ℝ) * a * δ ^ 2) / (3 * R)) := by
    apply (matrixChernoff_withoutReplacement_upper hN hd hm hmN X hR hX hbound hu
      hδ0.le).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    apply (upper_chernoff_factor_le hδ0.le hδ1.le
      (div_nonneg (mul_nonneg hmpos.le (ha.le.trans hau)) hR.le)).trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hau
      (show 0 ≤ (m : ℝ) * δ ^ 2 / (3 * R) by positivity)
    convert! neg_le_neg hh using 1 <;> ring
  have hbad := (probability_or_le L U).trans (add_le_add hL hU)
  have hgood := probability_mono (P := fun Ω : Sample N m => ¬ (L Ω ∨ U Ω))
    (Q := fun Ω : Sample N m => ∀ x : EuclideanSpace ℂ (Fin d),
      (1 - δ) * a * ‖x‖ ^ 2 ≤ quadratic (sampleMean X Ω) x ∧
      quadratic (sampleMean X Ω) x ≤ (1 + δ) * b * ‖x‖ ^ 2) (by
    intro Ω hΩ
    apply bounds_of_unit_bounds
    intro x hx
    have hlow : (1 - δ) * (m : ℝ) * l < quadratic (sampleSum X Ω) x :=
      lt_of_not_ge (fun hh => hΩ (Or.inl ⟨x, hx, hh⟩))
    have hupp : quadratic (sampleSum X Ω) x < (1 + δ) * (m : ℝ) * u :=
      lt_of_not_ge (fun hh => hΩ (Or.inr ⟨x, hx, hh⟩))
    have he : quadratic (sampleMean X Ω) x =
        (m : ℝ)⁻¹ * quadratic (sampleSum X Ω) x := by
      simpa only [sampleMean, Complex.ofReal_inv, Complex.ofReal_natCast] using
        quadratic_smul_matrix (sampleSum X Ω) (m : ℝ)⁻¹ x
    rw [he]
    have hl' := mul_le_mul_of_nonneg_left hal (show 0 ≤ (1 - δ) * (m : ℝ) by positivity)
    have hu' := mul_le_mul_of_nonneg_left hub (show 0 ≤ (1 + δ) * (m : ℝ) by positivity)
    constructor
    · rw [mul_comm (m : ℝ)⁻¹]
      apply (le_mul_inv_iff₀ hmpos).mpr
      nlinarith
    · apply (inv_mul_le_iff₀ hmpos).mpr
      nlinarith)
  rw [probability_not] at hgood
  linarith

end LeanNumDetect.FiniteMatrixSampling
