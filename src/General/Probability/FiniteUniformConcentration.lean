import General.Probability.FiniteCenteredConcentration
import General.Probability.FiniteUnion

/-! Uniform concentration from a finite net, for complex-valued populations
sampled uniformly without replacement. -/

set_option autoImplicit false

open scoped BigOperators

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section

/-- A finite net with deterministic extension error `ε / 2` converts centered
complex Hoeffding tails into one event controlling the entire parameter set. -/
theorem finiteSample_uniform_complex_probability_ge
    {κ ι τ : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    {m : ℕ} (hm : 1 ≤ m) (hmκ : m ≤ Fintype.card κ)
    (f : τ → κ → ℂ) (hbound : ∀ t k, ‖f t k‖ ≤ 1)
    (grid : ι → τ) {ε : ℝ} (hε : 0 < ε)
    (hcover : ∀ (Ω : FiniteSample κ m) t, ∃ i : ι,
      ‖(m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f t k -
          (Fintype.card κ : ℂ)⁻¹ * ∑ k, f t k‖ ≤
        ‖(m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f (grid i) k -
          (Fintype.card κ : ℂ)⁻¹ * ∑ k, f (grid i) k‖ + ε / 2) :
    1 - (Fintype.card ι : ℝ) *
        (4 * Real.exp (-(m : ℝ) * ε ^ 2 / 16)) ≤
      probability (fun Ω : FiniteSample κ m => ∀ t,
        ‖(m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f t k -
          (Fintype.card κ : ℂ)⁻¹ * ∑ k, f t k‖ ≤ ε) := by
  classical
  letI : Nonempty (FiniteSample κ m) := finiteSample_nonempty hmκ
  have h := probability_forall_finset_ge (Finset.univ : Finset ι)
    (fun i (Ω : FiniteSample κ m) =>
      ‖(m : ℂ)⁻¹ * ∑ k ∈ Ω.val, f (grid i) k -
        (Fintype.card κ : ℂ)⁻¹ * ∑ k, f (grid i) k‖ ≤ ε / 2)
    (b := 4 * Real.exp (-(m : ℝ) * ε ^ 2 / 16)) (by
      intro i _
      have hi := finiteSample_complex_centered_norm_probability_le hm hmκ
        (f (grid i)) (hbound (grid i)) (by positivity : 0 < ε / 2)
      convert hi using 1 <;> try simp only [not_le]
      congr 2
      ring)
  simp only [Finset.card_univ] at h
  apply h.trans
  apply probability_mono
  intro Ω hΩ t
  obtain ⟨i, hi⟩ := hcover Ω t
  have hi' := hΩ i (Finset.mem_univ i)
  linarith

/-- Exact logarithmic threshold for the finite-net tail. -/
theorem finite_net_failure_bound_of_sample_size {Q m ε η : ℝ}
    (hQ : 0 < Q) (hε : 0 < ε) (hη : 0 < η)
    (hsample : 16 / ε ^ 2 * Real.log (4 * Q / η) ≤ m) :
    Q * (4 * Real.exp (-m * ε ^ 2 / 16)) ≤ η := by
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hlog : Real.log (4 * Q / η) ≤ m * ε ^ 2 / 16 := by
    have hh := (div_le_iff₀ hεsq).1
      (show (16 * Real.log (4 * Q / η)) / ε ^ 2 ≤ m by
        simpa only [div_mul_eq_mul_div] using hsample)
    linarith
  have hexp : Real.exp (-Real.log (4 * Q / η)) = η / (4 * Q) := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    exact inv_div _ _
  have htail : Real.exp (-m * ε ^ 2 / 16) ≤ η / (4 * Q) := by
    rw [← hexp]
    apply Real.exp_le_exp.mpr
    linarith
  calc
    Q * (4 * Real.exp (-m * ε ^ 2 / 16)) ≤
        Q * (4 * (η / (4 * Q))) := by gcongr
    _ = η := by field_simp

end

end LeanNumDetect.FiniteMatrixSampling
