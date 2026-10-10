import General.Probability.RelativeMatrixSampling

/-! Exact lower Chernoff factors permit a factor-two loss in the retained Gram
energy while increasing the admissible leverage budget from `3*S/2` to `5*S/2`.
All logarithmic estimates and whitening transfers are proved in this file. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace LeanNumDetect.FiniteMatrixSampling

private theorem neg_log_lower_five {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    δ + δ^2/2 + δ^3/3 + δ^4/4 + δ^5/5 ≤ -Real.log (1-δ) := by
  let f : ℝ → ℝ := fun x => -Real.log (1-x) -
    (x + x^2/2 + x^3/3 + x^4/4 + x^5/5)
  have hd (x : ℝ) (hx : x ∈ Set.Icc 0 δ) : HasDerivAt f (x^5/(1-x)) x := by
    have hn : 1-x ≠ 0 := by linarith [hx.2]
    have hid := hasDerivAt_id x
    have hsub := (hasDerivAt_const x 1).sub hid
    have hlog := (Real.hasDerivAt_log hn).comp x hsub
    convert! hlog.neg.sub ((((hid.add ((hid.pow 2).div_const 2)).add
      ((hid.pow 3).div_const 3)).add ((hid.pow 4).div_const 4)).add
      ((hid.pow 5).div_const 5)) using 1
    dsimp
    field_simp
    ring
  have hc : ContinuousOn f (Set.Icc 0 δ) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hmono : MonotoneOn f (Set.Icc 0 δ) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 δ) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (by
        intro x hx
        have hx' : x ∈ Set.Icc 0 δ := interior_subset hx
        exact div_nonneg (pow_nonneg hx'.1 _) (by linarith [hx'.2]))
  have h := hmono (show 0 ∈ Set.Icc 0 δ from ⟨le_rfl,hδ0⟩)
    (show δ ∈ Set.Icc 0 δ from ⟨hδ0,le_rfl⟩) hδ0
  norm_num [f] at h ⊢
  linarith

private theorem lower_log_bound_six {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    δ^2/2 + δ^3/6 + δ^4/12 + δ^5/20 + δ^6/30 ≤
      δ + (1-δ)*Real.log (1-δ) := by
  let f : ℝ → ℝ := fun x => x + (1-x)*Real.log (1-x) -
    (x^2/2 + x^3/6 + x^4/12 + x^5/20 + x^6/30)
  have hd (x : ℝ) (hx : x ∈ Set.Icc 0 δ) :
      HasDerivAt f (-Real.log (1-x) - (x + x^2/2 + x^3/3 + x^4/4 + x^5/5)) x := by
    have hn : 1-x ≠ 0 := by linarith [hx.2]
    have hid := hasDerivAt_id x
    have hsub := (hasDerivAt_const x 1).sub hid
    have hlog := (Real.hasDerivAt_log hn).comp x hsub
    convert! (hid.add (hsub.mul hlog)).sub (((((hid.pow 2).div_const 2).add
      ((hid.pow 3).div_const 6)).add ((hid.pow 4).div_const 12)).add
      ((hid.pow 5).div_const 20) |>.add ((hid.pow 6).div_const 30)) using 1
    dsimp
    field_simp
    ring
  have hc : ContinuousOn f (Set.Icc 0 δ) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hmono : MonotoneOn f (Set.Icc 0 δ) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 δ) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (by
        intro x hx
        have hx' : x ∈ Set.Icc 0 δ := interior_subset hx
        exact sub_nonneg.mpr (neg_log_lower_five hx'.1 (by linarith [hx'.2])))
  have h := hmono (show 0 ∈ Set.Icc 0 δ from ⟨le_rfl,hδ0⟩)
    (show δ ∈ Set.Icc 0 δ from ⟨hδ0,le_rfl⟩) hδ0
  norm_num [f] at h ⊢
  linarith

/-- The half-energy threshold has lower-tail entropy at least `5*ρ²/6`. -/
theorem lower_log_bound_half_slack {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    5*ρ^2/6 ≤ (1+ρ)/2 + (1-(1+ρ)/2)*Real.log (1-(1+ρ)/2) := by
  have hb := lower_log_bound_six (δ := (1+ρ)/2) (by linarith) (by linarith)
  have hp2 : ρ^2 ≤ ρ := by nlinarith
  have hp3 : ρ^3 ≤ ρ := by nlinarith [mul_le_mul_of_nonneg_right hp2 hρ0]
  have hp4 : ρ^4 ≤ ρ := by nlinarith [mul_le_mul_of_nonneg_right hp3 hρ0]
  have hp5 : ρ^5 ≤ ρ := by nlinarith [mul_le_mul_of_nonneg_right hp4 hρ0]
  have hf : 0 ≤ (1-ρ)*(294+955*ρ-180*ρ^2-50*ρ^3-10*ρ^4-ρ^5) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have hid : ((1+ρ)/2)^2/2 + ((1+ρ)/2)^3/6 + ((1+ρ)/2)^4/12 +
      ((1+ρ)/2)^5/20 + ((1+ρ)/2)^6/30 - 5*ρ^2/6 =
      (1-ρ)*(294+955*ρ-180*ρ^2-50*ρ^3-10*ρ^4-ρ^5)/1920 := by ring
  nlinarith

/-- Exact Chernoff factor at the half-energy threshold. -/
theorem lower_chernoff_factor_half_slack_le {ρ t : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (ht : 0 ≤ t) :
    (Real.exp (-((1+ρ)/2)) / (1-(1+ρ)/2) ^ (1-(1+ρ)/2)) ^ t ≤
      Real.exp (-(5*t*ρ^2)/6) := by
  have hp : 0 < 1-(1+ρ)/2 := by linarith
  rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hp _)),
    Real.log_div (Real.exp_ne_zero _) (ne_of_gt (Real.rpow_pos_of_pos hp _)),
    Real.log_exp, Real.log_rpow hp]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (lower_log_bound_half_slack hρ0 hρ1) ht
  nlinarith

/-- A lower sample-mean estimate retaining half the relative energy. -/
theorem sampleMean_half_lower_bound_probability
    {N d m : ℕ} (hN : 0 < N) (hd : 0 < d) (hm : 1 ≤ m) (hmN : m ≤ N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) {R a ρ : ℝ}
    (hR : 0 < R) (ha : 0 < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hX : ∀ k, (X k).PosSemidef)
    (hbound : ∀ k (x : EuclideanSpace ℂ (Fin d)),
      quadratic (X k) x ≤ R * ‖x‖ ^ 2)
    (hmean : ∀ x : EuclideanSpace ℂ (Fin d),
      a * ‖x‖ ^ 2 ≤ quadratic (mean X) x) :
    1 - (d : ℝ) * Real.exp (-(5 * (m : ℝ) * a * ρ ^ 2) / (6 * R)) ≤
      probability (fun Ω : Sample N m => ∀ x : EuclideanSpace ℂ (Fin d),
        (1 - (1 + ρ)/2) * a * ‖x‖ ^ 2 ≤ quadratic (sampleMean X Ω) x) := by
  classical
  let δ := (1 + ρ)/2
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  letI : Nonempty (Sample N m) := sample_nonempty hmN
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨l, _, hl, _⟩ := exists_rayleigh_extrema hd (mean X)
  have hal : a ≤ l := by
    obtain ⟨x, hx, hq⟩ := hl.1
    simpa only [hx, one_pow, mul_one, hq] using hmean x
  let L : Sample N m → Prop := fun Ω => ∃ x : EuclideanSpace ℂ (Fin d),
    ‖x‖ = 1 ∧ quadratic (sampleSum X Ω) x ≤ (1 - δ) * (m : ℝ) * l
  have hL : probability L ≤ (d : ℝ) * Real.exp (-(5 * (m : ℝ) * a * ρ ^ 2) / (6 * R)) := by
    apply (matrixChernoff_withoutReplacement_lower hN hd hm hmN X hR hX hbound hl
      hδ0.le hδ1).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    apply (lower_chernoff_factor_half_slack_le hρ0.le hρ1
      (div_nonneg (mul_nonneg hmpos.le (ha.le.trans hal)) hR.le)).trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hal
      (show 0 ≤ 5 * (m : ℝ) * ρ ^ 2 / (6 * R) by positivity)
    convert! neg_le_neg hh using 1 <;> ring
  have hgood := probability_mono (P := fun Ω : Sample N m => ¬ L Ω)
    (Q := fun Ω : Sample N m => ∀ x : EuclideanSpace ℂ (Fin d),
      (1 - δ) * a * ‖x‖ ^ 2 ≤ quadratic (sampleMean X Ω) x) (by
    intro Ω hΩ x
    by_cases hx : x = 0
    · simp [hx]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y := (‖x‖⁻¹ : ℂ) • x
    have hy : ‖y‖ = 1 := norm_smul_inv_norm hx
    have hlow : (1 - δ) * (m : ℝ) * l < quadratic (sampleSum X Ω) y :=
      lt_of_not_ge (fun hh => hΩ ⟨y, hy, hh⟩)
    have hscaled : (1 - δ) * (m : ℝ) * a ≤ quadratic (sampleSum X Ω) y := by
      have h := mul_le_mul_of_nonneg_left hal
        (show 0 ≤ (1 - δ) * (m : ℝ) by positivity)
      exact h.trans hlow.le
    have he : quadratic (sampleMean X Ω) x =
        (m : ℝ)⁻¹ * quadratic (sampleSum X Ω) x := by
      simpa only [sampleMean, Complex.ofReal_inv, Complex.ofReal_natCast] using
        quadratic_smul_matrix (sampleSum X Ω) (m : ℝ)⁻¹ x
    have hyq : quadratic (sampleSum X Ω) y =
        ‖x‖⁻¹ ^ 2 * quadratic (sampleSum X Ω) x := by
      simpa only [y, ← Complex.ofReal_inv] using
        quadratic_real_smul (sampleSum X Ω) ‖x‖⁻¹ x
    rw [hyq] at hscaled
    have hmul := mul_le_mul_of_nonneg_right hscaled (sq_nonneg ‖x‖)
    have hcancel : (‖x‖⁻¹ ^ 2 * quadratic (sampleSum X Ω) x) * ‖x‖^2 =
        quadratic (sampleSum X Ω) x := by
      field_simp
    rw [hcancel] at hmul
    rw [he, mul_comm (m : ℝ)⁻¹]
    apply (le_mul_inv_iff₀ hmpos).mpr
    nlinarith)
  rw [probability_not] at hgood
  linarith


/-- Relative lower concentration for a leverage budget of `5*S/2`, with the
same exponent as the Gaussian bound with budget `3*S/2`. -/
theorem sampleMean_relative_half_lower_bound_probability
    {N d m : ℕ} (hN : 0 < N) (hd : 0 < d) (hm : 1 ≤ m) (hmN : m ≤ N)
    (X : Fin N → Matrix (Fin d) (Fin d) ℂ) {S ρ : ℝ}
    (hS : 0 < S) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hX : ∀ k, (X k).PosSemidef) (hG : (mean X).PosDef)
    (hbound : ∀ k (x : EuclideanSpace ℂ (Fin d)),
      quadratic (X k) x ≤ (5/2 : ℝ) * S * quadratic (mean X) x) :
    1 - (d : ℝ) * Real.exp (-((m : ℝ) * ρ ^ 2) / (3 * S)) ≤
      probability (fun Ω : Sample N m => ∀ x : EuclideanSpace ℂ (Fin d),
        (1 - (1 + ρ)/2) * quadratic (mean X) x ≤ quadratic (sampleMean X Ω) x) := by
  obtain ⟨P, hP, hwhite⟩ := exists_whitening_matrix (mean X) hG
  letI := hP.invertible
  let W := fun k => Pᴴ * X k * P
  have hmean : mean W = 1 := by rw [mean_congruence, hwhite]
  have hmetric (x : EuclideanSpace ℂ (Fin d)) :
      quadratic (mean X) (P.toEuclideanLin x) = ‖x‖ ^ 2 := by
    rw [← quadratic_congruence, hwhite, quadratic_identity]
  have hprob := sampleMean_half_lower_bound_probability hN hd hm hmN W
    (R := (5/2 : ℝ) * S) (by positivity)
    (by norm_num : (0 : ℝ) < 1) hρ0 hρ1
    (fun k => (hX k).conjTranspose_mul_mul_same P)
    (fun k x => by
      rw [quadratic_congruence]
      simpa only [hmetric] using hbound k (P.toEuclideanLin x))
    (a := 1) (fun x => by simp [hmean])
  have he : -(5 * (m : ℝ) * 1 * ρ^2)/(6*((5/2 : ℝ)*S)) =
      -((m : ℝ)*ρ^2)/(3*S) := by field_simp; ring
  rw [he] at hprob
  apply hprob.trans
  apply probability_mono
  intro Ω hΩ x
  let y := P⁻¹.toEuclideanLin x
  have hxy : P.toEuclideanLin y = x := by
    change (P.toEuclideanLin ∘ₗ P⁻¹.toEuclideanLin) x = x
    rw [← Matrix.toLpLin_mul_same, Matrix.mul_inv_of_invertible]
    simp
  have hy := hΩ y
  rw [sampleMean_congruence, quadratic_congruence, ← hmetric y, hxy] at hy
  simpa only [mul_one] using hy


end LeanNumDetect.FiniteMatrixSampling
