import General.Probability.SmoothWeightExistence
import General.Probability.CappedWeightSpectralCoercivity

/-! Subspace-thickness alternatives for the smooth frame potential.
These reusable threshold, coercivity, minimizer and determinant estimates are
independent of the direct logarithmic-frame sampling proof. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace LeanNumDetect.FiniteMatrixSampling

open FrameMatrixBounds
noncomputable section
attribute [local instance] Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Finite threshold counts imply the smooth logarithmic spectral estimate. -/
theorem sum_smoothEntropy_spectral_lower_radius {n : ℕ} (_hn : 0 < n)
    {R : ℝ} (hR : 0 < R) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis (Fin n) ℂ E) (eig : Fin n → ℝ)
    (heig : ∀ j, 0 < eig j) (hanti : Antitone eig) (q : E → ℝ)
    (hq : ∀ x, q x = ∑ j, eig j * ‖⟪b j, x⟫_ℂ‖ ^ 2)
    (f : ι → E) {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ E,
      ((Fintype.card ι : ℝ) * ((n : ℝ) + 1) / (2 * (n : ℝ) ^ 2)) *
        ((n - Module.finrank ℂ U : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun i => ∀ u : U, θ < ‖f i - (u : E)‖)).card : ℝ)) :
    R * ((Fintype.card ι : ℝ) * ((n : ℝ) + 1) / (2 * (n : ℝ) ^ 2)) *
      (∑ j, Real.log (1 + θ ^ 2 * eig j / R)) ≤
      ∑ i, smoothEntropy R (q (f i)) := by
  classical
  let a : ℕ → ℝ := fun j =>
    if hj : j < n then Real.log (1 + θ ^ 2 * eig ⟨j, hj⟩ / R) else 0
  let p := (Fintype.card ι : ℝ) * ((n : ℝ) + 1) / (2 * (n : ℝ) ^ 2)
  have ha : ∀ k < n, a (k + 1) ≤ a k := by
    intro k hk
    by_cases hk' : k + 1 < n
    · simp only [a, dif_pos hk', dif_pos hk]
      have hp := heig ⟨k + 1, hk'⟩
      apply Real.log_le_log (by positivity)
      have hh := hanti (by change k ≤ k + 1; omega :
        (⟨k, hk⟩ : Fin n) ≤ ⟨k + 1, hk'⟩)
      gcongr
    · simp only [a, dif_neg hk', dif_pos hk]
      apply Real.log_nonneg
      have hp := heig ⟨k, hk⟩
      have hx : 0 ≤ θ ^ 2 * eig ⟨k, hk⟩ / R := by positivity
      linarith
  have han : a n = 0 := by simp [a]
  have hqpos (i : ι) : 0 ≤ q (f i) := by
    rw [hq]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (heig j).le (sq_nonneg _))
  have hb (i : ι) : 0 ≤ Real.log (1 + q (f i) / R) := by
    apply Real.log_nonneg
    have hh := div_nonneg (hqpos i) hR.le
    linarith
  have hcount : ∀ k < n, p * ((k : ℝ) + 1) ≤
      ((Finset.univ.filter (fun i => a k ≤ Real.log (1 + q (f i) / R))).card : ℝ) := by
    intro k hk
    have hc := hthick (basisTailSpace b (k + 1))
    rw [finrank_basisTailSpace b (by omega)] at hc
    have hnsub : n - (n - (k + 1)) = k + 1 := by omega
    rw [hnsub, Nat.cast_add, Nat.cast_one] at hc
    change p * ((k : ℝ) + 1) ≤ _ at hc
    apply hc.trans
    exact_mod_cast (show
      (Finset.univ.filter (fun i =>
        ∀ u : basisTailSpace b (k + 1), θ < ‖f i - (u : E)‖)).card ≤
      (Finset.univ.filter (fun i => a k ≤ Real.log (1 + q (f i) / R))).card from by
        apply Finset.card_le_card
        intro i hi
        have hfar := (Finset.mem_filter.mp hi).2
        have hqf := spectral_prefix_lower_of_far b eig heig hanti q hq
          ⟨k, hk⟩ (f i) hθ hfar
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [a, dif_pos hk]
        have hp := heig ⟨k, hk⟩
        simpa only [add_comm] using (Real.log_lt_log (by positivity)
          (add_lt_add_left (div_lt_div_of_pos_right hqf hR) 1)).le)
  have hh := sum_lower_of_threshold_counts a (fun i => Real.log (1 + q (f i) / R))
    n p hb ha han hcount
  have hs : (∑ k ∈ Finset.range n, a k) =
      ∑ j, Real.log (1 + θ ^ 2 * eig j / R) := by
    rw [← Fin.sum_univ_eq_sum_range a n]
    apply Finset.sum_congr rfl
    intro j _
    simp only [a, dif_pos j.prop]
  rw [hs] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hR.le
  simpa only [smoothEntropy, Finset.mul_sum, mul_assoc] using hh'

/-- The smooth spectral estimate for an arbitrary positive-definite matrix. -/
theorem matrix_sum_smoothEntropy_spectral_lower_radius {n : ℕ} (hn : 0 < n)
    {R : ℝ} (hR : 0 < R) {ι : Type*} [Fintype ι]
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (f : ι → EuclideanSpace ℂ (Fin n)) {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      ((Fintype.card ι : ℝ) * ((n : ℝ) + 1) / (2 * (n : ℝ) ^ 2)) *
        ((n - Module.finrank ℂ U : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun i =>
        ∀ u : U, θ < ‖f i - (u : EuclideanSpace ℂ (Fin n))‖)).card : ℝ)) :
    R * ((Fintype.card ι : ℝ) * ((n : ℝ) + 1) / (2 * (n : ℝ) ^ 2)) *
      (∑ j, Real.log (1 + θ ^ 2 * hH.isHermitian.eigenvalues j / R)) ≤
      ∑ i, smoothEntropy R (quadratic H (f i)) := by
  classical
  let σ := Tuple.sort (fun j => -hH.isHermitian.eigenvalues j)
  let eig := fun j => hH.isHermitian.eigenvalues (σ j)
  let b := hH.isHermitian.eigenvectorBasis.reindex σ.symm
  have hp : ∀ j, 0 < eig j := fun j => hH.eigenvalues_pos (σ j)
  have ha : Antitone eig := by
    intro i j hij
    have hh := Tuple.monotone_sort (fun j => -hH.isHermitian.eigenvalues j) hij
    dsimp [Function.comp_def] at hh
    exact neg_le_neg_iff.mp hh
  have hq (x : EuclideanSpace ℂ (Fin n)) :
      quadratic H x = ∑ j, eig j * ‖⟪b j, x⟫_ℂ‖ ^ 2 := by
    rw [TraceExponential.quadratic_eq_sum hH.isHermitian]
    have hh := Equiv.sum_comp σ (fun j => hH.isHermitian.eigenvalues j *
      ‖⟪hH.isHermitian.eigenvectorBasis j, x⟫_ℂ‖ ^ 2)
    simpa only [eig, b, OrthonormalBasis.coe_reindex, Equiv.symm_symm,
      Function.comp_apply] using hh.symm
  have hh := sum_smoothEntropy_spectral_lower_radius hn hR b eig hp ha
    (quadratic H) hq f hθ hthick
  have hs := Equiv.sum_comp σ (fun j =>
    Real.log (1 + θ ^ 2 * hH.isHermitian.eigenvalues j / R))
  simp only [eig] at hh
  rw [hs] at hh
  exact hh

/-- With radius `12*n/5`, the averaged entropy dominates the spectral log tails. -/
theorem smooth_entropyMean_spectral_six_fifths {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι)
    (f : ι → EuclideanSpace ℂ (Fin n)) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (n + 1) * (n - Module.finrank ℂ U) * Fintype.card ι ≤
      2 * n ^ 2 * (Finset.univ.filter (fun i =>
        ∀ u : U, θ < ‖f i - (u : EuclideanSpace ℂ (Fin n))‖)).card) :
    (6 / 5 : ℝ) * (∑ j,
      Real.log (1 + θ ^ 2 * hA.isHermitian.eigenvalues j / ((12 / 5 : ℝ) * n))) ≤
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ i, smoothEntropy ((12 / 5 : ℝ) * n) (quadratic A (f i)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hι' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
  have hh := matrix_sum_smoothEntropy_spectral_lower_radius hn
    (R := (12 / 5 : ℝ) * n) (by positivity) A hA f hθ
    (thickness_real_of_card hn f θ hthick)
  have hs : ((12 / 5 : ℝ) * n) * (((n : ℝ) + 1) / (2 * (n : ℝ) ^ 2)) *
      (∑ j, Real.log (1 + θ ^ 2 * hA.isHermitian.eigenvalues j / ((12 / 5 : ℝ) * n))) ≤
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ i, smoothEntropy ((12 / 5 : ℝ) * n) (quadratic A (f i)) := by
    apply (le_inv_mul_iff₀ hι').mpr
    convert hh using 1 <;> first | rfl | ring
  have hfactor : (6 / 5 : ℝ) ≤
      ((12 / 5 : ℝ) * n) * (((n : ℝ) + 1) / (2 * (n : ℝ) ^ 2)) := by
    rw [← mul_div_assoc, le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ) ^ 2)]
    nlinarith
  apply le_trans (mul_le_mul_of_nonneg_right hfactor ?_) hs
  apply Finset.sum_nonneg
  intro j _
  apply Real.log_nonneg
  have hp := hA.eigenvalues_pos j
  have hx : 0 ≤ θ ^ 2 * hA.isHermitian.eigenvalues j / ((12 / 5 : ℝ) * n) := by positivity
  linarith

/-- Subspace thickness supplies the logarithmic entropy hypothesis. -/
theorem smoothFramePotential_logEigenvalues_abs_sum_le {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι)
    (f : ι → EuclideanSpace ℂ (Fin n)) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (n + 1) * (n - Module.finrank ℂ U) * Fintype.card ι ≤
      2 * n ^ 2 * (Finset.univ.filter (fun i =>
        ∀ u : U, θ < ‖f i - (u : EuclideanSpace ℂ (Fin n))‖)).card)
    (hpotential : smoothFramePotential f ((12 / 5 : ℝ) * n) A ≤ (n : ℝ)) :
    (∑ j, |Real.log (hA.isHermitian.eigenvalues j)|) ≤
      5 * (n : ℝ) + 6 * (n : ℝ) * max 0 (Real.log (((12 / 5 : ℝ) * n) / θ ^ 2)) := by
  exact smoothFramePotential_logEigenvalues_abs_sum_le_of_entropy hn hι f A hA hθ
    (smooth_entropyMean_spectral_six_fifths hn hι f A hA hθ hthick) hpotential

/-- Subspace thickness supplies the logarithmic entropy hypothesis. -/
theorem smoothFramePotential_sublevel_mem_interval {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι)
    (f : ι → EuclideanSpace ℂ (Fin n)) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (n + 1) * (n - Module.finrank ℂ U) * Fintype.card ι ≤
      2 * n ^ 2 * (Finset.univ.filter (fun i =>
        ∀ u : U, θ < ‖f i - (u : EuclideanSpace ℂ (Fin n))‖)).card)
    (hpotential : smoothFramePotential f ((12 / 5 : ℝ) * n) A ≤ (n : ℝ)) :
    A ∈ hermitianQuadraticInterval n
      (Real.exp (-(5 * (n : ℝ) +
        6 * (n : ℝ) * max 0 (Real.log (((12 / 5 : ℝ) * n) / θ ^ 2)))))
      (Real.exp (5 * (n : ℝ) +
        6 * (n : ℝ) * max 0 (Real.log (((12 / 5 : ℝ) * n) / θ ^ 2)))) := by
  exact smoothFramePotential_sublevel_mem_interval_of_entropy hn hι f A hA hθ
    (smooth_entropyMean_spectral_six_fifths hn hι f A hA hθ hthick) hpotential

/-- The smooth potential attains a minimum under subspace thickness. -/
theorem exists_smoothFramePotential_minimizer {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    (f : Fin N → EuclideanSpace ℂ (Fin n)) (hfull : mean (framePopulation f) = 1)
    {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (n + 1) * (n - Module.finrank ℂ U) * N ≤
      2 * n ^ 2 * (Finset.univ.filter (fun i =>
        ∀ u : U, θ < ‖f i - (u : EuclideanSpace ℂ (Fin n))‖)).card) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosDef ∧
      ∀ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef →
        smoothFramePotential f ((12 / 5 : ℝ) * n) A ≤
          smoothFramePotential f ((12 / 5 : ℝ) * n) H := by
  exact exists_smoothFramePotential_minimizer_of_entropy hN hn f hfull hθ
    (fun H hH => by
      simpa only [Fintype.card_fin] using smooth_entropyMean_spectral_six_fifths hn
        (by simpa using hN) f H hH hθ (by simpa using hthick))

/-- Inverting a positive-definite matrix inverts its real determinant. -/
theorem smooth_det_inverse_re {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) : (A⁻¹).det.re = (A.det.re)⁻¹ := by
  have hd : A.det = (A.det.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (RCLike.pos_iff.mp hA.det_pos).2
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hd]
  simp

/-- The smooth potential retains the quantitative inverse-determinant floor. -/
theorem smoothFramePotential_realDet_inverse_lower_slack_of_card {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι)
    (f : ι → EuclideanSpace ℂ (Fin n)) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (n + 1) * (n - Module.finrank ℂ U) * Fintype.card ι ≤
      2 * n ^ 2 * (Finset.univ.filter (fun i =>
        ∀ u : U, θ < ‖f i - (u : EuclideanSpace ℂ (Fin n))‖)).card)
    (hpotential : smoothFramePotential f ((12 / 5 : ℝ) * n) A ≤ (n : ℝ)) :
    Real.exp (-(5 * (n : ℝ) +
      6 * (n : ℝ) * Real.log (((12 / 5 : ℝ) * n) / θ ^ 2))) ≤ (A⁻¹).det.re := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let R := (12 / 5 : ℝ) * n
  have hR : 0 < R := by dsimp [R]; positivity
  let C := Real.log (R / θ ^ 2)
  let t := fun j => Real.log (hA.isHermitian.eigenvalues j)
  let hmean := (Fintype.card ι : ℝ)⁻¹ * ∑ i, smoothEntropy R (quadratic A (f i))
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
  have hentropy := smooth_entropyMean_spectral_six_fifths hn hι f A hA hθ hthick
  have hupper : -(∑ j, t j) + hmean ≤ (n : ℝ) := by
    simpa only [smoothFramePotential, smooth_log_det_eq_sum hA] using hpotential
  have hs : (∑ j, t j) ≤ 5 * (n : ℝ) + 6 * (n : ℝ) * C := by
    change (6 / 5 : ℝ) * (∑ j,
      Real.log (1 + θ ^ 2 * hA.isHermitian.eigenvalues j / R)) ≤ hmean at hentropy
    linarith
  have hl : -(5 * (n : ℝ) + 6 * (n : ℝ) * C) ≤ Real.log ((A⁻¹).det.re) := by
    rw [smooth_det_inverse_re hA, Real.log_inv, smooth_log_det_eq_sum hA]
    exact neg_le_neg hs
  have he := Real.exp_le_exp.mpr hl
  have hdpos : 0 < (A⁻¹).det.re := by
    simpa only [RCLike.re_eq_complex_re] using (RCLike.pos_iff.mp hA.inv.det_pos).1
  rw [Real.exp_log hdpos] at he
  exact he

end
end LeanNumDetect.FiniteMatrixSampling
