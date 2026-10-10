import General.Probability.CappedWeightEntropy
import General.MatrixAnalysis.HermitianVariational
import General.MatrixAnalysis.TraceExponential
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.Matrix.Order
import General.MatrixAnalysis.CappedWeightIteration

/-! Uniform subspace thickness yields coercivity of the capped frame potential.
The determinant floor uses only finite sums and spectral decomposition. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder

namespace LeanNumDetect.FiniteMatrixSampling

noncomputable section

attribute [local instance] Classical.propDecidable

def framePotential {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → EuclideanSpace ℂ (Fin n)) (R : ℝ) (G : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.log (G.det.re) +
    (Fintype.card ι : ℝ)⁻¹ * ∑ i, cappedEntropy R (quadratic G⁻¹ (f i))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def basisTailSpace {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ E) (k : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ (b '' {j | k ≤ j.val})

def basisTailPart {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ E) (k : ℕ) (x : E) : E :=
  b.repr.symm (toLp 2 (fun j => if k ≤ j.val then b.repr x j else 0))

omit [FiniteDimensional ℂ E] in
theorem basisTailPart_mem {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ E) (k : ℕ) (x : E) :
    basisTailPart b k x ∈ basisTailSpace b k := by
  classical
  apply b.toBasis.mem_span_image.mpr
  intro j hj
  by_contra h
  have h' : ¬ k ≤ j.val := by simpa using h
  have he : b.toBasis.repr (basisTailPart b k x) j = 0 := by
    simp [OrthonormalBasis.coe_toBasis_repr_apply, basisTailPart, h']
  exact (Finsupp.mem_support_iff.mp hj) he

omit [FiniteDimensional ℂ E] in
theorem basisTailPart_residual_sq {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ E)
    (k : ℕ) (x : E) :
    ‖x-basisTailPart b k x‖^2 =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), ‖⟪b j,x⟫_ℂ‖^2 := by
  classical
  rw [← b.repr.norm_map (x-basisTailPart b k x), LinearIsometryEquiv.map_sub,
    basisTailPart, b.repr.apply_symm_apply, EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : k ≤ j.val
  · simp [hj, show ¬j.val < k by omega]
  · simp [hj, show j.val < k by omega, OrthonormalBasis.repr_apply_apply]

theorem finrank_basisTailSpace {n k : ℕ} (b : OrthonormalBasis (Fin n) ℂ E) (hk : k ≤ n) :
    Module.finrank ℂ (basisTailSpace b k) = n-k := by
  classical
  let s := Finset.univ.filter (fun j : Fin n => k ≤ j.val)
  have hs : (s : Set (Fin n)) = {j | k ≤ j.val} := by ext j; simp [s]
  rw [basisTailSpace, ← hs, finrank_orthonormal_span]
  let e : s ≃ Fin (n-k) :=
    { toFun := fun j => ⟨j.val.val-k, by
        have hj : k ≤ j.val.val := (Finset.mem_filter.mp j.property).2
        omega⟩
      invFun := fun j => ⟨⟨j.val+k, by omega⟩, by simp [s]⟩
      left_inv := by intro j; apply Subtype.ext; apply Fin.ext; dsimp
                     have hj : k ≤ j.val.val := (Finset.mem_filter.mp j.property).2
                     omega
      right_inv := by intro j; apply Fin.ext; dsimp; omega }
  have he := Fintype.card_congr e
  simpa only [Fintype.card_coe, Fintype.card_fin] using he

omit [FiniteDimensional ℂ E] in
theorem spectral_prefix_lower_of_far {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ E) (eig : Fin n → ℝ)
    (heig : ∀ j, 0 < eig j) (hanti : Antitone eig) (q : E → ℝ)
    (hq : ∀ x, q x = ∑ j, eig j*‖⟪b j,x⟫_ℂ‖^2)
    (k : Fin n) (x : E) {θ : ℝ} (hθ : 0 < θ)
    (hfar : ∀ u : basisTailSpace b (k.val+1), θ < ‖x-(u : E)‖) :
    θ^2*eig k < q x := by
  classical
  have hf := hfar ⟨basisTailPart b (k.val+1) x, basisTailPart_mem b _ x⟩
  have hh := (sq_lt_sq₀ hθ.le (norm_nonneg _)).mpr hf
  rw [basisTailPart_residual_sq] at hh
  have hs : eig k*(∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val+1),
      ‖⟪b j,x⟫_ℂ‖^2) ≤ q x := by
    rw [hq, Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j.val < k.val+1
    · rw [if_pos hj]
      exact mul_le_mul_of_nonneg_right (hanti (by omega : j ≤ k)) (sq_nonneg _)
    · rw [if_neg hj]
      exact mul_nonneg (heig j).le (sq_nonneg _)
  have hm := mul_lt_mul_of_pos_left hh (heig k)
  simpa only [mul_comm] using hm.trans_le hs

theorem sum_cappedEntropy_spectral_lower {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis (Fin n) ℂ E) (eig : Fin n → ℝ)
    (heig : ∀ j, 0 < eig j) (hanti : Antitone eig) (q : E → ℝ)
    (hq : ∀ x, q x = ∑ j, eig j*‖⟪b j,x⟫_ℂ‖^2)
    (f : ι → E) {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ E,
      ((Fintype.card ι : ℝ)*((n : ℝ)+1)/(2*(n : ℝ)^2)) *
        ((n-Module.finrank ℂ U : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun i => ∀ u : U, θ < ‖f i-(u : E)‖)).card : ℝ)) :
    (Fintype.card ι : ℝ)*(((n : ℝ)+1)/(n : ℝ)) *
      (∑ j, max 0 (Real.log (eig j)-Real.log ((2*(n : ℝ))/θ^2))) ≤
      ∑ i, cappedEntropy (2*(n : ℝ)) (q (f i)) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let C := Real.log ((2*(n : ℝ))/θ^2)
  let a : ℕ → ℝ := fun j => if hj : j < n then max 0 (Real.log (eig ⟨j,hj⟩)-C) else 0
  let p := (Fintype.card ι : ℝ)*((n : ℝ)+1)/(2*(n : ℝ)^2)
  have ha : ∀ k < n, a (k+1) ≤ a k := by
    intro k hk
    by_cases hk' : k+1 < n
    · simp only [a, dif_pos hk', dif_pos hk]
      apply max_le_max le_rfl
      apply sub_le_sub_right
      exact Real.log_le_log (heig ⟨k+1,hk'⟩) (hanti (by change k ≤ k+1; omega : (⟨k,hk⟩ : Fin n) ≤ ⟨k+1,hk'⟩))
    · simp only [a, dif_neg hk', dif_pos hk]
      exact le_max_left _ _
  have han : a n = 0 := by simp [a]
  have hcount : ∀ k < n, p*((k : ℝ)+1) ≤
      ((Finset.univ.filter (fun i => a k ≤ max 0 (Real.log (q (f i)/(2*(n : ℝ)))))).card : ℝ) := by
    intro k hk
    have hc := hthick (basisTailSpace b (k+1))
    rw [finrank_basisTailSpace b (by omega)] at hc
    have hnsub : n-(n-(k+1)) = k+1 := by omega
    rw [hnsub, Nat.cast_add, Nat.cast_one] at hc
    change p*((k : ℝ)+1) ≤ _ at hc
    apply hc.trans
    exact_mod_cast (show (Finset.univ.filter (fun i =>
      ∀ u : basisTailSpace b (k+1), θ < ‖f i-(u : E)‖)).card ≤
      (Finset.univ.filter (fun i => a k ≤ max 0 (Real.log (q (f i)/(2*(n : ℝ)))))).card from by
        apply Finset.card_le_card
        intro i hi
        have hf := (Finset.mem_filter.mp hi).2
        have hqf := spectral_prefix_lower_of_far b eig heig hanti q hq ⟨k,hk⟩ (f i) hθ hf
        have hkp := heig ⟨k,hk⟩
        have hlog := Real.log_lt_log (show 0 < θ^2*eig ⟨k,hk⟩/(2*(n : ℝ)) by positivity)
          (div_lt_div_of_pos_right hqf (by positivity : 0 < 2*(n : ℝ)))
        have he : Real.log (θ^2*eig ⟨k,hk⟩/(2*(n : ℝ))) = Real.log (eig ⟨k,hk⟩)-C := by
          dsimp [C]
          rw [Real.log_div (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity),
            Real.log_div (by positivity) (by positivity)]
          ring
        rw [he] at hlog
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [a, dif_pos hk]
        exact max_le_max le_rfl hlog.le)
  have hqpos (i : ι) : 0 ≤ q (f i) := by
    rw [hq]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (heig j).le (sq_nonneg _))
  have hh := cappedEntropy_sum_lower_of_threshold_counts
    (R := 2*(n : ℝ)) (by positivity) a (fun i => q (f i)) n p hqpos ha han hcount
  have hs : (∑ k ∈ Finset.range n, a k) = ∑ j, max 0 (Real.log (eig j)-C) := by
    rw [← Fin.sum_univ_eq_sum_range a n]
    apply Finset.sum_congr rfl
    intro j _
    simp only [a, dif_pos j.prop]
  rw [hs] at hh
  have he : (2*(n : ℝ))*p = (Fintype.card ι : ℝ)*(((n : ℝ)+1)/(n : ℝ)) := by
    dsimp [p]
    field_simp
  rw [he] at hh
  exact hh

theorem matrix_sum_cappedEntropy_spectral_lower {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι]
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (f : ι → EuclideanSpace ℂ (Fin n)) {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      ((Fintype.card ι : ℝ)*((n : ℝ)+1)/(2*(n : ℝ)^2)) *
        ((n-Module.finrank ℂ U : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun i => ∀ u : U, θ < ‖f i-(u : EuclideanSpace ℂ (Fin n))‖)).card : ℝ)) :
    (Fintype.card ι : ℝ)*(((n : ℝ)+1)/(n : ℝ)) *
      (∑ j, max 0 (Real.log (hH.isHermitian.eigenvalues j)-Real.log ((2*(n : ℝ))/θ^2))) ≤
      ∑ i, cappedEntropy (2*(n : ℝ)) (quadratic H (f i)) := by
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
      quadratic H x = ∑ j, eig j*‖⟪b j,x⟫_ℂ‖^2 := by
    rw [TraceExponential.quadratic_eq_sum hH.isHermitian]
    have hh := Equiv.sum_comp σ (fun j => hH.isHermitian.eigenvalues j *
      ‖⟪hH.isHermitian.eigenvectorBasis j,x⟫_ℂ‖^2)
    simpa only [eig, b, OrthonormalBasis.coe_reindex, Equiv.symm_symm, Function.comp_apply] using hh.symm
  have hh := sum_cappedEntropy_spectral_lower hn b eig hp ha (quadratic H) hq f hθ hthick
  have hs := Equiv.sum_comp σ (fun j => max 0 (Real.log (hH.isHermitian.eigenvalues j)-
    Real.log ((2*(n : ℝ))/θ^2)))
  simp only [eig] at hh
  rw [hs] at hh
  exact hh

theorem realDet_inverse {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    CappedWeightIteration.realDet G⁻¹ = (CappedWeightIteration.realDet G)⁻¹ := by
  have hd : G.det = (CappedWeightIteration.realDet G : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (RCLike.pos_iff.mp hG.det_pos).2
  unfold CappedWeightIteration.realDet
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, hd]
  simp

/-- Uniform subspace thickness bounds the determinant of every matrix whose
capped potential does not exceed the identity potential. -/
theorem framePotential_realDet_lower {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι)
    (f : ι → EuclideanSpace ℂ (Fin n)) (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef)
    {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      ((Fintype.card ι : ℝ)*((n : ℝ)+1)/(2*(n : ℝ)^2)) *
        ((n-Module.finrank ℂ U : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun i => ∀ u : U, θ < ‖f i-(u : EuclideanSpace ℂ (Fin n))‖)).card : ℝ))
    (hpotential : framePotential f (2*(n : ℝ)) G ≤ (n : ℝ)) :
    Real.exp (-((n : ℝ)^2 + (n : ℝ)*((n : ℝ)+1)*Real.log ((2*(n : ℝ))/θ^2))) ≤
      CappedWeightIteration.realDet G := by
  have hι' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
  let C := Real.log ((2*(n : ℝ))/θ^2)
  let t := fun j => Real.log (hG.inv.isHermitian.eigenvalues j)
  let hmean := (Fintype.card ι : ℝ)⁻¹ * ∑ i, cappedEntropy (2*(n : ℝ)) (quadratic G⁻¹ (f i))
  have he : Real.log (CappedWeightIteration.realDet G) = -(∑ j, t j) := by
    have hh := CappedWeightIteration.log_realDet_eq_sum hG.inv
    rw [realDet_inverse hG, Real.log_inv] at hh
    dsimp [t]
    linarith
  have hh := matrix_sum_cappedEntropy_spectral_lower hn G⁻¹ hG.inv f hθ hthick
  have hentropy : (((n : ℝ)+1)/(n : ℝ)) * (∑ j, max 0 (t j-C)) ≤ hmean := by
    dsimp [hmean, t, C]
    apply (le_inv_mul_iff₀ hι').mpr
    simpa only [mul_assoc] using hh
  have hupper : -(∑ j, t j)+hmean ≤ (n : ℝ) := by
    rw [← he]
    exact hpotential
  have hs := cappedEntropy_sum_coercivity hn C hmean t hentropy hupper
  have hl : -((n : ℝ)^2 + (n : ℝ)*((n : ℝ)+1)*C) ≤
      Real.log (CappedWeightIteration.realDet G) := by rw [he]; linarith
  have hexp := Real.exp_le_exp.mpr hl
  rw [Real.exp_log (CappedWeightIteration.realDet_pos hG)] at hexp
  exact hexp


theorem thickness_real_of_card {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : ι → E) (θ : ℝ)
    (hthick : ∀ U : Submodule ℂ E,
      (n+1)*(n-Module.finrank ℂ U)*Fintype.card ι ≤
      2*n^2*(Finset.univ.filter (fun i => ∀ u : U, θ < ‖f i-(u : E)‖)).card) :
    ∀ U : Submodule ℂ E,
      ((Fintype.card ι : ℝ)*((n : ℝ)+1)/(2*(n : ℝ)^2)) *
        ((n-Module.finrank ℂ U : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun i => ∀ u : U, θ < ‖f i-(u : E)‖)).card : ℝ) := by
  intro U
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : ((n : ℝ)+1)*((n-Module.finrank ℂ U : ℕ) : ℝ)*(Fintype.card ι : ℝ) ≤
      2*(n : ℝ)^2*((Finset.univ.filter (fun i => ∀ u : U, θ < ‖f i-(u : E)‖)).card : ℝ) := by
    exact_mod_cast hthick U
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 2*(n : ℝ)^2)).mpr
  nlinarith [hc]

/-- Cardinal subspace thickness gives the same determinant floor without a
real-valued counting hypothesis. -/
theorem framePotential_realDet_lower_of_card {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι)
    (f : ι → EuclideanSpace ℂ (Fin n)) (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef)
    {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (n+1)*(n-Module.finrank ℂ U)*Fintype.card ι ≤
      2*n^2*(Finset.univ.filter (fun i =>
        ∀ u : U, θ < ‖f i-(u : EuclideanSpace ℂ (Fin n))‖)).card)
    (hpotential : framePotential f (2*(n : ℝ)) G ≤ (n : ℝ)) :
    Real.exp (-((n : ℝ)^2 + (n : ℝ)*((n : ℝ)+1)*Real.log ((2*(n : ℝ))/θ^2))) ≤
      CappedWeightIteration.realDet G := by
  exact framePotential_realDet_lower hn hι f G hG hθ
    (thickness_real_of_card hn f θ hthick) hpotential


theorem sum_cappedEntropy_spectral_lower_radius {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis (Fin n) ℂ E) (eig : Fin n → ℝ)
    (heig : ∀ j, 0 < eig j) (hanti : Antitone eig) (q : E → ℝ)
    (hq : ∀ x, q x = ∑ j, eig j*‖⟪b j,x⟫_ℂ‖^2)
    (f : ι → E) {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ E,
      ((Fintype.card ι : ℝ)*((n : ℝ)+1)/(2*(n : ℝ)^2)) *
        ((n-Module.finrank ℂ U : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun i => ∀ u : U, θ < ‖f i-(u : E)‖)).card : ℝ)) :
    R*((Fintype.card ι : ℝ)*((n : ℝ)+1)/(2*(n : ℝ)^2)) *
      (∑ j, max 0 (Real.log (eig j)-Real.log (R/θ^2))) ≤
      ∑ i, cappedEntropy R (q (f i)) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let C := Real.log (R/θ^2)
  let a : ℕ → ℝ := fun j => if hj : j < n then max 0 (Real.log (eig ⟨j,hj⟩)-C) else 0
  let p := (Fintype.card ι : ℝ)*((n : ℝ)+1)/(2*(n : ℝ)^2)
  have ha : ∀ k < n, a (k+1) ≤ a k := by
    intro k hk
    by_cases hk' : k+1 < n
    · simp only [a, dif_pos hk', dif_pos hk]
      apply max_le_max le_rfl
      apply sub_le_sub_right
      exact Real.log_le_log (heig ⟨k+1,hk'⟩) (hanti (by change k ≤ k+1; omega : (⟨k,hk⟩ : Fin n) ≤ ⟨k+1,hk'⟩))
    · simp only [a, dif_neg hk', dif_pos hk]
      exact le_max_left _ _
  have han : a n = 0 := by simp [a]
  have hcount : ∀ k < n, p*((k : ℝ)+1) ≤
      ((Finset.univ.filter (fun i => a k ≤ max 0 (Real.log (q (f i)/R)))).card : ℝ) := by
    intro k hk
    have hc := hthick (basisTailSpace b (k+1))
    rw [finrank_basisTailSpace b (by omega)] at hc
    have hnsub : n-(n-(k+1)) = k+1 := by omega
    rw [hnsub, Nat.cast_add, Nat.cast_one] at hc
    change p*((k : ℝ)+1) ≤ _ at hc
    apply hc.trans
    exact_mod_cast (show (Finset.univ.filter (fun i =>
      ∀ u : basisTailSpace b (k+1), θ < ‖f i-(u : E)‖)).card ≤
      (Finset.univ.filter (fun i => a k ≤ max 0 (Real.log (q (f i)/R)))).card from by
        apply Finset.card_le_card
        intro i hi
        have hf := (Finset.mem_filter.mp hi).2
        have hqf := spectral_prefix_lower_of_far b eig heig hanti q hq ⟨k,hk⟩ (f i) hθ hf
        have hkp := heig ⟨k,hk⟩
        have hlog := Real.log_lt_log (show 0 < θ^2*eig ⟨k,hk⟩/R by positivity)
          (div_lt_div_of_pos_right hqf hR)
        have he : Real.log (θ^2*eig ⟨k,hk⟩/R) = Real.log (eig ⟨k,hk⟩)-C := by
          dsimp [C]
          rw [Real.log_div (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity),
            Real.log_div (by positivity) (by positivity)]
          ring
        rw [he] at hlog
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [a, dif_pos hk]
        exact max_le_max le_rfl hlog.le)
  have hqpos (i : ι) : 0 ≤ q (f i) := by
    rw [hq]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (heig j).le (sq_nonneg _))
  have hh := cappedEntropy_sum_lower_of_threshold_counts
    (R := R) hR a (fun i => q (f i)) n p hqpos ha han hcount
  have hs : (∑ k ∈ Finset.range n, a k) = ∑ j, max 0 (Real.log (eig j)-C) := by
    rw [← Fin.sum_univ_eq_sum_range a n]
    apply Finset.sum_congr rfl
    intro j _
    simp only [a, dif_pos j.prop]
  rw [hs] at hh
  exact hh

theorem matrix_sum_cappedEntropy_spectral_lower_radius {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    {ι : Type*} [Fintype ι]
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (f : ι → EuclideanSpace ℂ (Fin n)) {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      ((Fintype.card ι : ℝ)*((n : ℝ)+1)/(2*(n : ℝ)^2)) *
        ((n-Module.finrank ℂ U : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun i => ∀ u : U, θ < ‖f i-(u : EuclideanSpace ℂ (Fin n))‖)).card : ℝ)) :
    R*((Fintype.card ι : ℝ)*((n : ℝ)+1)/(2*(n : ℝ)^2)) *
      (∑ j, max 0 (Real.log (hH.isHermitian.eigenvalues j)-Real.log (R/θ^2))) ≤
      ∑ i, cappedEntropy R (quadratic H (f i)) := by
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
      quadratic H x = ∑ j, eig j*‖⟪b j,x⟫_ℂ‖^2 := by
    rw [TraceExponential.quadratic_eq_sum hH.isHermitian]
    have hh := Equiv.sum_comp σ (fun j => hH.isHermitian.eigenvalues j *
      ‖⟪hH.isHermitian.eigenvectorBasis j,x⟫_ℂ‖^2)
    simpa only [eig, b, OrthonormalBasis.coe_reindex, Equiv.symm_symm, Function.comp_apply] using hh.symm
  have hh := sum_cappedEntropy_spectral_lower_radius hn hR b eig hp ha (quadratic H) hq f hθ hthick
  have hs := Equiv.sum_comp σ (fun j => max 0 (Real.log (hH.isHermitian.eigenvalues j)-
    Real.log (R/θ^2)))
  simp only [eig] at hh
  rw [hs] at hh
  exact hh


theorem cappedEntropy_sum_coercivity_six_fifths {n : ℕ}
    (C hmean : ℝ) (t : Fin n → ℝ)
    (hentropy : (6/5 : ℝ)*(∑ j, max 0 (t j-C)) ≤ hmean)
    (hupper : -(∑ j, t j)+hmean ≤ (n : ℝ)) :
    (∑ j, t j) ≤ 5*(n : ℝ)+6*(n : ℝ)*C := by
  have hs : (∑ j, t j)-(n : ℝ)*C ≤ ∑ j, max 0 (t j-C) := by
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      le_max_right 0 (t j-C))
    simpa [Finset.sum_sub_distrib] using hh
  linarith

/-- The radius `12*n/5` gives an exponent linear in `n` while retaining the
same final leverage budget. -/
theorem framePotential_realDet_lower_slack {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι)
    (f : ι → EuclideanSpace ℂ (Fin n)) (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef)
    {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      ((Fintype.card ι : ℝ)*((n : ℝ)+1)/(2*(n : ℝ)^2)) *
        ((n-Module.finrank ℂ U : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun i => ∀ u : U, θ < ‖f i-(u : EuclideanSpace ℂ (Fin n))‖)).card : ℝ))
    (hpotential : framePotential f ((12/5 : ℝ)*n) G ≤ (n : ℝ)) :
    Real.exp (-(5*(n : ℝ)+6*(n : ℝ)*Real.log (((12/5 : ℝ)*n)/θ^2))) ≤
      CappedWeightIteration.realDet G := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hι' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
  let C := Real.log (((12/5 : ℝ)*n)/θ^2)
  let t := fun j => Real.log (hG.inv.isHermitian.eigenvalues j)
  let hmean := (Fintype.card ι : ℝ)⁻¹ *
    ∑ i, cappedEntropy ((12/5 : ℝ)*n) (quadratic G⁻¹ (f i))
  have he : Real.log (CappedWeightIteration.realDet G) = -(∑ j, t j) := by
    have hh := CappedWeightIteration.log_realDet_eq_sum hG.inv
    rw [realDet_inverse hG, Real.log_inv] at hh
    dsimp [t]
    linarith
  have hh := matrix_sum_cappedEntropy_spectral_lower_radius hn
    (R := (12/5 : ℝ)*n) (by positivity) G⁻¹ hG.inv f hθ hthick
  have hentropy' : ((12/5 : ℝ)*n)*(((n : ℝ)+1)/(2*(n : ℝ)^2)) *
      (∑ j, max 0 (t j-C)) ≤ hmean := by
    dsimp [hmean, t, C]
    apply (le_inv_mul_iff₀ hι').mpr
    convert hh using 1 <;> first | rfl | ring
  have hfactor : (6/5 : ℝ) ≤ ((12/5 : ℝ)*n)*(((n : ℝ)+1)/(2*(n : ℝ)^2)) := by
    rw [← mul_div_assoc, le_div_iff₀ (by positivity : 0 < 2*(n : ℝ)^2)]
    nlinarith
  have hentropy : (6/5 : ℝ)*(∑ j, max 0 (t j-C)) ≤ hmean :=
    (mul_le_mul_of_nonneg_right hfactor (Finset.sum_nonneg fun _ _ => le_max_left _ _)).trans hentropy'
  have hupper : -(∑ j, t j)+hmean ≤ (n : ℝ) := by
    rw [← he]
    exact hpotential
  have hs := cappedEntropy_sum_coercivity_six_fifths C hmean t hentropy hupper
  have hl : -(5*(n : ℝ)+6*(n : ℝ)*C) ≤
      Real.log (CappedWeightIteration.realDet G) := by rw [he]; linarith
  have hexp := Real.exp_le_exp.mpr hl
  rw [Real.exp_log (CappedWeightIteration.realDet_pos hG)] at hexp
  exact hexp

/-- Optimized determinant coercivity from the exact cardinality condition. -/
theorem framePotential_realDet_lower_slack_of_card {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι)
    (f : ι → EuclideanSpace ℂ (Fin n)) (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef)
    {θ : ℝ} (hθ : 0 < θ)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      (n+1)*(n-Module.finrank ℂ U)*Fintype.card ι ≤
      2*n^2*(Finset.univ.filter (fun i =>
        ∀ u : U, θ < ‖f i-(u : EuclideanSpace ℂ (Fin n))‖)).card)
    (hpotential : framePotential f ((12/5 : ℝ)*n) G ≤ (n : ℝ)) :
    Real.exp (-(5*(n : ℝ)+6*(n : ℝ)*Real.log (((12/5 : ℝ)*n)/θ^2))) ≤
      CappedWeightIteration.realDet G := by
  exact framePotential_realDet_lower_slack hn hι f G hG hθ
    (thickness_real_of_card hn f θ hthick) hpotential

end
end LeanNumDetect.FiniteMatrixSampling
