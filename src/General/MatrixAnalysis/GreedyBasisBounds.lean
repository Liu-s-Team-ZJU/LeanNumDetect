import General.Fourier.TranslatedBasisThickness
import General.MatrixAnalysis.FiniteFrameGram
import General.MatrixAnalysis.TraceExponentialBounds
import General.MatrixAnalysis.HermitianVariational
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! Quantitative Gram bounds for vectors accepted by a greedy basis rule. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Matrix WithLp InnerProductSpace
open scoped BigOperators InnerProductSpace ComplexOrder

namespace LeanNumDetect.GreedyBasisBounds

open TranslatedBasisThickness FiniteMatrixSampling FrameMatrixBounds TraceExponential

noncomputable section

/-- Every new vector lies farther than `τ` from the span of its predecessors. -/
def GreedySeparated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r : ℕ} (v : Fin r → E) (τ : ℝ) : Prop :=
  ∀ i, FarFromSubspace (v i) (Submodule.span ℂ (v '' Set.Iio i)) τ

/-- A common positive eigenvalue bound for all accepted prefixes of size at most `n`. -/
def greedyBasisEnergy (n : ℕ) (τ M : ℝ) : ℝ :=
  τ ^ (2 * n) / ((n : ℝ) * M ^ 2) ^ (n - 1)

/-- The unnormalized ambient Gram of a finite family. -/
def gramFamily {r n : ℕ} (v : Fin r → EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ := ∑ i, framePopulation v i

theorem gramFamily_posSemidef {r n : ℕ} (v : Fin r → EuclideanSpace ℂ (Fin n)) :
    (gramFamily v).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun i _ => framePopulation_posSemidef v i)

theorem quadratic_gramFamily {r n : ℕ} (v : Fin r → EuclideanSpace ℂ (Fin n))
    (x : EuclideanSpace ℂ (Fin n)) :
    quadratic (gramFamily v) x = ∑ i, ‖⟪v i, x⟫_ℂ‖ ^ 2 := by
  rw [gramFamily, quadratic_sum]
  simp only [quadratic_framePopulation]

theorem gramFamily_snoc {r n : ℕ} (v : Fin r → EuclideanSpace ℂ (Fin n))
    (w : EuclideanSpace ℂ (Fin n)) :
    gramFamily (Fin.snoc v w) = gramFamily v + framePopulation (fun _ : Fin 1 => w) 0 := by
  unfold gramFamily
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ext a b
    simp [framePopulation]
  · ext a b
    simp [framePopulation]

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {r : ℕ}

theorem snoc_prefix_image (v : Fin r → E) (w : E) (i : Fin r) :
    Fin.snoc v w '' Set.Iio i.castSucc = v '' Set.Iio i := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hjr : j.val < r := by have := i.isLt; change j < i.castSucc at hj; omega
    let j' : Fin r := ⟨j.val, hjr⟩
    have he : j = j'.castSucc := Fin.ext rfl
    refine ⟨j', ?_, ?_⟩
    · change j.val < i.val
      exact hj
    · rw [he, Fin.snoc_castSucc]
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.castSucc, by simpa using hj, by simp⟩

theorem snoc_last_image (v : Fin r → E) (w : E) :
    Fin.snoc v w '' Set.Iio (Fin.last r) = Set.range v := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hjr : j.val < r := by change j < Fin.last r at hj; omega
    let j' : Fin r := ⟨j.val, hjr⟩
    have he : j = j'.castSucc := Fin.ext rfl
    exact ⟨j', by rw [he, Fin.snoc_castSucc]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, by simp, by simp⟩

theorem GreedySeparated.snoc {v : Fin r → E} {τ : ℝ}
    (hv : GreedySeparated v τ) {w : E}
    (hw : FarFromSubspace w (Submodule.span ℂ (Set.range v)) τ) :
    GreedySeparated (Fin.snoc v w) τ := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last, snoc_last_image] using hw
  · simpa only [Fin.snoc_castSucc, snoc_prefix_image] using hv j

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {r : ℕ}

/-- The Gram--Schmidt residual has the accepted distance lower bound. -/
theorem gramSchmidt_norm_lower {v : Fin r → E} {τ : ℝ}
    (hv : GreedySeparated v τ) (i : Fin r) :
    τ < ‖gramSchmidt ℂ v i‖ := by
  classical
  let U := Submodule.span ℂ (v '' Set.Iio i)
  let u := ∑ j ∈ Finset.Iio i, (ℂ ∙ gramSchmidt ℂ v j).starProjection (v i)
  have hu : u ∈ U := by
    apply U.sum_mem
    intro j hj
    have hji : j < i := Finset.mem_Iio.mp hj
    have hgs : gramSchmidt ℂ v j ∈ U := by
      change gramSchmidt ℂ v j ∈ Submodule.span ℂ (v '' Set.Iio i)
      rw [← span_gramSchmidt_Iio ℂ v i]
      exact Submodule.subset_span ⟨j, hji, rfl⟩
    exact ((Submodule.span_singleton_le_iff_mem _ _).mpr hgs)
      ((ℂ ∙ gramSchmidt ℂ v j).starProjection_apply_mem (v i))
  have h := hv i ⟨u, hu⟩
  change τ < ‖v i - u‖ at h
  rw [gramSchmidt_def]
  exact h

theorem linearIndependent_of_greedySeparated {v : Fin r → E} {τ : ℝ}
    (hτ : 0 < τ) (hv : GreedySeparated v τ) : LinearIndependent ℂ v := by
  have hgs : LinearIndependent ℂ (gramSchmidt ℂ v) :=
    linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => by
      have hi := (gramSchmidt_norm_lower hv i).trans' hτ
      exact norm_pos_iff.mp hi)
      (fun i j hij => gramSchmidt_orthogonal ℂ v hij)
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card (Fin r) = Module.finrank ℂ (Submodule.span ℂ (Set.range v))
  rw [← span_gramSchmidt ℂ v]
  exact linearIndependent_iff_card_eq_finrank_span.mp hgs

theorem finrank_span_of_greedySeparated {v : Fin r → E} {τ : ℝ}
    (hτ : 0 < τ) (hv : GreedySeparated v τ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = r := by
  simpa only [Fintype.card_fin] using finrank_span_eq_card
    (linearIndependent_of_greedySeparated hτ hv)

/-- The diagonal entry in the Gram--Schmidt triangular factor is a residual norm. -/
theorem inner_gramSchmidtNormed_self {v : Fin r → E} (hv : LinearIndependent ℂ v)
    (i : Fin r) :
    ⟪gramSchmidtNormed ℂ v i, v i⟫_ℂ = (‖gramSchmidt ℂ v i‖ : ℂ) := by
  classical
  have hi : ‖gramSchmidt ℂ v i‖ ≠ 0 := norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv)
  have hs : ⟪gramSchmidt ℂ v i, v i⟫_ℂ = (‖gramSchmidt ℂ v i‖ : ℂ) ^ 2 := by
    rw [gramSchmidt_def' ℂ v i, inner_add_right, inner_sum]
    have hz : (∑ j ∈ Finset.Iio i,
        ⟪gramSchmidt ℂ v i, (ℂ ∙ gramSchmidt ℂ v j).starProjection (v i)⟫_ℂ) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Submodule.starProjection_singleton, inner_smul_right,
        gramSchmidt_orthogonal ℂ v (Finset.mem_Iio.mp hj).ne', mul_zero]
    rw [hz, add_zero, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [gramSchmidtNormed, inner_smul_left, hs]
  simp [RCLike.conj_ofReal, hi, pow_two]

/-- In an `r`-dimensional space, the Gram determinant is the product of squared
Gram--Schmidt residual norms. -/
theorem det_gram_eq_prod_residual_sq (v : Fin r → E) (hv : LinearIndependent ℂ v)
    (hdim : Module.finrank ℂ E = r) :
    (Matrix.gram ℂ v).det = ((∏ i, ‖gramSchmidt ℂ v i‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have hd : Module.finrank ℂ E = Fintype.card (Fin r) := by simpa only [Fintype.card_fin]
    using hdim
  let b := gramSchmidtOrthonormalBasis hd v
  let C : Matrix (Fin r) (Fin r) ℂ := fun i j => b.repr (v j) i
  have hdiag (i : Fin r) : ⟪b i, v i⟫_ℂ = (‖gramSchmidt ℂ v i‖ : ℂ) := by
    rw [show b i = gramSchmidtNormed ℂ v i from
      gramSchmidtOrthonormalBasis_apply hd (by
        have hi := (gramSchmidtNormed_unit_length i hv)
        intro h
        rw [h, norm_zero] at hi
        norm_num at hi)]
    exact inner_gramSchmidtNormed_self hv i
  have hC : C.det = ∏ i, (‖gramSchmidt ℂ v i‖ : ℂ) := by
    have h := gramSchmidtOrthonormalBasis_det hd v
    rw [Module.Basis.det_apply] at h
    change C.det = ∏ i, ⟪b i, v i⟫_ℂ at h
    simpa only [hdiag] using h
  rw [Matrix.gram_eq_conjTranspose_mul b v, Matrix.det_mul, Matrix.det_conjTranspose]
  change star C.det * C.det = _
  rw [hC]
  simp [← Complex.ofReal_prod, RCLike.star_def, ← Complex.ofReal_mul,
    ← pow_two, Finset.prod_pow]

/-- Greedy acceptance bounds the Gram determinant below by `τ^(2r)`. -/
theorem det_gram_lower_of_greedySeparated {v : Fin r → E} {τ : ℝ}
    (hτ : 0 < τ) (hv : GreedySeparated v τ) (hdim : Module.finrank ℂ E = r) :
    τ ^ (2 * r) ≤ (Matrix.gram ℂ v).det.re := by
  rw [det_gram_eq_prod_residual_sq v (linearIndependent_of_greedySeparated hτ hv) hdim,
    Complex.ofReal_re]
  calc
    τ ^ (2 * r) = ∏ _i : Fin r, τ ^ 2 := by simp [pow_mul]
    _ ≤ ∏ i, ‖gramSchmidt ℂ v i‖ ^ 2 := by
      apply Finset.prod_le_prod (fun _ _ => sq_nonneg _)
      intro i _
      exact (sq_le_sq₀ hτ.le (norm_nonneg _)).mpr (gramSchmidt_norm_lower hv i).le

/-- Passing to the span removes the ambient dimension from the Gram determinant. -/
theorem det_gram_lower {v : Fin r → E} {τ : ℝ}
    (hτ : 0 < τ) (hv : GreedySeparated v τ) :
    τ ^ (2 * r) ≤ (Matrix.gram ℂ v).det.re := by
  classical
  let U := Submodule.span ℂ (Set.range v)
  let w : Fin r → U := fun i => ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hw : GreedySeparated w τ := by
    intro i u
    have he : (Submodule.span ℂ (w '' Set.Iio i)).map U.subtype =
        Submodule.span ℂ (v '' Set.Iio i) := by
      rw [Submodule.map_span, Set.image_image]
      rfl
    have hu : (u.val : E) ∈ Submodule.span ℂ (v '' Set.Iio i) := by
      rw [← he]
      exact ⟨u.val, u.property, rfl⟩
    exact hv i ⟨u.val, hu⟩
  have hd : Module.finrank ℂ U = r := finrank_span_of_greedySeparated hτ hv
  have hgram : Matrix.gram ℂ w = Matrix.gram ℂ v := rfl
  rw [← hgram]
  exact det_gram_lower_of_greedySeparated hτ hw hd

/-- The trace of a Gram is the sum of the squared vector norms. -/
theorem trace_gram_re (v : Fin r → E) :
    (Matrix.gram ℂ v).trace.re = ∑ i, ‖v i‖ ^ 2 := by
  simp [Matrix.trace, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- Every Gram eigenvalue is at most `r M²`. -/
theorem gram_eigenvalue_upper {v : Fin r → E} {M : ℝ}
    (hM : 0 ≤ M) (hv : ∀ i, ‖v i‖ ≤ M) (i : Fin r) :
    (Matrix.isHermitian_gram ℂ v).eigenvalues i ≤ (r : ℝ) * M ^ 2 := by
  have hG := Matrix.posSemidef_gram ℂ v
  have ht : (Matrix.gram ℂ v).trace.re =
      ∑ j, (Matrix.isHermitian_gram ℂ v).eigenvalues j := by
    rw [(Matrix.isHermitian_gram ℂ v).trace_eq_sum_eigenvalues, Complex.re_sum]
    rfl
  calc
    _ ≤ ∑ j, (Matrix.isHermitian_gram ℂ v).eigenvalues j :=
      Finset.single_le_sum (fun j _ => hG.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = ∑ j, ‖v j‖ ^ 2 := by rw [← ht, trace_gram_re]
    _ ≤ ∑ _j : Fin r, M ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact (sq_le_sq₀ (norm_nonneg _) hM).mpr (hv j)
    _ = _ := by simp

end InnerProduct

/-- The `n`-vector lower bound is also valid for every nonempty accepted prefix. -/
theorem greedyBasisEnergy_le_prefix {r n : ℕ} {τ M : ℝ}
    (hr : 0 < r) (hrn : r ≤ n) (hτ : 0 < τ) (hM : 0 < M) (hτM : τ ≤ M) :
    greedyBasisEnergy n τ M ≤ τ ^ (2 * r) / ((n : ℝ) * M ^ 2) ^ (r - 1) := by
  let R := (n : ℝ) * M ^ 2
  have hn : 0 < n := lt_of_lt_of_le hr hrn
  have hR : 0 < R := mul_pos (by exact_mod_cast hn) (sq_pos_of_pos hM)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hτR : τ ^ 2 ≤ R := by
    have hsq := (sq_le_sq₀ hτ.le hM.le).mpr hτM
    dsimp [R]
    nlinarith [sq_nonneg M]
  have hpow : τ ^ (2 * n) ≤ τ ^ (2 * r) * R ^ (n - r) := by
    calc
      _ = τ ^ (2 * r) * (τ ^ 2) ^ (n - r) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (sq_nonneg τ) hτR _) (by positivity)
  unfold greedyBasisEnergy
  change τ ^ (2 * n) / R ^ (n - 1) ≤ τ ^ (2 * r) / R ^ (r - 1)
  apply (div_le_div_iff₀ (pow_pos hR _) (pow_pos hR _)).mpr
  calc
    _ ≤ (τ ^ (2 * r) * R ^ (n - r)) * R ^ (r - 1) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {r : ℕ}

/-- The determinant lower bound and the trace upper bound control each positive
Gram eigenvalue, uniformly over prefix lengths. -/
theorem gram_eigenvalue_lower {n : ℕ} {v : Fin r → E} {τ M : ℝ}
    (hrn : r ≤ n) (hτ : 0 < τ) (hM : 0 < M) (hτM : τ ≤ M)
    (hv : GreedySeparated v τ) (hnorm : ∀ i, ‖v i‖ ≤ M) (i : Fin r) :
    greedyBasisEnergy n τ M ≤ (Matrix.isHermitian_gram ℂ v).eigenvalues i := by
  classical
  let R := (n : ℝ) * M ^ 2
  let ev := (Matrix.isHermitian_gram ℂ v).eigenvalues
  have hr : 0 < r := Nat.pos_of_ne_zero (fun hr => by simpa [hr] using i.isLt)
  have hn : 0 < n := lt_of_lt_of_le hr hrn
  have hR : 0 < R := mul_pos (by exact_mod_cast hn) (sq_pos_of_pos hM)
  have hev : ∀ j, 0 ≤ ev j := fun j => (Matrix.posSemidef_gram ℂ v).eigenvalues_nonneg j
  have hu : ∀ j, ev j ≤ R := by
    intro j
    exact (gram_eigenvalue_upper hM.le hnorm j).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hrn) (sq_nonneg M))
  have hp : τ ^ (2 * r) ≤ ∏ j, ev j := by
    have h := det_gram_lower hτ hv
    rw [(Matrix.isHermitian_gram ℂ v).det_eq_prod_eigenvalues] at h
    have he : (∏ j, (ev j : ℂ)) = ((∏ j, ev j : ℝ) : ℂ) := by norm_cast
    change τ ^ (2 * r) ≤ (∏ j, (ev j : ℂ)).re at h
    rw [he, Complex.ofReal_re] at h
    exact h
  have herase : (∏ j ∈ Finset.univ.erase i, ev j) ≤ R ^ (r - 1) := by
    calc
      _ ≤ ∏ _j ∈ Finset.univ.erase i, R :=
        Finset.prod_le_prod (fun j _ => hev j) (fun j _ => hu j)
      _ = _ := by simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  have hlower : τ ^ (2 * r) / R ^ (r - 1) ≤ ev i := by
    apply (div_le_iff₀ (pow_pos hR _)).mpr
    calc
      _ ≤ ∏ j, ev j := hp
      _ = ev i * ∏ j ∈ Finset.univ.erase i, ev j :=
        (Finset.mul_prod_erase Finset.univ ev (Finset.mem_univ i)).symm
      _ ≤ ev i * R ^ (r - 1) := mul_le_mul_of_nonneg_left herase (hev i)
  exact (greedyBasisEnergy_le_prefix hr hrn hτ hM hτM).trans hlower

/-- The coefficient Gram quadratic form equals the squared synthesis norm. -/
theorem quadratic_gram_eq_synthesis_norm_sq (v : Fin r → E)
    (c : EuclideanSpace ℂ (Fin r)) :
    quadratic (Matrix.gram ℂ v) c = ‖∑ i, (c i) • v i‖ ^ 2 := by
  unfold quadratic
  rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm,
    Matrix.star_dotProduct_gram_mulVec, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- Every accepted prefix has a uniform synthesis energy lower bound. -/
theorem synthesis_energy_lower {n : ℕ} {v : Fin r → E} {τ M : ℝ}
    (hrn : r ≤ n) (hτ : 0 < τ) (hM : 0 < M) (hτM : τ ≤ M)
    (hv : GreedySeparated v τ) (hnorm : ∀ i, ‖v i‖ ≤ M)
    (c : EuclideanSpace ℂ (Fin r)) :
    greedyBasisEnergy n τ M * ‖c‖ ^ 2 ≤ ‖∑ i, (c i) • v i‖ ^ 2 := by
  let hG := Matrix.isHermitian_gram ℂ v
  rw [← quadratic_gram_eq_synthesis_norm_sq, quadratic_eq_sum hG,
    ← hG.eigenvectorBasis.sum_sq_norm_inner_right c, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right
    (gram_eigenvalue_lower hrn hτ hM hτM hv hnorm i) (sq_nonneg _)

/-- On the span of an accepted family, its ambient Gram has the same lower
energy bound as its coefficient Gram. -/
theorem span_energy_lower {n : ℕ} {v : Fin r → E} {τ M : ℝ}
    (hrn : r ≤ n) (hτ : 0 < τ) (hM : 0 < M) (hτM : τ ≤ M)
    (hv : GreedySeparated v τ) (hnorm : ∀ i, ‖v i‖ ≤ M)
    (x : E) (hx : x ∈ Submodule.span ℂ (Set.range v)) :
    greedyBasisEnergy n τ M * ‖x‖ ^ 2 ≤ ∑ i, ‖⟪v i, x⟫_ℂ‖ ^ 2 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  let y : EuclideanSpace ℂ (Fin r) := toLp 2 c
  let a : EuclideanSpace ℂ (Fin r) := toLp 2 (fun i => ⟪v i, x⟫_ℂ)
  have hinner : ⟪x, x⟫_ℂ = ⟪y, a⟫_ℂ := by
    calc
      _ = ⟪∑ i, c i • v i, x⟫_ℂ := congrArg (fun z => ⟪z, x⟫_ℂ) hc.symm
      _ = _ := by
        rw [sum_inner]
        simp only [inner_smul_left]
        simp only [y, a, EuclideanSpace.inner_eq_star_dotProduct, ofLp_toLp, dotProduct,
          Pi.star_apply, starRingEnd_apply]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hlower : greedyBasisEnergy n τ M * ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [y, hc, PiLp.toLp_apply] using
      synthesis_energy_lower hrn hτ hM hτM hv hnorm y
  have hCS : ‖x‖ ^ 2 ≤ ‖y‖ * ‖a‖ := by
    calc
      _ = ‖⟪x, x⟫_ℂ‖ := by simp [inner_self_eq_norm_sq_to_K]
      _ = ‖⟪y, a⟫_ℂ‖ := congrArg norm hinner
      _ ≤ _ := norm_inner_le_norm y a
  have hCSsq : ‖x‖ ^ 2 * ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 * ‖a‖ ^ 2 := by
    have h := (sq_le_sq₀ (sq_nonneg ‖x‖)
      (mul_nonneg (norm_nonneg y) (norm_nonneg a))).mpr hCS
    rw [mul_pow] at h
    simpa only [pow_two] using h
  have hη : 0 ≤ greedyBasisEnergy n τ M := by unfold greedyBasisEnergy; positivity
  have h1 := mul_le_mul_of_nonneg_left hCSsq hη
  have h2 := mul_le_mul_of_nonneg_right hlower (sq_nonneg ‖a‖)
  have hfinal : greedyBasisEnergy n τ M * ‖x‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
      nlinarith
  simpa only [a, EuclideanSpace.norm_sq_eq, PiLp.toLp_apply] using hfinal


end InnerProduct

/-- Positive threshold and positive dimension give a positive Gram energy. -/
theorem greedyBasisEnergy_pos {n : ℕ} {τ M : ℝ}
    (hn : 0 < n) (hτ : 0 < τ) (hM : 0 < M) : 0 < greedyBasisEnergy n τ M := by
  unfold greedyBasisEnergy
  exact div_pos (pow_pos hτ _) (pow_pos
    (mul_pos (by exact_mod_cast hn) (sq_pos_of_pos hM)) _)

theorem greedy_on_span_energy_lower {r n : ℕ} {τ M : ℝ}
    (hn : 0 < n) (hτ : 0 < τ) (hτM : τ ≤ M) (hr : r ≤ n)
    (v : Fin r → EuclideanSpace ℂ (Fin n)) (hv : GreedySeparated v τ)
    (hNorm : ∀ i, ‖v i‖ ≤ M) (x : EuclideanSpace ℂ (Fin n))
    (hx : x ∈ Submodule.span ℂ (Set.range v)) :
    greedyBasisEnergy n τ M * ‖x‖ ^ 2 ≤ quadratic (gramFamily v) x := by
  rw [quadratic_gramFamily]
  exact span_energy_lower hr hτ (hτ.trans_le hτM) hτM hv hNorm x hx

theorem greedy_full_energy_lower {n : ℕ} {τ M : ℝ}
    (hn : 0 < n) (hτ : 0 < τ) (hτM : τ ≤ M)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) (hv : GreedySeparated v τ)
    (hNorm : ∀ i, ‖v i‖ ≤ M) (x : EuclideanSpace ℂ (Fin n)) :
    greedyBasisEnergy n τ M * ‖x‖ ^ 2 ≤ quadratic (gramFamily v) x := by
  have htop : Submodule.span ℂ (Set.range v) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by
      simpa only [finrank_euclideanSpace_fin] using finrank_span_of_greedySeparated hτ hv)
  apply greedy_on_span_energy_lower hn hτ hτM le_rfl v hv hNorm x
  rw [htop]
  trivial

end
end LeanNumDetect.GreedyBasisBounds
