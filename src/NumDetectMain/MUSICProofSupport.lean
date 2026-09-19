import General.MatrixAnalysis.MUSICSubspacePerturbation
import NumDetectMain.ProofSupport
import NumDetectMain.Segmented

/-! Proved adapters for the fixed-rank MUSIC perturbation argument. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- The squared image norm expanded in the orthonormal Gram eigenbasis. -/
theorem music_norm_sq_eq_sum_gram_eigenvalues
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) (v : E) :
    ‖T v‖ ^ 2 = ∑ i : Fin (Module.finrank ℂ E),
      T.isSymmetric_adjoint_comp_self.eigenvalues rfl i *
        ‖⟪T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i, v⟫_ℂ‖ ^ 2 := by
  let G := T.adjoint ∘ₗ T
  let hG := T.isSymmetric_adjoint_comp_self
  let b := hG.eigenvectorBasis rfl
  have he (i : Fin (Module.finrank ℂ E)) :
      ⟪b i, G v⟫_ℂ = (hG.eigenvalues rfl i : ℂ) * ⟪b i, v⟫_ℂ := by
    rw [← hG, hG.apply_eigenvectorBasis]
    simp only [inner_smul_real_left, Complex.real_smul, b]
  calc
    ‖T v‖ ^ 2 = RCLike.re (⟪v, G v⟫_ℂ) := by
      change ‖T v‖ ^ 2 = RCLike.re ⟪v, T.adjoint (T v)⟫_ℂ
      rw [T.adjoint_inner_right, inner_self_eq_norm_sq]
    _ = ∑ i, RCLike.re (⟪v, b i⟫_ℂ * ⟪b i, G v⟫_ℂ) := by
      rw [← b.sum_inner_mul_inner v (G v), map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [he, mul_left_comm]
      change RCLike.re ((hG.eigenvalues rfl i) •
        (⟪v, b i⟫_ℂ * ⟪b i, v⟫_ℂ)) = _
      rw [RCLike.smul_re, inner_mul_symm_re_eq_norm, norm_mul,
        ← inner_conj_symm v (b i), RCLike.norm_conj, ← pow_two]

/-- The last column singular value is a lower Euclidean expansion factor. -/
theorem lastSingularValue_mul_norm_le
    {m : Type*} [Fintype m] {n : ℕ}
    (A : Matrix m (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    matrixSingularValue A (n - 1) * ‖v‖ ≤ ‖A.toEuclideanLin v‖ := by
  let T := A.toEuclideanLin
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  have hl (i : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin n)))) :
      matrixSingularValue A (n - 1) ^ 2 ≤
        T.isSymmetric_adjoint_comp_self.eigenvalues rfl i := by
    have hi : i.val < n := by simpa using i.isLt
    have hs : matrixSingularValue A (n - 1) ≤ T.singularValues i :=
      T.singularValues_antitone (by omega)
    have hsq := pow_le_pow_left₀ (matrixSingularValue_nonneg A (n - 1)) hs 2
    rwa [T.sq_singularValues_fin rfl i] at hsq
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [mul_pow]
  calc
    matrixSingularValue A (n - 1) ^ 2 * ‖v‖ ^ 2 =
        ∑ i, matrixSingularValue A (n - 1) ^ 2 * ‖⟪b i, v⟫_ℂ‖ ^ 2 := by
      rw [← b.sum_sq_norm_inner_right v, Finset.mul_sum]
    _ ≤ ∑ i, T.isSymmetric_adjoint_comp_self.eigenvalues rfl i *
        ‖⟪b i, v⟫_ℂ‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hl i) (sq_nonneg _)
    _ = ‖A.toEuclideanLin v‖ ^ 2 :=
      (music_norm_sq_eq_sum_gram_eigenvalues T v).symm

/-- Coercivity on an `(i+1)`-dimensional subspace bounds the `i`th singular value. -/
theorem music_le_matrixSingularValue_of_subspace
    {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]
    (A : Matrix m p ℂ) {i : ℕ}
    (S : Submodule ℂ (EuclideanSpace ℂ p))
    (hdim : Module.finrank ℂ S = i + 1) {c : ℝ} (hc : 0 ≤ c)
    (hcoer : ∀ x ∈ S, c * ‖x‖ ≤ ‖A.toEuclideanLin x‖) :
    c ≤ matrixSingularValue A i := by
  have hi : i < Module.finrank ℂ (EuclideanSpace ℂ p) := by
    have := S.finrank_le
    omega
  have heq : (Aᴴ * A).toEuclideanLin =
      A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    ext x
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have hG : (Aᴴ * A).toEuclideanLin.IsSymmetric :=
    heq.symm ▸ A.toEuclideanLin.isSymmetric_adjoint_comp_self
  have hcf := (hermitian_courant_fischer (Aᴴ * A) hG ⟨i, hi⟩).1.2
  have hbound : c ^ 2 ≤ hG.eigenvalues rfl ⟨i, hi⟩ := by
    apply hcf
    refine ⟨S, hdim, ?_⟩
    intro x hx hnorm
    have h := hcoer x hx
    have h' : c ≤ ‖A.toEuclideanLin x‖ := by
      simpa only [hnorm, mul_one] using h
    calc
      c ^ 2 ≤ ‖A.toEuclideanLin x‖ ^ 2 := pow_le_pow_left₀ hc h' 2
      _ = RCLike.re ⟪x, (Aᴴ * A).toEuclideanLin x⟫_ℂ := by
        rw [heq]
        simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
          inner_self_eq_norm_sq]
  have hev : hG.eigenvalues rfl ⟨i, hi⟩ =
      matrixSingularValue A i ^ 2 := by
    simp only [heq]
    exact (A.toEuclideanLin.sq_singularValues_fin rfl ⟨i, hi⟩).symm
  rw [hev] at hbound
  exact le_of_sq_le_sq hbound (matrixSingularValue_nonneg A i)

/-- A coercive map's adjoint has the same lower bound on its range. -/
theorem music_adjoint_mul_norm_le_on_range
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F]
    (B : E →ₗ[ℂ] F) {c : ℝ} (hc : 0 ≤ c)
    (hB : ∀ x, c * ‖x‖ ≤ ‖B x‖) {w : F} (hw : w ∈ B.range) :
    c * ‖w‖ ≤ ‖B.adjoint w‖ := by
  obtain ⟨x, rfl⟩ := hw
  by_cases hx : B x = 0
  · simp [hx]
  have hp : 0 < ‖B x‖ := norm_pos_iff.mpr hx
  have hcs : ‖B x‖ ^ 2 ≤ ‖x‖ * ‖B.adjoint (B x)‖ := by
    have := re_inner_le_norm (𝕜 := ℂ) x (B.adjoint (B x))
    simpa only [LinearMap.adjoint_inner_right, inner_self_eq_norm_sq,
      RCLike.ofReal_re] using this
  have h₁ := mul_le_mul_of_nonneg_left hcs hc
  have h₂ := mul_le_mul_of_nonneg_right (hB x) (norm_nonneg (B.adjoint (B x)))
  apply (mul_le_mul_iff_left₀ hp).mp
  nlinarith

/-- Entrywise conjugation preserves the least-column coercivity bound. -/
theorem lastSingularValue_conjugate_mul_norm_le
    {m : Type*} [Fintype m] {n : ℕ}
    (B : Matrix m (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    matrixSingularValue B (n - 1) * ‖x‖ ≤
      ‖(B.map star).toEuclideanLin x‖ := by
  have h := lastSingularValue_mul_norm_le B
    (toLp 2 (star (ofLp x)))
  have hnorm : ‖toLp 2 (star (ofLp x))‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq]
  rw [hnorm] at h
  have he : (B.map star).toEuclideanLin x =
      toLp 2 (star (ofLp (B.toEuclideanLin
        (toLp 2 (star (ofLp x)))))) := by
    ext i
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, star_sum,
      star_mul, mul_comm]
  rw [he]
  have hout :
      ‖toLp 2 (star (ofLp (B.toEuclideanLin
        (toLp 2 (star (ofLp x))))))‖ =
        ‖B.toEuclideanLin (toLp 2 (star (ofLp x)))‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq]
  rw [hout]
  exact h

/-- The transpose has the same least-column lower bound on the conjugate range. -/
theorem transpose_mul_norm_le_on_conjugate_range
    {m : Type*} [Fintype m] [DecidableEq m] {n : ℕ}
    (B : Matrix m (Fin n) ℂ)
    {w : EuclideanSpace ℂ m}
    (hw : w ∈ (B.map star).toEuclideanLin.range) :
    matrixSingularValue B (n - 1) * ‖w‖ ≤ ‖Bᵀ.toEuclideanLin w‖ := by
  have h := music_adjoint_mul_norm_le_on_range
    (B.map star).toEuclideanLin
    (matrixSingularValue_nonneg B (n - 1))
    (lastSingularValue_conjugate_mul_norm_le B) hw
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h
  have he : (B.map star)ᴴ = Bᵀ := by ext i j; simp
  rwa [he] at h

/-- A full-column-rank matrix has a positive last column singular value. -/
theorem lastSingularValue_pos_of_fullColumnRank
    {m : Type*} [Fintype m] {n : ℕ}
    (A : Matrix m (Fin n) ℂ) (hn : 0 < n)
    (hA : HasFullColumnRank A) :
    0 < matrixSingularValue A (n - 1) := by
  have hi : Function.Injective A.toEuclideanLin := by
    intro x y hxy
    apply WithLp.ofLp_injective
    apply hA
    exact congrArg ofLp hxy
  exact (A.toEuclideanLin.injective_iff_forall_lt_finrank_singularValues_pos.mp hi)
    (n - 1) (by simpa using (show n - 1 < n by omega))

/-- A positive last column singular value implies full column rank. -/
theorem fullColumnRank_of_lastSingularValue_pos
    {m : Type*} [Fintype m] {n : ℕ}
    (A : Matrix m (Fin n) ℂ) (hn : 0 < n)
    (hA : 0 < matrixSingularValue A (n - 1)) :
    HasFullColumnRank A := by
  have hi : Function.Injective A.toEuclideanLin := by
    rw [A.toEuclideanLin.injective_iff_forall_lt_finrank_singularValues_pos]
    intro i hi
    have hi' : i < n := by
      simpa only [finrank_euclideanSpace, Fintype.card_fin] using hi
    exact hA.trans_le
      (A.toEuclideanLin.singularValues_antitone (by omega))
  intro x y hxy
  apply WithLp.toLp_injective
  apply hi
  change toLp 2 (A *ᵥ x) = toLp 2 (A *ᵥ y)
  exact congrArg (toLp 2) hxy

/-- A Vandermonde-diagonal-transpose factor has the manuscript's product lower bound. -/
theorem vandermondeFactor_signalSingularValue_lower
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rowFrequency : ι → Point d) (columnFrequency : κ → Point d)
    (node : Fin n → Point d) (a : Fin n → ℂ) (aMin : ℝ)
    (hn : 0 < n) (haMinPos : 0 < aMin)
    (haMin : ∀ j, aMin ≤ ‖a j‖)
    (hfull₂ : HasFullColumnRank
      (generalizedVandermonde columnFrequency node)) :
    aMin *
        matrixSingularValue
          (generalizedVandermonde rowFrequency node) (n - 1) *
        matrixSingularValue
          (generalizedVandermonde columnFrequency node) (n - 1) ≤
      matrixSingularValue
        (generalizedVandermonde rowFrequency node *
          Matrix.diagonal a *
          (generalizedVandermonde columnFrequency node)ᵀ) (n - 1) := by
  let V₁ := generalizedVandermonde rowFrequency node
  let V₂ := generalizedVandermonde columnFrequency node
  let S := (V₂.map star).toEuclideanLin.range
  have hV₂pos : 0 < matrixSingularValue V₂ (n - 1) :=
    lastSingularValue_pos_of_fullColumnRank V₂ hn hfull₂
  have hconjInj : Function.Injective (V₂.map star).toEuclideanLin := by
    intro x y hxy
    have hcoer := lastSingularValue_conjugate_mul_norm_le V₂ (x - y)
    have hz : (V₂.map star).toEuclideanLin (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    rw [hz, norm_zero] at hcoer
    have hnorm : ‖x - y‖ = 0 := by
      nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hdim : Module.finrank ℂ S = n - 1 + 1 := by
    rw [LinearMap.finrank_range_of_inj hconjInj]
    simp
    omega
  apply music_le_matrixSingularValue_of_subspace
    (generalizedVandermonde rowFrequency node *
      Matrix.diagonal a *
      (generalizedVandermonde columnFrequency node)ᵀ) S hdim
  · exact mul_nonneg
      (mul_nonneg haMinPos.le
        (matrixSingularValue_nonneg V₁ (n - 1)))
      (matrixSingularValue_nonneg V₂ (n - 1))
  · intro x hx
    have hrow := transpose_mul_norm_le_on_conjugate_range V₂ hx
    have hleft := mul_lower_bound V₁ (Matrix.diagonal a)
      (matrixSingularValue_nonneg V₁ (n - 1))
      (lastSingularValue_mul_norm_le V₁)
      (norm_diagonal_mulVec_lower a haMinPos.le haMin)
      (V₂ᵀ.toEuclideanLin x)
    change
      aMin * matrixSingularValue V₁ (n - 1) *
          matrixSingularValue V₂ (n - 1) * ‖x‖ ≤ _
    calc
      _ = (matrixSingularValue V₁ (n - 1) * aMin) *
          (matrixSingularValue V₂ (n - 1) * ‖x‖) := by ring
      _ ≤ (matrixSingularValue V₁ (n - 1) * aMin) *
          ‖V₂ᵀ.toEuclideanLin x‖ :=
        mul_le_mul_of_nonneg_left hrow
          (mul_nonneg (matrixSingularValue_nonneg V₁ (n - 1))
            haMinPos.le)
      _ ≤ ‖(V₁ * Matrix.diagonal a).toEuclideanLin
          (V₂ᵀ.toEuclideanLin x)‖ := by
        simpa [mul_comm] using hleft
      _ = _ := by
        simp [V₁, V₂, Matrix.toLpLin_apply,
          Matrix.mulVec_mulVec]

/-- Positivity of the signal lower bound forces the GHM factor to have rank `n`. -/
theorem vandermondeFactor_rank
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rowFrequency : ι → Point d) (columnFrequency : κ → Point d)
    (node : Fin n → Point d) (a : Fin n → ℂ) (aMin : ℝ)
    (hn : 0 < n) (haMinPos : 0 < aMin)
    (haMin : ∀ j, aMin ≤ ‖a j‖)
    (hfull₁ : HasFullColumnRank
      (generalizedVandermonde rowFrequency node))
    (hfull₂ : HasFullColumnRank
      (generalizedVandermonde columnFrequency node)) :
    (generalizedVandermonde rowFrequency node *
      Matrix.diagonal a *
      (generalizedVandermonde columnFrequency node)ᵀ).rank = n := by
  let A := generalizedVandermonde rowFrequency node *
    Matrix.diagonal a *
    (generalizedVandermonde columnFrequency node)ᵀ
  have hgapPos :
      0 < aMin *
          matrixSingularValue
            (generalizedVandermonde rowFrequency node) (n - 1) *
          matrixSingularValue
            (generalizedVandermonde columnFrequency node) (n - 1) :=
    mul_pos
      (mul_pos haMinPos
        (lastSingularValue_pos_of_fullColumnRank _ hn hfull₁))
      (lastSingularValue_pos_of_fullColumnRank _ hn hfull₂)
  have hsvPos : 0 < matrixSingularValue A (n - 1) :=
    hgapPos.trans_le
      (vandermondeFactor_signalSingularValue_lower
        rowFrequency columnFrequency node a aMin hn haMinPos haMin hfull₂)
  have hrankLower : n ≤ A.rank := by
    by_contra h
    have hz := matrixSingularValue_eq_zero_of_rank_le A
      (show A.rank ≤ n - 1 by omega)
    linarith
  have hrankUpper : A.rank ≤ n := by
    unfold A
    exact (Matrix.rank_mul_le_left
      (generalizedVandermonde rowFrequency node *
        Matrix.diagonal a)
      (generalizedVandermonde columnFrequency node)ᵀ).trans
        ((Matrix.rank_mul_le_left
          (generalizedVandermonde rowFrequency node)
          (Matrix.diagonal a)).trans (by
            simpa using Matrix.rank_le_card_width
              (generalizedVandermonde rowFrequency node)))
  exact le_antisymm hrankUpper hrankLower

/-- Unit normalization of every nonempty steering vector. -/
theorem norm_normalizedSteering
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (frequency : ι → Point d) (y : Point d) :
    ‖toLp 2 (normalizedSteering frequency y)‖ = 1 := by
  have hs : ‖toLp 2 (steeringVector frequency y)‖ ≠ 0 := by
    intro hz
    have hv := norm_eq_zero.mp hz
    let i : ι := Classical.choice inferInstance
    have hi := congrArg (fun v => (ofLp v) i) hv
    simp [steeringVector] at hi
  simp [normalizedSteering, norm_smul, hs]

/-- The fixed-rank pointwise projection estimate yields the uniform MUSIC bound. -/
theorem correlationUniformDistance_le_of_fixedRank
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (frequency : ι → Point d) (A E : Matrix ι κ ℂ)
    (hn : 0 < n) (hrows : n < Fintype.card ι)
    (hcols : n ≤ Fintype.card κ)
    (hrank : A.rank = n)
    (hsmall : 2 * matrixSpectralNorm E < matrixSingularValue A (n - 1)) :
    correlationUniformDistance
        (rankNoiseSpaceCorrelation frequency (A + E) n)
        (rankNoiseSpaceCorrelation frequency A n) ≤
      2 * matrixSpectralNorm E / matrixSingularValue A (n - 1) := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  unfold correlationUniformDistance
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro _ ⟨y, rfl⟩
    simpa only [rankNoiseSpaceCorrelation, norm_normalizedSteering,
      mul_one] using
      fixedRankTrailingLeftSingularSubspacePerturbation
        A E n hn hrows hcols hrank hsmall
          (toLp 2 (normalizedSteering frequency y))

/-- Periodic coordinate distance is positive for distinct angular representatives. -/
theorem periodicCoordinateDistance_pos
    {u v : ℝ}
    (hu : -Real.pi < u ∧ u ≤ Real.pi)
    (hv : -Real.pi < v ∧ v ≤ Real.pi)
    (hne : u ≠ v) :
    0 < periodicCoordinateDistance u v := by
  unfold periodicCoordinateDistance
  rw [lt_min_iff]
  constructor
  · exact abs_pos.mpr (sub_ne_zero.mpr hne)
  · rw [sub_pos]
    rw [abs_lt]
    constructor <;> nlinarith [Real.pi_pos]

/-- Periodic coordinate distance is nonnegative on the angular cube. -/
theorem periodicCoordinateDistance_nonneg
    {u v : ℝ}
    (hu : -Real.pi < u ∧ u ≤ Real.pi)
    (hv : -Real.pi < v ∧ v ≤ Real.pi) :
    0 ≤ periodicCoordinateDistance u v := by
  by_cases h : u = v
  · subst v
    simp [periodicCoordinateDistance, Real.pi_pos.le]
  · exact (periodicCoordinateDistance_pos hu hv h).le

/-- Distinct angular representatives have positive periodic `ℓ¹` distance. -/
theorem periodicL1Distance_pos_of_ne
    {d : ℕ} {u v : Point d}
    (hu : InAngularCube u) (hv : InAngularCube v) (hne : u ≠ v) :
    0 < periodicL1Distance u v := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, u k ≠ v k := by
    by_contra h
    apply hne
    funext j
    exact not_ne_iff.mp (not_exists.mp h j)
  unfold periodicL1Distance
  exact Finset.sum_pos'
    (fun j _ => periodicCoordinateDistance_nonneg (hu j) (hv j))
    ⟨k, Finset.mem_univ k, periodicCoordinateDistance_pos (hu k) (hv k) hk⟩

/-- A reduced family in the angular cube has positive minimum periodic separation. -/
theorem periodicMinimumL1Separation_pos
    {d n : ℕ} (μ : AtomicMeasure d n) (hn : 2 ≤ n)
    (hcube : ∀ j, InAngularCube (μ.node j)) :
    0 < periodicMinimumL1Separation μ.node hn := by
  rw [periodicMinimumL1Separation, minimumOverDistinctPairs,
    Finset.lt_inf'_iff]
  intro ij hij
  have hne : ij.1 ≠ ij.2 := by
    simpa [distinctPairs] using hij
  exact periodicL1Distance_pos_of_ne (hcube ij.1) (hcube ij.2)
    (fun h => hne (μ.node_injective h))

/-- Every factor in the explicit segmented MUSIC constant is positive. -/
theorem segmentedVandermondeLowerBound_pos
    {d n A nStar m r D : ℕ} {τ η β : ℝ}
    (μ : AtomicMeasure d n)
    (hn : 2 ≤ n)
    (hclumps : IsAngularClumpStructure μ.node A nStar τ η)
    (hm : 1 ≤ m) (hD : m < D)
    (hβ : 1 / (2 * Real.log 2) < β)
    (hr : 2 * nStar ≤ r) :
    0 < segmentedVandermondeLowerBound d n nStar m r D β
      (periodicMinimumL1Separation μ.node hn) := by
  have hnStarTwo : 2 ≤ nStar := hclumps.1
  have hnStar : 0 < nStar := by omega
  have hrPos : 0 < r :=
    lt_of_lt_of_le (by omega : 0 < 2 * nStar) hr
  have hDPos : 0 < D := Nat.zero_lt_of_lt (hm.trans_lt hD)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβPos : 0 < β := (by positivity : 0 < 1 / (2 * Real.log 2)).trans hβ
  have hexp : Real.exp (1 / (2 * β)) < 2 := by
    calc
      Real.exp (1 / (2 * β)) < Real.exp (Real.log 2) := by
        rw [Real.exp_lt_exp]
        apply (div_lt_iff₀ (by positivity : 0 < 2 * β)).2
        have h := (div_lt_iff₀
          (by positivity : 0 < 2 * Real.log 2)).1 hβ
        nlinarith
      _ = 2 := Real.exp_log (by norm_num)
  have hsep : 0 < periodicMinimumL1Separation μ.node hn :=
    periodicMinimumL1Separation_pos μ hn hclumps.2.2.2.1
  unfold segmentedVandermondeLowerBound
  positivity

/-- The segmented row set has more than `n` samples under `d ≥ 1` and `m ≥ n`. -/
theorem sourceCount_lt_card_segmentedIndex
    {d n m r : ℕ} (hd : 1 ≤ d) (hmn : n ≤ m) :
    n < Fintype.card (SegmentedIndex d m r) := by
  let b := (r + 1) * (m + 1)
  have hmb : m < b := by
    dsimp [b]
    nlinarith
  have hb : 1 ≤ b := by
    have : 0 < b := by
      dsimp [b]
      exact Nat.mul_pos (Nat.succ_pos r) (Nat.succ_pos m)
    omega
  have hbpow : b ≤ b ^ d := by
    simpa only [pow_one] using pow_le_pow_right₀ hb hd
  have : n < b ^ d := (hmn.trans_lt hmb).trans_le hbpow
  simpa only [SegmentedIndex, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_prod] using this

end

end NumDetect
end LeanNumDetect
