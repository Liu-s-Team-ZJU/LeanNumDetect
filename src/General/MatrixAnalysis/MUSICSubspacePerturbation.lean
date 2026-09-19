import General.MatrixAnalysis.SingularValueBounds
import NumDetectMain.Matrices

/-!
Fixed-rank perturbation bounds for the trailing left singular subspace.

This file proves the project-specific estimate directly from finite-dimensional
singular-value variational bounds. It does not add an external theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Matrix WithLp
open scoped InnerProductSpace

namespace LeanNumDetect

noncomputable section

private def trailingSingularSubspace
    {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : EuclideanSpace ℂ ι →ₗ[ℂ] F) (n : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ ι) :=
  Submodule.span ℂ
    (Set.range fun j :
      {j : Fin (Fintype.card ι) // n ≤ (j : ℕ)} =>
        T.isSymmetric_adjoint_comp_self.eigenvectorBasis
          finrank_euclideanSpace j.1)

private theorem trailingSingularSubspace_eq_span_Ici
    {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : EuclideanSpace ℂ ι →ₗ[ℂ] F) {n : ℕ}
    (hn : n < Fintype.card ι) :
    trailingSingularSubspace T n =
      Submodule.span ℂ
        (T.isSymmetric_adjoint_comp_self.eigenvectorBasis
            finrank_euclideanSpace ''
          (Finset.Ici (⟨n, hn⟩ : Fin (Fintype.card ι)) : Set _)) := by
  unfold trailingSingularSubspace
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j.1, by simpa using j.2, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨⟨j, ?_⟩, rfl⟩
    have hj' : (⟨n, hn⟩ : Fin (Fintype.card ι)) ≤ j :=
      Finset.mem_Ici.mp hj
    exact hj'

private theorem finrank_trailingSingularSubspace
    {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : EuclideanSpace ℂ ι →ₗ[ℂ] F) {n : ℕ}
    (hn : n < Fintype.card ι) :
    Module.finrank ℂ (trailingSingularSubspace T n) =
      Fintype.card ι - n := by
  rw [trailingSingularSubspace_eq_span_Ici T hn,
    finrank_orthonormal_span]
  rw [show Finset.Ici (⟨n, hn⟩ : Fin (Fintype.card ι)) =
      (Finset.Iio ⟨n, hn⟩)ᶜ by ext j; simp]
  rw [Finset.card_compl, Fin.card_Iio]
  simp only [Fintype.card_fin]

private theorem norm_sq_apply_eq_sum_singularBasis
    {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : EuclideanSpace ℂ ι →ₗ[ℂ] F) (x : EuclideanSpace ℂ ι) :
    ‖T x‖ ^ 2 = ∑ i : Fin (Fintype.card ι),
      T.isSymmetric_adjoint_comp_self.eigenvalues finrank_euclideanSpace i *
        ‖⟪T.isSymmetric_adjoint_comp_self.eigenvectorBasis
          finrank_euclideanSpace i, x⟫_ℂ‖ ^ 2 := by
  let H := T.adjoint ∘ₗ T
  let hH := T.isSymmetric_adjoint_comp_self
  let b := hH.eigenvectorBasis finrank_euclideanSpace
  have he (i : Fin (Fintype.card ι)) :
      ⟪b i, H x⟫_ℂ =
        (hH.eigenvalues finrank_euclideanSpace i : ℂ) * ⟪b i, x⟫_ℂ := by
    rw [← hH, hH.apply_eigenvectorBasis]
    simp only [inner_smul_real_left, Complex.real_smul, b]
  calc
    ‖T x‖ ^ 2 = RCLike.re ⟪x, H x⟫_ℂ := by
      change ‖T x‖ ^ 2 = RCLike.re ⟪x, T.adjoint (T x)⟫_ℂ
      rw [T.adjoint_inner_right, inner_self_eq_norm_sq]
    _ = ∑ i, RCLike.re (⟪x, b i⟫_ℂ * ⟪b i, H x⟫_ℂ) := by
      rw [← b.sum_inner_mul_inner x (H x), map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [he, mul_left_comm]
      change RCLike.re ((hH.eigenvalues finrank_euclideanSpace i) •
        (⟪x, b i⟫_ℂ * ⟪b i, x⟫_ℂ)) = _
      rw [RCLike.smul_re, inner_mul_symm_re_eq_norm, norm_mul,
        ← inner_conj_symm x (b i), RCLike.norm_conj, ← pow_two]

private theorem norm_apply_le_singularValues_mul_of_mem_trailing
    {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : EuclideanSpace ℂ ι →ₗ[ℂ] F) {n : ℕ}
    (hn : n < Fintype.card ι)
    {x : EuclideanSpace ℂ ι} (hx : x ∈ trailingSingularSubspace T n) :
    ‖T x‖ ≤ T.singularValues n * ‖x‖ := by
  let hH := T.isSymmetric_adjoint_comp_self
  let b := hH.eigenvectorBasis finrank_euclideanSpace
  have hx' :
      x ∈ Submodule.span ℂ
        (b '' (Finset.Ici (⟨n, hn⟩ : Fin (Fintype.card ι)) : Set _)) := by
    simpa only [b, hH] using
      (trailingSingularSubspace_eq_span_Ici T hn ▸ hx)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (T.singularValues_nonneg n)
    (norm_nonneg x))).1
  rw [norm_sq_apply_eq_sum_singularBasis, mul_pow,
    T.sq_singularValues_of_lt finrank_euclideanSpace hn,
    ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : ⟪b j, x⟫_ℂ = 0
  · simpa only [b, hH, hj, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero]
      using (le_refl (0 : ℝ))
  ·
    have hnj : (⟨n, hn⟩ : Fin (Fintype.card ι)) ≤ j := by
      by_contra h
      exact hj (orthonormal_inner_eq_zero_of_mem_span b
        (Finset.Ici (⟨n, hn⟩ : Fin (Fintype.card ι))) hx'
        (by simpa using h))
    exact mul_le_mul_of_nonneg_right
      (hH.eigenvalues_antitone finrank_euclideanSpace hnj) (sq_nonneg _)

private theorem singularValues_mul_norm_le_of_mem_trailing_orthogonal
    {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : EuclideanSpace ℂ ι →ₗ[ℂ] F) {n : ℕ} (hn : 0 < n)
    (hdim : n < Fintype.card ι)
    {x : EuclideanSpace ℂ ι}
    (hx : x ∈ (trailingSingularSubspace T n)ᗮ) :
    T.singularValues (n - 1) * ‖x‖ ≤ ‖T x‖ := by
  let hH := T.isSymmetric_adjoint_comp_self
  let b := hH.eigenvectorBasis finrank_euclideanSpace
  apply (sq_le_sq₀
    (mul_nonneg (T.singularValues_nonneg (n - 1)) (norm_nonneg x))
    (norm_nonneg _)).1
  rw [mul_pow, T.sq_singularValues_of_lt finrank_euclideanSpace (by omega),
    norm_sq_apply_eq_sum_singularBasis,
    ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : ⟪b j, x⟫_ℂ = 0
  · simpa only [b, hH, hj, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero]
      using (le_refl (0 : ℝ))
  ·
    have hjn : j.val < n := by
      by_contra h
      have hbmem : b j ∈ trailingSingularSubspace T n := by
        apply Submodule.subset_span
        exact ⟨⟨j, by omega⟩, rfl⟩
      exact hj (hx (b j) hbmem)
    have hjle : j.val ≤ n - 1 := by omega
    have hjle' : j ≤ (⟨n - 1, by omega⟩ :
        Fin (Fintype.card ι)) :=
      Fin.le_iff_val_le_val.mpr hjle
    exact mul_le_mul_of_nonneg_right
      (hH.eigenvalues_antitone finrank_euclideanSpace hjle') (sq_nonneg _)

private theorem trailingSingularSubspace_invariant
    {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : EuclideanSpace ℂ ι →ₗ[ℂ] F) (n : ℕ)
    {x : EuclideanSpace ℂ ι}
    (hx : x ∈ trailingSingularSubspace T n) :
    (T.adjoint ∘ₗ T) x ∈ trailingSingularSubspace T n := by
  let H := T.adjoint ∘ₗ T
  let hH := T.isSymmetric_adjoint_comp_self
  change H x ∈ trailingSingularSubspace T n
  change x ∈ Submodule.span ℂ
    (Set.range fun j :
      {j : Fin (Fintype.card ι) // n ≤ (j : ℕ)} =>
        hH.eigenvectorBasis finrank_euclideanSpace j.1) at hx
  refine Submodule.span_induction
    (p := fun x _ => H x ∈ trailingSingularSubspace T n) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩
    rw [hH.apply_eigenvectorBasis]
    exact (trailingSingularSubspace T n).smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add] using (trailingSingularSubspace T n).add_mem hx hy
  · intro c x _ hx
    simpa only [map_smul] using (trailingSingularSubspace T n).smul_mem c hx

private theorem norm_apply_starProjection_trailing_orthogonal_le
    {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : EuclideanSpace ℂ ι →ₗ[ℂ] F) (n : ℕ)
    (x : EuclideanSpace ℂ ι) :
    ‖T ((trailingSingularSubspace T n)ᗮ.starProjection x)‖ ≤ ‖T x‖ := by
  let M := trailingSingularSubspace T n
  let y := Mᗮ.starProjection x
  let z := M.starProjection x
  have hy : y ∈ Mᗮ := Submodule.starProjection_apply_mem _ _
  have hz : z ∈ M := Submodule.starProjection_apply_mem _ _
  have hHz : (T.adjoint ∘ₗ T) z ∈ M :=
    trailingSingularSubspace_invariant T n hz
  have horth : ⟪T y, T z⟫_ℂ = 0 := by
    rw [← T.adjoint_inner_right]
    exact inner_eq_zero_symm.mpr (hy _ hHz)
  have hdecomp : x = y + z := by
    dsimp only [y, z, M]
    rw [Submodule.starProjection_orthogonal_val]
    abel
  change ‖T y‖ ≤ ‖T x‖
  rw [hdecomp, map_add]
  have hsquare := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (T y) (T z) horth
  apply (sq_le_sq₀ (norm_nonneg (T y)) (norm_nonneg (T y + T z))).1
  rw [pow_two, pow_two]
  nlinarith [norm_nonneg (T z)]

private theorem trailingSingularSubspace_eq_ker
    {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : EuclideanSpace ℂ ι →ₗ[ℂ] F) {n : ℕ}
    (hn : n < Fintype.card ι)
    (hrank : Module.finrank ℂ T.range = n) :
    trailingSingularSubspace T n = T.ker := by
  have hzero : T.singularValues n = 0 :=
    T.singularValues_eq_zero_iff_le_finrank_range.mpr hrank.le
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    rw [LinearMap.mem_ker]
    have h := norm_apply_le_singularValues_mul_of_mem_trailing T hn hx
    rw [hzero, zero_mul] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  · rw [finrank_trailingSingularSubspace T hn]
    have hdim := T.finrank_range_add_finrank_ker
    rw [finrank_euclideanSpace] at hdim
    omega

private theorem singularValues_mul_norm_le_adjoint_of_mem_range
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : E →ₗ[ℂ] F) {n : ℕ} (hn : 0 < n)
    (hrank : Module.finrank ℂ T.range = n)
    {w : F} (hw : w ∈ T.range) :
    T.singularValues (n - 1) * ‖w‖ ≤ ‖T.adjoint w‖ := by
  have hnDomain : n - 1 < Module.finrank ℂ E := by
    have := T.finrank_range_le
    omega
  obtain ⟨S, hSdim, hSlower⟩ :=
    singularValues_lower_subspace_exists T hnDomain
  have hsigma : 0 < T.singularValues (n - 1) := by
    rw [T.singularValues_pos_iff_lt_finrank_range, hrank]
    omega
  let TS : S →ₗ[ℂ] F := T.domRestrict S
  have hTSinj : Function.Injective TS := by
    intro x y hxy
    apply Subtype.ext
    have hzero : T ((x : E) - (y : E)) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hxy
    have hbound := hSlower ((x : E) - (y : E))
      (S.sub_mem x.property y.property)
    rw [hzero, norm_zero] at hbound
    exact sub_eq_zero.mp (norm_eq_zero.mp (by
      nlinarith [norm_nonneg ((x : E) - (y : E))]))
  have hTSrange : TS.range = T.range := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rw [LinearMap.finrank_range_of_inj hTSinj, hSdim, hrank]
      omega
  rw [← hTSrange] at hw
  obtain ⟨x, rfl⟩ := hw
  by_cases hTx : T (x : E) = 0
  · change T.singularValues (n - 1) * ‖T (x : E)‖ ≤
      ‖T.adjoint (T (x : E))‖
    rw [hTx]
    simp
  have hTxPos : 0 < ‖T (x : E)‖ := norm_pos_iff.mpr hTx
  have hcs :
      ‖T (x : E)‖ ^ 2 ≤ ‖(x : E)‖ * ‖T.adjoint (T (x : E))‖ := by
    have h := re_inner_le_norm (𝕜 := ℂ) (x : E) (T.adjoint (T (x : E)))
    simpa only [T.adjoint_inner_right, inner_self_eq_norm_sq,
      RCLike.ofReal_re] using h
  have h₁ := mul_le_mul_of_nonneg_left hcs
    (T.singularValues_nonneg (n - 1))
  have h₂ := mul_le_mul_of_nonneg_right
    (hSlower (x : E) x.property) (norm_nonneg (T.adjoint (T (x : E))))
  change T.singularValues (n - 1) * ‖T (x : E)‖ ≤
    ‖T.adjoint (T (x : E))‖
  apply (mul_le_mul_iff_left₀ hTxPos).mp
  nlinarith

private theorem projection_difference_le_of_cross_bounds
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (N M : Submodule ℂ E) {c : ℝ} (hc : 0 ≤ c)
    (hMS : ∀ y ∈ M, ‖Nᗮ.starProjection y‖ ≤ c * ‖y‖)
    (hNM : ∀ z ∈ N, ‖Mᗮ.starProjection z‖ ≤ c * ‖z‖)
    (x : E) :
    ‖M.starProjection x - N.starProjection x‖ ≤ c * ‖x‖ := by
  have hSM : ∀ z ∈ Nᗮ, ‖M.starProjection z‖ ≤ c * ‖z‖ := by
    intro z hz
    let y := M.starProjection z
    by_cases hy : y = 0
    · change ‖y‖ ≤ c * ‖z‖
      rw [hy, norm_zero]
      exact mul_nonneg hc (norm_nonneg z)
    have hyM : y ∈ M := Submodule.starProjection_apply_mem _ _
    have hinner :
        RCLike.re ⟪y, z⟫_ℂ = ‖y‖ ^ 2 := by
      simpa only [y, Submodule.starProjection_apply, Submodule.coe_norm] using
        (Submodule.re_inner_starProjection_eq_normSq M z)
    have hreplace : ⟪Nᗮ.starProjection y, z⟫_ℂ = ⟪y, z⟫_ℂ := by
      rw [Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr hz]
    have hsq :
        ‖y‖ ^ 2 ≤ ‖Nᗮ.starProjection y‖ * ‖z‖ := by
      rw [← hinner, ← hreplace]
      exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    have hcross := hMS y hyM
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
    nlinarith [norm_nonneg z]
  let u := M.starProjection (Nᗮ.starProjection x)
  let v := Mᗮ.starProjection (N.starProjection x)
  have huM : u ∈ M := Submodule.starProjection_apply_mem _ _
  have hvMo : v ∈ Mᗮ := Submodule.starProjection_apply_mem _ _
  have hdecomp :
      M.starProjection x - N.starProjection x = u - v := by
    dsimp only [u, v]
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_orthogonal_val]
    simp only [map_sub]
    abel
  have huv : ⟪u, -v⟫_ℂ = 0 := by
    have huv0 : ⟪u, v⟫_ℂ = 0 := hvMo u huM
    simp only [inner_neg_right, huv0, neg_zero]
  have hsquare :
      ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    simpa only [sub_eq_add_neg, norm_neg, pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u (-v) huv
  have hu := hSM (Nᗮ.starProjection x)
    (Submodule.starProjection_apply_mem _ _)
  have hv := hNM (N.starProjection x)
    (Submodule.starProjection_apply_mem _ _)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg x))).1
  rw [hdecomp, hsquare, mul_pow,
    Submodule.norm_sq_eq_add_norm_sq_starProjection x N]
  nlinarith [norm_nonneg u, norm_nonneg v,
    norm_nonneg (Nᗮ.starProjection x), norm_nonneg (N.starProjection x)]

namespace NumDetect

/-- Fixed-rank perturbation estimate for the trailing left singular subspace.

The proof uses singular-value variational bounds and the two complementary
cross-projection estimates. -/
theorem fixedRankTrailingLeftSingularSubspacePerturbation
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A E : Matrix ι κ ℂ) (n : ℕ)
    (hn : 0 < n) (hrows : n < Fintype.card ι)
    (hcols : n ≤ Fintype.card κ)
    (hrank : A.rank = n)
    (hsmall :
      2 * matrixSpectralNorm E < matrixSingularValue A (n - 1))
    (x : EuclideanSpace ℂ ι) :
    |‖(trailingLeftSingularSubspace (A + E) n).starProjection x‖ -
        ‖(trailingLeftSingularSubspace A n).starProjection x‖| ≤
      (2 * matrixSpectralNorm E /
        matrixSingularValue A (n - 1)) * ‖x‖ := by
  let T := A.toEuclideanLin
  let L := T.adjoint
  let B := (A + E).toEuclideanLin
  let LB := B.adjoint
  let N := trailingSingularSubspace L n
  let M := trailingSingularSubspace LB n
  let σ := matrixSingularValue A (n - 1)
  let ε := matrixSpectralNorm E
  have hTrank : Module.finrank ℂ T.range = n := by
    change Module.finrank ℂ (LinearMap.range
      ((Matrix.toLin (EuclideanSpace.basisFun κ ℂ).toBasis
        (EuclideanSpace.basisFun ι ℂ).toBasis) A)) = n
    rw [← A.rank_eq_finrank_range_toLin
      (EuclideanSpace.basisFun ι ℂ).toBasis
      (EuclideanSpace.basisFun κ ℂ).toBasis, hrank]
  have hLrank : Module.finrank ℂ L.range = n := by
    simpa only [L, T] using T.finrank_range_adjoint.trans hTrank
  have hN : N = T.rangeᗮ := by
    calc
      N = L.ker := trailingSingularSubspace_eq_ker L (by simpa using hrows) hLrank
      _ = T.rangeᗮ := by simpa only [L] using T.orthogonal_range.symm
  have hNperp : Nᗮ = T.range := by rw [hN]; simp
  have hσdef : σ = T.singularValues (n - 1) := rfl
  have hσpos : 0 < σ := by
    rw [hσdef, T.singularValues_pos_iff_lt_finrank_range, hTrank]
    omega
  have hε : 0 ≤ ε := norm_nonneg _
  have hdiff : ‖(LB - L).toContinuousLinearMap‖ = ε := by
    have heq : LB - L = E.toEuclideanLin.adjoint := by
      ext y
      simp [LB, L, B, T]
    rw [heq, LinearMap.adjoint_toContinuousLinearMap,
      ContinuousLinearMap.adjoint.norm_map]
    rfl
  have hLzero : L.singularValues n = 0 :=
    L.singularValues_eq_zero_iff_le_finrank_range.mpr hLrank.le
  have hLBtail : LB.singularValues n ≤ ε := by
    have hweyl := abs_singularValues_sub_le_operatorNorm LB L
      (by simpa using hrows)
    rw [hLzero, sub_zero, abs_of_nonneg (LB.singularValues_nonneg n), hdiff] at hweyl
    exact hweyl
  have hLlower :
      ∀ z ∈ T.range, σ * ‖z‖ ≤ ‖L z‖ := by
    intro z hz
    simpa only [hσdef, L] using
      singularValues_mul_norm_le_adjoint_of_mem_range T hn hTrank hz
  have hLB_on_M : ∀ y ∈ M, ‖LB y‖ ≤ ε * ‖y‖ := by
    intro y hy
    exact (norm_apply_le_singularValues_mul_of_mem_trailing LB
      (by simpa using hrows) hy).trans
        (mul_le_mul_of_nonneg_right hLBtail (norm_nonneg y))
  have hLminusLB : ∀ y, ‖(L - LB) y‖ ≤ ε * ‖y‖ := by
    intro y
    have hnorm : ‖(L - LB).toContinuousLinearMap‖ = ε := by
      rw [show L - LB = -(LB - L) by abel]
      change ‖-(LB - L).toContinuousLinearMap‖ = ε
      rw [norm_neg, hdiff]
    calc
      ‖(L - LB) y‖ =
          ‖(L - LB).toContinuousLinearMap y‖ := rfl
      _ ≤ ‖(L - LB).toContinuousLinearMap‖ * ‖y‖ :=
        (L - LB).toContinuousLinearMap.le_opNorm y
      _ = ε * ‖y‖ := by rw [hnorm]
  have hMS : ∀ y ∈ M, ‖Nᗮ.starProjection y‖ ≤ (2 * ε / σ) * ‖y‖ := by
    intro y hy
    let z := Nᗮ.starProjection y
    have hzRange : z ∈ T.range := by
      rw [← hNperp]
      exact Submodule.starProjection_apply_mem _ _
    have hyzKer : y - z ∈ L.ker := by
      rw [← trailingSingularSubspace_eq_ker L
        (by simpa using hrows) hLrank]
      have horth :
          y - z ∈ (Nᗮ)ᗮ :=
        Submodule.sub_starProjection_mem_orthogonal (K := Nᗮ) y
      rw [Submodule.orthogonal_orthogonal] at horth
      exact horth
    have hLyz : L y = L z := by
      rw [LinearMap.mem_ker] at hyzKer
      simpa only [map_sub, sub_eq_zero] using hyzKer
    have hLy :
        ‖L y‖ ≤ 2 * ε * ‖y‖ := by
      calc
        ‖L y‖ = ‖LB y + (L - LB) y‖ := by congr 1 <;> simp
        _ ≤ ‖LB y‖ + ‖(L - LB) y‖ := norm_add_le _ _
        _ ≤ ε * ‖y‖ + ε * ‖y‖ :=
          add_le_add (hLB_on_M y hy) (hLminusLB y)
        _ = 2 * ε * ‖y‖ := by ring
    have hzLower := hLlower z hzRange
    rw [← hLyz] at hzLower
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hσpos).2
    nlinarith
  have hLB_lower_on_range :
      ∀ z ∈ T.range, (σ - ε) * ‖z‖ ≤ ‖LB z‖ := by
    intro z hz
    have hexact := hLlower z hz
    have hpert := hLminusLB z
    have htriangle : ‖L z‖ ≤ ‖LB z‖ + ‖(L - LB) z‖ := by
      calc
        ‖L z‖ = ‖LB z + (L - LB) z‖ := by congr 1 <;> simp
        _ ≤ _ := norm_add_le _ _
    linarith
  have hLBhead :
      σ - ε ≤ LB.singularValues (n - 1) := by
    apply le_singularValues_of_subspace LB (i := n - 1)
      (by simpa using (show n - 1 < Fintype.card ι by omega)) T.range
    · simpa [Nat.sub_add_cancel hn] using hTrank
    · exact hLB_lower_on_range
  have hNM : ∀ z ∈ N, ‖Mᗮ.starProjection z‖ ≤ (2 * ε / σ) * ‖z‖ := by
    intro z hz
    let y := Mᗮ.starProjection z
    have hyMo : y ∈ Mᗮ := Submodule.starProjection_apply_mem _ _
    have hhead :=
      singularValues_mul_norm_le_of_mem_trailing_orthogonal LB hn
        (by simpa using hrows) hyMo
    have hcoer : (σ - ε) * ‖y‖ ≤ ‖LB y‖ :=
      (mul_le_mul_of_nonneg_right hLBhead (norm_nonneg y)).trans hhead
    have hproject : ‖LB y‖ ≤ ‖LB z‖ := by
      exact norm_apply_starProjection_trailing_orthogonal_le LB n z
    have hzKer : L z = 0 := by
      rw [← LinearMap.mem_ker, ← trailingSingularSubspace_eq_ker L
        (by simpa using hrows) hLrank]
      exact hz
    have hLBz : ‖LB z‖ ≤ ε * ‖z‖ := by
      have h := hLminusLB z
      rw [LinearMap.sub_apply, hzKer, zero_sub, norm_neg] at h
      exact h
    have hyLe : ‖y‖ ≤ ‖z‖ :=
      (Mᗮ.norm_starProjection_apply_le z)
    have hmain : σ * ‖y‖ ≤ 2 * ε * ‖z‖ := by
      calc
        σ * ‖y‖ = (σ - ε) * ‖y‖ + ε * ‖y‖ := by ring
        _ ≤ ε * ‖z‖ + ε * ‖z‖ := add_le_add
          (hcoer.trans (hproject.trans hLBz))
          (mul_le_mul_of_nonneg_left hyLe hε)
        _ = 2 * ε * ‖z‖ := by ring
    change ‖y‖ ≤ (2 * ε / σ) * ‖z‖
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hσpos).2 (by simpa [mul_comm] using hmain)
  have hproj :
      ‖M.starProjection x - N.starProjection x‖ ≤
        (2 * ε / σ) * ‖x‖ :=
    projection_difference_le_of_cross_bounds N M
      (div_nonneg (mul_nonneg (by norm_num) hε) hσpos.le) hMS hNM x
  have hreverse :
      |‖M.starProjection x‖ - ‖N.starProjection x‖| ≤
        ‖M.starProjection x - N.starProjection x‖ :=
    abs_norm_sub_norm_le _ _
  have htrail (C : Matrix ι κ ℂ) :
      trailingLeftSingularSubspace C n =
        trailingSingularSubspace C.toEuclideanLin.adjoint n := by
    rfl
  rw [htrail (A + E), htrail A]
  simpa only [M, N, LB, L, B, T, σ, ε] using hreverse.trans hproj

end NumDetect

end

end LeanNumDetect
