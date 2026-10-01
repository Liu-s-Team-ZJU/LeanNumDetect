import NumDetect.MUSICSelector
import NumDetect.Segmented.Interpolation
import NumDetect.Segmented.Threshold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix WithLp
open scoped BigOperators InnerProductSpace

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Separation yields a product lower bound in terms of the nearest source. -/
theorem separated_distance_product_growth
    {α : Type*} [PseudoMetricSpace α] {n : ℕ}
    (hn : 0 < n) (node : Fin n → α) (y : α)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hsep : ∀ i j : Fin n, i ≠ j → Δ ≤ dist (node i) (node j)) :
    (Δ / 2) ^ (n - 1) * min (Δ / 4) (finiteSourceDistance hn node y) ≤
      ∏ j : Fin n, dist y (node j) := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin n))
    (fun j => dist y (node j)) (fin_univ_nonempty hn)
  have hmin : finiteSourceDistance hn node y = dist y (node i) := by
    apply le_antisymm
    · exact Finset.inf'_le _ (Finset.mem_univ i)
    · apply (Finset.le_inf'_iff (fin_univ_nonempty hn)
        (fun j => dist y (node j))).2
      intro j hj
      exact hi j hj
  have hother (j : Fin n) (hji : j ≠ i) : Δ / 2 ≤ dist y (node j) := by
    by_cases hnear : dist y (node i) ≤ Δ / 2
    · have htriangle : dist (node i) (node j) ≤
          dist (node i) y + dist y (node j) := dist_triangle _ _ _
      have hseparate := hsep i j (Ne.symm hji)
      rw [dist_comm (node i) y] at htriangle
      linarith
    · have hsmallest := hi j (Finset.mem_univ j)
      linarith
  have hproduct :
      (Δ / 2) ^ (n - 1) ≤
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          dist y (node j) := by
    have hle :
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
            (Δ / 2 : ℝ)) ≤
          ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
            dist y (node j) := by
      apply Finset.prod_le_prod
      · intro j hj
        positivity
      · intro j hj
        exact hother j (Finset.ne_of_mem_erase hj)
    have hcard : ((Finset.univ : Finset (Fin n)).erase i).card = n - 1 := by
      simp
    rw [Finset.prod_const, hcard] at hle
    exact hle
  have hnearbound : min (Δ / 4) (finiteSourceDistance hn node y) ≤
      dist y (node i) := by
    rw [hmin]
    exact min_le_right _ _
  have hnonneg : 0 ≤ min (Δ / 4) (finiteSourceDistance hn node y) := by
    rw [hmin]
    exact le_min (by linarith) dist_nonneg
  calc
    (Δ / 2) ^ (n - 1) * min (Δ / 4) (finiteSourceDistance hn node y) ≤
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          dist y (node j)) * min (Δ / 4) (finiteSourceDistance hn node y) := by
      exact mul_le_mul_of_nonneg_right hproduct hnonneg
    _ ≤ (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          dist y (node j)) * dist y (node i) := by
      apply mul_le_mul_of_nonneg_left hnearbound
      exact Finset.prod_nonneg (by intro j hj; exact dist_nonneg)
    _ = ∏ j : Fin n, dist y (node j) := by
      simpa only using (Finset.prod_erase_mul
        (Finset.univ : Finset (Fin n))
        (fun j => dist y (node j)) (Finset.mem_univ i))

/-- Euclidean-coordinate version of the separated source-distance product bound. -/
theorem separated_euclidean_distance_product_growth
    {d n : ℕ} (hn : 0 < n) (node : Fin n → Point d) (y : Point d)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hsep : ∀ i j : Fin n, i ≠ j →
      Δ ≤ pointEuclideanDistance (node i) (node j)) :
    (Δ / 2) ^ (n - 1) *
      min (Δ / 4) (finiteEuclideanSourceDistance hn node y) ≤
      ∏ j : Fin n, pointEuclideanDistance y (node j) := by
  let nodeE : Fin n → EuclideanSpace ℝ (Fin d) := fun j => WithLp.toLp 2 (node j)
  have h := separated_distance_product_growth hn nodeE (WithLp.toLp 2 y)
    Δ hΔ hsep
  simpa only [finiteSourceDistance, finiteEuclideanSourceDistance,
    pointEuclideanDistance, nodeE] using h


theorem steeringVector_norm_sq_eq_card
    {d : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d) (y : Point d) :
    ‖toLp 2 (steeringVector frequency y)‖ ^ 2 = (Fintype.card ι : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [steeringVector, Complex.norm_exp, Complex.mul_re]

theorem steeringVector_norm_eq_sqrt_card
    {d : ℕ} {ι : Type*} [Fintype ι]
    (frequency : ι → Point d) (y : Point d) :
    ‖toLp 2 (steeringVector frequency y)‖ = Real.sqrt (Fintype.card ι : ℝ) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [steeringVector_norm_sq_eq_card, Real.sq_sqrt (Nat.cast_nonneg _)]


/-- A vector orthogonal to the exact signal space certifies a lower bound for
MUSIC's noise-space projection. -/
theorem norm_inner_le_music_noise_projection
    {ι : Type*} [Fintype ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι))
    (c z : EuclideanSpace ℂ ι) (hc : c ∈ S) :
    ‖⟪c, z⟫_ℂ‖ ≤ ‖c‖ * ‖S.starProjection z‖ := by
  calc
    ‖⟪c, z⟫_ℂ‖ = ‖⟪S.starProjection c, z⟫_ℂ‖ := by
      rw [S.starProjection_eq_self_iff.mpr hc]
    _ = ‖⟪c, S.starProjection z⟫_ℂ‖ := by
      rw [S.inner_starProjection_left_eq_right]
    _ ≤ ‖c‖ * ‖S.starProjection z‖ := norm_inner_le_norm _ _

/-- The coefficient vector of a polynomial vanishing on all source steering
vectors is orthogonal to the Vandermonde range. -/
theorem vandermonde_annihilator_mem_orthogonal
    {d n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (frequency : ι → Point d) (node : Fin n → Point d)
    (c : ι → ℂ)
    (hvanish : ∀ j : Fin n,
      ∑ i : ι, c i * steeringVector frequency (node j) i = 0) :
    toLp 2 (star c) ∈
      (generalizedVandermonde frequency node).toEuclideanLin.rangeᗮ := by
  let V := generalizedVandermonde frequency node
  have hVc : Vᵀ *ᵥ c = 0 := by
    funext j
    simpa [V, Matrix.mulVec, dotProduct, generalizedVandermonde,
      mul_comm] using hvanish j
  apply (Submodule.mem_orthogonal' V.toEuclideanLin.range _).2
  intro u hu
  obtain ⟨x, rfl⟩ := hu
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toLpLin_apply, ofLp_toLp, star_star]
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, hVc]
  simp

/-- A rank-`n` Vandermonde factorization has exactly the Vandermonde column
space as its signal space. -/
theorem vandermondeFactor_range_eq_vandermonde_range
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (frequency : ι → Point d) (node : Fin n → Point d)
    (B : Matrix (Fin n) κ ℂ)
    (hrank :
      (generalizedVandermonde frequency node * B).rank = n) :
    (generalizedVandermonde frequency node * B).toEuclideanLin.range =
      (generalizedVandermonde frequency node).toEuclideanLin.range := by
  let V := generalizedVandermonde frequency node
  let A := V * B
  have hsubset : A.toEuclideanLin.range ≤ V.toEuclideanLin.range := by
    intro z hz
    obtain ⟨x, rfl⟩ := hz
    refine ⟨B.toEuclideanLin x, ?_⟩
    simp [A, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have hAdim : Module.finrank ℂ A.toEuclideanLin.range = n := by
    change Module.finrank ℂ (LinearMap.range
      ((Matrix.toLin (EuclideanSpace.basisFun κ ℂ).toBasis
        (EuclideanSpace.basisFun ι ℂ).toBasis) A)) = n
    rw [← A.rank_eq_finrank_range_toLin
      (EuclideanSpace.basisFun ι ℂ).toBasis
      (EuclideanSpace.basisFun κ ℂ).toBasis]
    exact hrank
  have hVdim : Module.finrank ℂ V.toEuclideanLin.range = n := by
    have hlo := Submodule.finrank_mono hsubset
    have hhi := V.toEuclideanLin.finrank_range_le
    simp at hhi
    omega
  exact Submodule.eq_of_le_of_finrank_eq hsubset (hAdim.trans hVdim.symm)

/-- Projection of an unnormalized steering vector is its norm times the
normalized MUSIC residual. -/
theorem steering_projection_norm_eq_norm_mul_music_correlation
    {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [Nonempty ι]
    (frequency : ι → Point d) (A : Matrix ι κ ℂ)
    (signalRank : ℕ) (y : Point d) :
    ‖(trailingLeftSingularSubspace A signalRank).starProjection
        (toLp 2 (steeringVector frequency y))‖ =
      ‖toLp 2 (steeringVector frequency y)‖ *
        rankNoiseSpaceCorrelation frequency A signalRank y := by
  let S := trailingLeftSingularSubspace A signalRank
  let z := toLp 2 (steeringVector frequency y)
  have hs : ‖z‖ ≠ 0 := by
    intro hz
    have hv := norm_eq_zero.mp hz
    let i : ι := Classical.choice inferInstance
    have hi := congrArg (fun v => (ofLp v) i) hv
    simp [z, steeringVector] at hi
  have hscale :
      z = (‖z‖ : ℂ) • toLp 2 (normalizedSteering frequency y) := by
    ext i
    simp [z, normalizedSteering, smul_smul, hs]
  calc
    ‖S.starProjection z‖ =
        ‖S.starProjection ((‖z‖ : ℂ) •
          toLp 2 (normalizedSteering frequency y))‖ := by rw [← hscale]
    _ = ‖(‖z‖ : ℂ) • S.starProjection
          (toLp 2 (normalizedSteering frequency y))‖ := by rw [map_smul]
    _ = ‖z‖ * rankNoiseSpaceCorrelation frequency A signalRank y := by
      rw [norm_smul]
      simp [rankNoiseSpaceCorrelation, S, z]

/-- A polynomial annihilating all source columns is controlled pointwise by
the exact rank-`n` MUSIC residual. -/
theorem vandermonde_polynomial_le_music_residual
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (frequency : ι → Point d) (node : Fin n → Point d)
    (B : Matrix (Fin n) κ ℂ)
    (hrows : n < Fintype.card ι)
    (hrank : (generalizedVandermonde frequency node * B).rank = n)
    (c : ι → ℂ)
    (hvanish : ∀ j : Fin n,
      ∑ i : ι, c i * steeringVector frequency (node j) i = 0)
    (y : Point d) :
    ‖∑ i : ι, c i * steeringVector frequency y i‖ ≤
      ‖toLp 2 c‖ * ‖toLp 2 (steeringVector frequency y)‖ *
        rankNoiseSpaceCorrelation frequency
          (generalizedVandermonde frequency node * B) n y := by
  let V := generalizedVandermonde frequency node
  let A := V * B
  let z := toLp 2 (steeringVector frequency y)
  let q := toLp 2 (star c)
  have hcard : 0 < Fintype.card ι := by omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hcard
  have horthV : q ∈ V.toEuclideanLin.rangeᗮ :=
    vandermonde_annihilator_mem_orthogonal frequency node c hvanish
  have horthA : q ∈ A.toEuclideanLin.rangeᗮ := by
    rw [vandermondeFactor_range_eq_vandermonde_range
      frequency node B hrank]
    exact horthV
  have hcert : q ∈ trailingLeftSingularSubspace A n := by
    rw [trailingLeftSingularSubspace_eq_range_orthogonal A n hrows hrank]
    exact horthA
  have hpoly : (∑ i : ι, c i * steeringVector frequency y i) = ⟪q, z⟫_ℂ := by
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, mul_comm]
  have hqnorm : ‖q‖ = ‖toLp 2 c‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [q, EuclideanSpace.norm_sq_eq]
  have hprojection :=
    steering_projection_norm_eq_norm_mul_music_correlation frequency A n y
  calc
    ‖∑ i : ι, c i * steeringVector frequency y i‖ = ‖⟪q, z⟫_ℂ‖ := by
      rw [hpoly]
    _ ≤ ‖q‖ * ‖(trailingLeftSingularSubspace A n).starProjection z‖ :=
      norm_inner_le_music_noise_projection
        (trailingLeftSingularSubspace A n) q z hcert
    _ = ‖toLp 2 c‖ * ‖z‖ * rankNoiseSpaceCorrelation frequency A n y := by
      rw [hqnorm, hprojection]
      ring

/-- The Euclidean coefficient norm is bounded by total coefficient mass. -/
theorem coefficient_l2_le_l1
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ) :
    ‖toLp 2 c‖ ≤ ∑ i : ι, ‖c i‖ := by
  have hdecomp :
      toLp 2 c = ∑ i : ι,
        (PiLp.single 2 i (c i) : EuclideanSpace ℂ ι) := by
    ext j
    simp
  calc
    ‖toLp 2 c‖ = ‖∑ i : ι,
        (PiLp.single 2 i (c i) : EuclideanSpace ℂ ι)‖ := by
      rw [← hdecomp]
    _ ≤ ∑ i : ι, ‖(PiLp.single 2 i (c i) : EuclideanSpace ℂ ι)‖ :=
      norm_sum_le _ _
    _ = ∑ i : ι, ‖c i‖ := by
      simp


namespace SegmentedPolynomial

noncomputable section

private theorem exists_finiteProduct_of_linearFactors
    {ι : Type*} [DecidableEq ι]
    {d D : ℕ} (hD : 0 < D)
    (F : ι → SegmentedPolynomial d 1 0 D)
    (S : Finset ι) (hSD : S.card < D) :
    ∃ P : SegmentedPolynomial d S.card 0 D,
      ∀ y : Point d,
        P.angularValue y = ∏ j ∈ S, (F j).angularValue y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨one d D hD, ?_⟩
      intro y
      simp [angularValue, eval_one]
  | @insert a S ha ih =>
      have hScard : S.card < D := by
        rw [Finset.card_insert_of_notMem ha] at hSD
        omega
      obtain ⟨P, hP⟩ := ih hScard
      have hsum : S.card + 1 < D := by
        rw [Finset.card_insert_of_notMem ha] at hSD
        exact hSD
      rw [Finset.card_insert_of_notMem ha] at hSD ⊢
      refine ⟨P.mul (F a) hsum, ?_⟩
      intro y
      rw [angularValue_mul, hP, Finset.prod_insert ha]
      ring

private def scalarMul {d m r D : ℕ} (c : ℂ)
    (P : SegmentedPolynomial d m r D) : SegmentedPolynomial d m r D where
  hD := P.hD
  coeff a := c * P.coeff a

private theorem angularValue_scalarMul {d m r D : ℕ} (c : ℂ)
    (P : SegmentedPolynomial d m r D) (y : Point d) :
    (scalarMul c P).angularValue y = c * P.angularValue y := by
  rw [angularValue_eq_angularTrigPolynomial,
    angularValue_eq_angularTrigPolynomial]
  unfold angularTrigPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [scalarMul]
  ring

theorem fullColumnRank_of_linearSeparators
    {d m r D n : ℕ} (hn : 0 < n) (hnm : n ≤ m) (hmD : m < D)
    (node : Fin n → Point d)
    (F : Fin n → Fin n → SegmentedPolynomial d 1 0 D)
    (hzero : ∀ i j, i ≠ j → (F i j).angularValue (node j) = 0)
    (hnonzero : ∀ i j, i ≠ j → (F i j).angularValue (node i) ≠ 0) :
    HasFullColumnRank (segmentedVandermonde m r D node) := by
  classical
  have hD : 0 < D := by omega
  have hP (i : Fin n) :
      ∃ P : SegmentedPolynomial d m r D,
        (∀ j, j ≠ i → P.angularValue (node j) = 0) ∧
          P.angularValue (node i) ≠ 0 := by
    let S := (Finset.univ : Finset (Fin n)).erase i
    have hcard : S.card = n - 1 := by
      simp [S, Finset.card_erase_of_mem]
    have hSD : S.card < D := by rw [hcard]; omega
    obtain ⟨P, hPval⟩ :=
      exists_finiteProduct_of_linearFactors hD (F i) S hSD
    have hSm : S.card ≤ m := by rw [hcard]; omega
    let Q := P.widen hSm (Nat.zero_le r) hmD
    refine ⟨Q, ?_, ?_⟩
    · intro j hji
      have hjS : j ∈ S := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
      rw [show Q.angularValue (node j) = P.angularValue (node j) by
        exact SegmentedPolynomial.angularValue_widen P hSm (Nat.zero_le r) hmD _]
      rw [hPval]
      exact Finset.prod_eq_zero hjS (hzero i j (Ne.symm hji))
    · rw [show Q.angularValue (node i) = P.angularValue (node i) by
        exact SegmentedPolynomial.angularValue_widen P hSm (Nat.zero_le r) hmD _]
      rw [hPval]
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact hnonzero i j (Finset.mem_erase.mp hj).1.symm
  choose P hP using hP
  let G (i : Fin n) : SegmentedPolynomial d m r D :=
    scalarMul ((P i).angularValue (node i))⁻¹ (P i)
  have hG : IsLagrangeFamily node G := by
    intro i j
    simp only [G, angularValue_scalarMul]
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact inv_mul_cancel₀ (hP i).2
    · rw [if_neg hij, (hP i).1 j (Ne.symm hij), mul_zero]
  have hsingular :=
    segmentedPolynomial_lagrange_minimumSingularValue hmD hn node G hG
  exact segmentedThreshold_fullColumnRank_of_lastSingularValue_pos
    (segmentedVandermonde m r D node) hn hsingular.1

theorem fullColumnRank_of_coordinateFactors
    {d m r D n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hnm : n ≤ m) (hmD : m < D)
    (node : Fin n → Point d)
    (factor : Fin d → Point d → SegmentedPolynomial d 1 0 D)
    (hvalue : ∀ k x y, (factor k x).angularValue y =
      Complex.exp (Complex.I * (y k : ℂ)) -
        Complex.exp (Complex.I * (x k : ℂ)))
    (hphase : ∀ i j, i ≠ j → ∃ k : Fin d,
      Complex.exp (Complex.I * (node i k : ℂ)) ≠
        Complex.exp (Complex.I * (node j k : ℂ))) :
    HasFullColumnRank (segmentedVandermonde m r D node) := by
  classical
  let selected (i j : Fin n) : Fin d :=
    if hij : i = j then ⟨0, hd⟩ else Classical.choose (hphase i j hij)
  let F (i j : Fin n) := factor (selected i j) (node j)
  apply fullColumnRank_of_linearSeparators hn hnm hmD node F
  · intro i j hij
    simp only [F, hvalue, sub_self]
  · intro i j hij
    have hselected :
        Complex.exp (Complex.I * (node i (selected i j) : ℂ)) ≠
          Complex.exp (Complex.I * (node j (selected i j) : ℂ)) := by
      simpa only [selected, dif_neg hij] using
        Classical.choose_spec (hphase i j hij)
    simp only [F, hvalue]
    exact sub_ne_zero.mpr hselected

end
end SegmentedPolynomial

private theorem chord_lower_scalar {x w : ℝ}
    (hw : w < 2 * Real.pi) (hx : |x| ≤ w) :
    (2 / Real.pi) * (1 - w / (2 * Real.pi)) * |x| ≤
      ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hs : 0 ≤ |x| := abs_nonneg _
  have hsπ : |x| / 2 ≤ Real.pi := by linarith
  have hsin : 0 ≤ Real.sin (|x| / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hsπ
  have hnorm :
      ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ =
        2 * Real.sin (|x| / 2) := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith)]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hnorm]
  by_cases hsmall : |x| ≤ Real.pi
  · have hhalf : |x| / 2 ≤ Real.pi / 2 := by linarith
    have hchord := Real.mul_le_sin (by positivity : 0 ≤ |x| / 2) hhalf
    have hfactor : 1 - w / (2 * Real.pi) ≤ 1 := by
      have : 0 ≤ w := hs.trans hx
      have : 0 ≤ w / (2 * Real.pi) := by positivity
      linarith
    have hA : 0 ≤ 2 / Real.pi := by positivity
    calc
      (2 / Real.pi) * (1 - w / (2 * Real.pi)) * |x| ≤
          (2 / Real.pi) * |x| :=
        by simpa only [mul_one] using
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor hA) hs
      _ = 2 * ((2 / Real.pi) * (|x| / 2)) := by ring
      _ ≤ 2 * Real.sin (|x| / 2) := by linarith
  · have hlarge : |x| / 2 ≥ Real.pi / 2 := by linarith
    have harg : 0 ≤ Real.pi - |x| / 2 ∧ Real.pi - |x| / 2 ≤ Real.pi / 2 := by
      constructor <;> linarith
    have hchord := Real.mul_le_sin harg.1 harg.2
    rw [Real.sin_pi_sub] at hchord
    have hwside : 0 ≤ 1 - w / (2 * Real.pi) := by
      apply sub_nonneg.mpr
      exact (div_le_one (by positivity)).mpr hw.le
    have hA : 0 ≤ 2 / Real.pi := by positivity
    have hscale :
        (1 - w / (2 * Real.pi)) * |x| ≤ 2 * Real.pi - |x| := by
      calc
        (1 - w / (2 * Real.pi)) * |x| ≤
            (1 - w / (2 * Real.pi)) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_left (by linarith) hwside
        _ = 2 * Real.pi - w := by field_simp
        _ ≤ 2 * Real.pi - |x| := by linarith
    calc
      (2 / Real.pi) * (1 - w / (2 * Real.pi)) * |x| =
          (2 / Real.pi) * ((1 - w / (2 * Real.pi)) * |x|) := by ring
      _ ≤ (2 / Real.pi) * (2 * Real.pi - |x|) :=
        mul_le_mul_of_nonneg_left hscale hA
      _ = 2 * ((2 / Real.pi) * (Real.pi - |x| / 2)) := by ring
      _ ≤ 2 * Real.sin (|x| / 2) := by linarith

theorem exp_I_chord_lower_of_width {u v w : ℝ}
    (hw : w < 2 * Real.pi) (huv : |u - v| ≤ w) :
    (2 / Real.pi) * (1 - w / (2 * Real.pi)) * |u - v| ≤
      ‖Complex.exp (Complex.I * (u : ℂ)) -
        Complex.exp (Complex.I * (v : ℂ))‖ := by
  have hfactor :
      Complex.exp (Complex.I * (u : ℂ)) -
          Complex.exp (Complex.I * (v : ℂ)) =
        Complex.exp (Complex.I * (v : ℂ)) *
          (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact chord_lower_scalar hw huv


private def growthZeroIndex (d D : ℕ) : SegmentedIndex d 1 0 :=
  fun _ => (0, 0)

private def growthCoordinateIndex {d D : ℕ} (k : Fin d) : SegmentedIndex d 1 0 :=
  fun t => (0, if t = k then 1 else 0)

private theorem growthCoordinateIndex_ne_zero {d D : ℕ} (k : Fin d) :
    growthCoordinateIndex (D := D) k ≠ growthZeroIndex d D := by
  intro h
  have hk := congrFun h k
  simp [growthCoordinateIndex, growthZeroIndex] at hk

/-- A degree-one factor of modulus-one coefficient mass two. -/
private def growthCoordinateFactor {d D : ℕ} (hD : 1 < D)
    (k : Fin d) (x : Point d) : SegmentedPolynomial d 1 0 D where
  hD := hD
  coeff a :=
    if a = growthCoordinateIndex (D := D) k then 1
    else if a = growthZeroIndex d D then -Complex.exp (Complex.I * (x k : ℂ))
    else 0

private theorem growthCoordinateFactor_mass {d D : ℕ} (hD : 1 < D)
    (k : Fin d) (x : Point d) :
    (growthCoordinateFactor hD k x).mass = 2 := by
  classical
  unfold SegmentedPolynomial.mass growthCoordinateFactor
  have hnorm (a : SegmentedIndex d 1 0) :
      ‖if a = growthCoordinateIndex (D := D) k then (1 : ℂ)
        else if a = growthZeroIndex d D then -Complex.exp (Complex.I * (x k : ℂ))
        else 0‖ =
      if a = growthCoordinateIndex (D := D) k then 1
      else if a = growthZeroIndex d D then 1 else 0 := by
    split_ifs <;> simp
  simp_rw [hnorm]
  have hsplit (a : SegmentedIndex d 1 0) :
      (if a = growthCoordinateIndex (D := D) k then (1 : ℝ)
        else if a = growthZeroIndex d D then 1 else 0) =
      (if a = growthCoordinateIndex (D := D) k then 1 else 0) +
      (if a = growthZeroIndex d D then 1 else 0) := by
    by_cases ha : a = growthCoordinateIndex (D := D) k
    · subst a
      simp [growthCoordinateIndex_ne_zero (D := D) k]
    · simp [ha]
  simp_rw [hsplit, Finset.sum_add_distrib]
  simp
  norm_num

private theorem growthCoordinateFactor_value {d D : ℕ} (hD : 1 < D)
    (k : Fin d) (x y : Point d) :
    (growthCoordinateFactor hD k x).angularValue y =
      Complex.exp (Complex.I * (y k : ℂ)) -
        Complex.exp (Complex.I * (x k : ℂ)) := by
  classical
  rw [SegmentedPolynomial.angularValue_eq_angularTrigPolynomial]
  unfold angularTrigPolynomial
  have hterm (a : SegmentedIndex d 1 0) :
      (growthCoordinateFactor hD k x).coeff a *
          Complex.exp (Complex.I *
            ((∑ t, (segmentedPolynomialFrequency d 1 0 D a t : ℝ) * y t : ℝ) : ℂ)) =
        if a = growthCoordinateIndex (D := D) k then
          Complex.exp (Complex.I * (y k : ℂ))
        else if a = growthZeroIndex d D then
          -Complex.exp (Complex.I * (x k : ℂ)) else 0 := by
    by_cases ha : a = growthCoordinateIndex (D := D) k
    · subst a
      have hcoordinate (t : Fin d) :
          (segmentedPolynomialFrequency d 1 0 D
            (growthCoordinateIndex (D := D) k) t : ℝ) * y t =
          if t = k then y t else 0 := by
        by_cases ht : t = k
        · subst t
          simp [segmentedPolynomialFrequency, growthCoordinateIndex]
        · simp [segmentedPolynomialFrequency, growthCoordinateIndex, ht]
      have hsum :
          (∑ t, (segmentedPolynomialFrequency d 1 0 D
            (growthCoordinateIndex (D := D) k) t : ℝ) * y t) = y k := by
        simp_rw [hcoordinate]
        simp
      simp [growthCoordinateFactor, hsum]
    · by_cases hb : a = growthZeroIndex d D
      · subst a
        simp [growthCoordinateFactor, ha, growthZeroIndex,
          segmentedPolynomialFrequency]
      · simp [growthCoordinateFactor, ha, hb]
  simp_rw [hterm]
  have hsplit (a : SegmentedIndex d 1 0) :
      (if a = growthCoordinateIndex (D := D) k then
          Complex.exp (Complex.I * (y k : ℂ))
        else if a = growthZeroIndex d D then
          -Complex.exp (Complex.I * (x k : ℂ)) else 0) =
      (if a = growthCoordinateIndex (D := D) k then
          Complex.exp (Complex.I * (y k : ℂ)) else 0) +
      (if a = growthZeroIndex d D then
          -Complex.exp (Complex.I * (x k : ℂ)) else 0) := by
    by_cases ha : a = growthCoordinateIndex (D := D) k
    · subst a
      simp [growthCoordinateIndex_ne_zero (D := D) k]
    · simp [ha]
  simp_rw [hsplit, Finset.sum_add_distrib]
  simp
  ring

/-- A polynomial on the segmented array vanishing at every node, with a
quantitative value at the chosen test point. -/
theorem exists_segmented_growth_certificate
    {d n m r D : ℕ} (hn : 0 < n) (hm : n ≤ m) (hmD : m < D)
    (node : Fin n → Point d) (k : Fin n → Fin d) (y : Point d) :
    ∃ P : SegmentedPolynomial d m r D,
      P.mass ≤ (2 : ℝ) ^ n ∧
      (∀ j, P.angularValue (node j) = 0) ∧
      P.angularValue y =
        ∏ j : Fin n,
          (Complex.exp (Complex.I * (y (k j) : ℂ)) -
            Complex.exp (Complex.I * (node j (k j) : ℂ))) := by
  classical
  have hD1 : 1 < D := by omega
  have hnD : 1 * n < D := by omega
  let F (j : Fin n) : SegmentedPolynomial d 1 0 D :=
    growthCoordinateFactor hD1 (k j) (node j)
  let Q : SegmentedPolynomial d (1 * n) (0 * n) D :=
    SegmentedPolynomial.prod n F hnD
  let P : SegmentedPolynomial d m r D :=
    Q.widen (by simpa using hm) (by simp) hmD
  refine ⟨P, ?_, ?_, ?_⟩
  · calc
      P.mass = Q.mass := SegmentedPolynomial.mass_widen Q _ _ hmD
      _ ≤ ∏ j : Fin n, (F j).mass := SegmentedPolynomial.mass_prod_le F hnD
      _ = (2 : ℝ) ^ n := by simp [F, growthCoordinateFactor_mass]
  · intro j
    simp only [P, SegmentedPolynomial.angularValue_widen,
      Q, SegmentedPolynomial.angularValue_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [F, growthCoordinateFactor_value]
  · simp [P, Q, F, SegmentedPolynomial.angularValue_prod,
      growthCoordinateFactor_value]

/-- At least one coordinate captures a `1 / √d` fraction of the Euclidean
norm of a nonzero-dimensional real vector. -/
theorem exists_coordinate_abs_ge_euclidean_div_sqrt
    {d : ℕ} (hd : 0 < d) (x : Point d) :
    ∃ k : Fin d, ‖toLp 2 x‖ / Real.sqrt d ≤ |x k| := by
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin d)) (fun k => |x k|) (fin_univ_nonempty hd)
  have hle (j : Fin d) : |x j| ≤ |x k| := hk j (Finset.mem_univ j)
  have hsum : (∑ j : Fin d, |x j| ^ 2) ≤ (d : ℝ) * |x k| ^ 2 := by
    calc
      (∑ j : Fin d, |x j| ^ 2) ≤ ∑ _j : Fin d, |x k| ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (abs_nonneg _) (hle j) 2
      _ = (d : ℝ) * |x k| ^ 2 := by simp
  have hsq : ‖toLp 2 x‖ ^ 2 = ∑ j : Fin d, |x j| ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs]
  have hdpos : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hsqrt : (Real.sqrt d * |x k|) ^ 2 = (d : ℝ) * |x k| ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  refine ⟨k, (div_le_iff₀ hdpos).2 ?_⟩
  rw [mul_comm |x k| (Real.sqrt d)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))).1
  rwa [hsqrt, hsq]

theorem segmented_node_phase_separation_of_width
    {d n : ℕ} (node : Fin n → Point d) (Δ w : ℝ)
    (hΔ : 0 < Δ) (hw : w < 2 * Real.pi)
    (hwidth : ∀ i j k, |node i k - node j k| ≤ w)
    (hsep : ∀ i j, i ≠ j →
      Δ ≤ pointEuclideanDistance (node i) (node j)) :
    ∀ i j, i ≠ j → ∃ k : Fin d,
      Complex.exp (Complex.I * (node i k : ℂ)) ≠
        Complex.exp (Complex.I * (node j k : ℂ)) := by
  intro i j hij
  have hneq : node i ≠ node j := by
    intro heq
    have h := hsep i j hij
    rw [heq] at h
    simp [pointEuclideanDistance] at h
    linarith
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hneq
  refine ⟨k, ?_⟩
  intro heq
  have hchord := exp_I_chord_lower_of_width hw (hwidth i j k)
  rw [heq, sub_self, norm_zero] at hchord
  have hκ : 0 < (2 / Real.pi) * (1 - w / (2 * Real.pi)) := by
    have hκ' : 0 < 1 - w / (2 * Real.pi) := by
      apply sub_pos.mpr
      exact (div_lt_one (by positivity)).mpr hw
    positivity
  have hzero : |node i k - node j k| = 0 := by
    nlinarith [abs_nonneg (node i k - node j k)]
  exact hk (sub_eq_zero.mp (abs_eq_zero.mp hzero))

theorem segmentedVandermonde_fullColumnRank_of_width
    {d n m r D : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hm : n ≤ m) (hmD : m < D)
    (node : Fin n → Point d) (Δ w : ℝ)
    (hΔ : 0 < Δ) (hw : w < 2 * Real.pi)
    (hwidth : ∀ i j k, |node i k - node j k| ≤ w)
    (hsep : ∀ i j, i ≠ j →
      Δ ≤ pointEuclideanDistance (node i) (node j)) :
    HasFullColumnRank (segmentedVandermonde m r D node) := by
  have hD1 : 1 < D := by omega
  exact SegmentedPolynomial.fullColumnRank_of_coordinateFactors
    hd hn hm hmD node
    (growthCoordinateFactor hD1)
    (growthCoordinateFactor_value hD1)
    (segmented_node_phase_separation_of_width node Δ w hΔ hw hwidth hsep)

theorem segmentedPolynomial_angularValue_eq_steering
    {d m r D : ℕ} (P : SegmentedPolynomial d m r D)
    (y : Point d) :
    P.angularValue y =
      ∑ a : SegmentedIndex d m r,
        P.coeff a * steeringVector (segmentedFrequency d m r D) y a := by
  rw [SegmentedPolynomial.angularValue_eq_angularTrigPolynomial]
  simp only [angularTrigPolynomial, steeringVector, segmentedFrequency,
    segmentedPolynomialFrequency, dot]
  apply Finset.sum_congr rfl
  intro a _
  congr 1

/-- The first consecutive block gives a polynomial certificate whose value
is bounded below by the product of Euclidean source distances. -/
theorem exists_segmented_growth_certificate_lower
    {d n m r D : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hm : n ≤ m) (hmD : m < D)
    (node : Fin n → Point d) (y : Point d) (w : ℝ)
    (hw : w < 2 * Real.pi)
    (hwidth : ∀ j k, |y k - node j k| ≤ w) :
    ∃ P : SegmentedPolynomial d m r D,
      P.mass ≤ (2 : ℝ) ^ n ∧
      (∀ j, P.angularValue (node j) = 0) ∧
      (((2 / Real.pi) * (1 - w / (2 * Real.pi)) / Real.sqrt d) ^ n *
        ∏ j : Fin n, pointEuclideanDistance y (node j)) ≤
          ‖P.angularValue y‖ := by
  classical
  have hdpos : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hκ : 0 ≤ 1 - w / (2 * Real.pi) := by
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity)).mpr hw.le
  let k (j : Fin n) : Fin d :=
    Classical.choose (exists_coordinate_abs_ge_euclidean_div_sqrt hd (y - node j))
  have hk (j : Fin n) :
      pointEuclideanDistance y (node j) / Real.sqrt d ≤
        |y (k j) - node j (k j)| := by
    simpa [k, pointEuclideanDistance_eq_norm, Pi.sub_apply] using
      Classical.choose_spec
        (exists_coordinate_abs_ge_euclidean_div_sqrt hd (y - node j))
  obtain ⟨P, hmass, hzero, hvalue⟩ :=
    exists_segmented_growth_certificate hn hm hmD node k y
  refine ⟨P, hmass, hzero, ?_⟩
  have hfactor (j : Fin n) :
      ((2 / Real.pi) * (1 - w / (2 * Real.pi)) / Real.sqrt d) *
          pointEuclideanDistance y (node j) ≤
        ‖Complex.exp (Complex.I * (y (k j) : ℂ)) -
          Complex.exp (Complex.I * (node j (k j) : ℂ))‖ := by
    have hchord := exp_I_chord_lower_of_width hw (hwidth j (k j))
    have hscale : 0 ≤ (2 / Real.pi) * (1 - w / (2 * Real.pi)) := by
      positivity
    calc
      ((2 / Real.pi) * (1 - w / (2 * Real.pi)) / Real.sqrt d) *
          pointEuclideanDistance y (node j) =
          ((2 / Real.pi) * (1 - w / (2 * Real.pi))) *
            (pointEuclideanDistance y (node j) / Real.sqrt d) := by ring
      _ ≤ ((2 / Real.pi) * (1 - w / (2 * Real.pi))) *
          |y (k j) - node j (k j)| :=
        mul_le_mul_of_nonneg_left (hk j) hscale
      _ ≤ _ := hchord
  have hproduct :
      (∏ j : Fin n,
        ((2 / Real.pi) * (1 - w / (2 * Real.pi)) / Real.sqrt d) *
          pointEuclideanDistance y (node j)) ≤
        ∏ j : Fin n,
          ‖Complex.exp (Complex.I * (y (k j) : ℂ)) -
            Complex.exp (Complex.I * (node j (k j) : ℂ))‖ := by
    apply Finset.prod_le_prod
    · intro j hj
      exact mul_nonneg (div_nonneg
        (mul_nonneg (by positivity) hκ) hdpos.le)
        (by simp [pointEuclideanDistance])
    · intro j hj
      exact hfactor j
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hproduct
  simpa only [hvalue, norm_prod, Finset.card_fin] using hproduct

/-- Residual growth for the exact segmented GHM, in the factorized constant
that arises directly from the degree-one polynomial certificate. -/
theorem segmentedMUSIC_growth_factored
    {d n m r D : ℕ} (μ : AtomicMeasure d n) (K : Set (Point d))
    (Δ w : ℝ) (hd : 0 < d) (hn : 0 < n)
    (hm : n ≤ m) (hmD : m < D)
    (hΔ : 0 < Δ) (hw : w < 2 * Real.pi)
    (hnodeK : ∀ j, μ.node j ∈ K)
    (hwidth : ∀ u ∈ K, ∀ v ∈ K, ∀ k, |u k - v k| ≤ w)
    (hsep : ∀ i j, i ≠ j →
      Δ ≤ pointEuclideanDistance (μ.node i) (μ.node j)) :
    HasFullColumnRank (segmentedVandermonde m r D μ.node) ∧
    ∀ y ∈ K,
      ((((2 / Real.pi) * (1 - w / (2 * Real.pi)) / Real.sqrt d) ^ n *
          (Δ / 2) ^ (n - 1)) /
          ((2 : ℝ) ^ n *
            Real.sqrt (Fintype.card (SegmentedIndex d m r) : ℝ))) *
        min (Δ / 4) (finiteEuclideanSourceDistance hn μ.node y) ≤
      rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
        (segmentedNoiselessMatrix m r D μ) n y := by
  classical
  let frequency := segmentedFrequency d m r D
  let V := segmentedVandermonde m r D μ.node
  let B : Matrix (Fin n) (SegmentedIndex d m r) ℂ :=
    Matrix.diagonal (segmentedPhaseAmplitude m r D μ) * Vᵀ
  let A := segmentedNoiselessMatrix m r D μ
  have hfull : HasFullColumnRank V :=
    segmentedVandermonde_fullColumnRank_of_width hd hn hm hmD μ.node Δ w hΔ hw
      (fun i j k => hwidth (μ.node i) (hnodeK i) (μ.node j) (hnodeK j) k)
      hsep
  have hrows : n < Fintype.card (SegmentedIndex d m r) :=
    sourceCount_lt_card_segmentedIndex hd hm
  have hrank : A.rank = n := by
    simpa only [A, segmentedNoiselessMatrix, segmentedVandermonde,
      segmentedColumnVandermonde] using
      vandermondeFactor_rank frequency frequency μ.node
        (segmentedPhaseAmplitude m r D μ) (minAmplitude μ hn)
        hn (minAmplitude_pos μ hn)
        (minAmplitude_le_norm_segmentedPhaseAmplitude m r D μ hn)
        hfull hfull
  have hAB : V * B = A := by
    simp [A, B, V, segmentedNoiselessMatrix,
      segmentedVandermonde, segmentedColumnVandermonde, Matrix.mul_assoc]
  refine ⟨hfull, ?_⟩
  intro y hyK
  obtain ⟨P, hmass, hzero, hPvalue⟩ :=
    exists_segmented_growth_certificate_lower hd hn hm hmD μ.node y w
      hw (fun j k => hwidth y hyK (μ.node j) (hnodeK j) k)
  have hvanish (j : Fin n) :
      (∑ a : SegmentedIndex d m r,
          P.coeff a * steeringVector frequency (μ.node j) a) = 0 := by
    rw [← segmentedPolynomial_angularValue_eq_steering]
    exact hzero j
  have hcert := vandermonde_polynomial_le_music_residual
    frequency μ.node B hrows (by
      change (V * B).rank = n
      rw [hAB]
      exact hrank) P.coeff hvanish y
  have hcoeff : ‖toLp 2 P.coeff‖ ≤ (2 : ℝ) ^ n :=
    (coefficient_l2_le_l1 P.coeff).trans hmass
  have hnorm :
      ‖toLp 2 (steeringVector frequency y)‖ =
        Real.sqrt (Fintype.card (SegmentedIndex d m r) : ℝ) :=
    steeringVector_norm_eq_sqrt_card frequency y
  have hRnonneg :
      0 ≤ rankNoiseSpaceCorrelation frequency A n y := norm_nonneg _
  have hPupper :
      ‖P.angularValue y‖ ≤
        (2 : ℝ) ^ n * Real.sqrt (Fintype.card (SegmentedIndex d m r) : ℝ) *
          rankNoiseSpaceCorrelation frequency A n y := by
    rw [segmentedPolynomial_angularValue_eq_steering]
    calc
      ‖∑ a, P.coeff a * steeringVector frequency y a‖ ≤
          ‖toLp 2 P.coeff‖ * ‖toLp 2 (steeringVector frequency y)‖ *
            rankNoiseSpaceCorrelation frequency (V * B) n y := hcert
      _ ≤ (2 : ℝ) ^ n *
          Real.sqrt (Fintype.card (SegmentedIndex d m r) : ℝ) *
            rankNoiseSpaceCorrelation frequency A n y := by
        rw [hAB, hnorm]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _)) hRnonneg
  have hCnonneg :
      0 ≤ (2 / Real.pi) * (1 - w / (2 * Real.pi)) / Real.sqrt d := by
    have hκ : 0 ≤ 1 - w / (2 * Real.pi) := by
      apply sub_nonneg.mpr
      exact (div_le_one (by positivity)).mpr hw.le
    positivity
  have hproduct := separated_euclidean_distance_product_growth
    hn μ.node y Δ hΔ hsep
  have hnumerator :
      ((2 / Real.pi) * (1 - w / (2 * Real.pi)) / Real.sqrt d) ^ n *
          (Δ / 2) ^ (n - 1) *
          min (Δ / 4) (finiteEuclideanSourceDistance hn μ.node y) ≤
        (2 : ℝ) ^ n *
          Real.sqrt (Fintype.card (SegmentedIndex d m r) : ℝ) *
          rankNoiseSpaceCorrelation frequency A n y := by
    calc
      _ ≤ ((2 / Real.pi) * (1 - w / (2 * Real.pi)) / Real.sqrt d) ^ n *
          ∏ j : Fin n, pointEuclideanDistance y (μ.node j) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hproduct (pow_nonneg hCnonneg n)
      _ ≤ ‖P.angularValue y‖ := hPvalue
      _ ≤ _ := hPupper
  have hdenpos :
      0 < (2 : ℝ) ^ n *
        Real.sqrt (Fintype.card (SegmentedIndex d m r) : ℝ) := by
    have hM : 0 < Real.sqrt (Fintype.card (SegmentedIndex d m r) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast (show 0 < Fintype.card (SegmentedIndex d m r) by omega))
    positivity
  change
    ((((2 / Real.pi) * (1 - w / (2 * Real.pi)) / Real.sqrt d) ^ n *
          (Δ / 2) ^ (n - 1)) /
          ((2 : ℝ) ^ n *
            Real.sqrt (Fintype.card (SegmentedIndex d m r) : ℝ))) *
        min (Δ / 4) (finiteEuclideanSourceDistance hn μ.node y) ≤
      rankNoiseSpaceCorrelation frequency A n y
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hdenpos).2
  calc
    _ ≤ (2 : ℝ) ^ n *
        Real.sqrt (Fintype.card (SegmentedIndex d m r) : ℝ) *
          rankNoiseSpaceCorrelation frequency A n y := hnumerator
    _ = _ := by ring

/-- The explicit Euclidean growth constant for the segmented MUSIC residual. -/
def segmentedMUSICGrowthConstant (d n m r : ℕ) (Δ w : ℝ) : ℝ :=
  ((1 - w / (2 * Real.pi)) ^ n * (Δ / 2) ^ (n - 1)) /
    ((segmentedLength m r : ℝ) ^ ((d : ℝ) / 2) *
      (Real.pi * Real.sqrt d) ^ n)

theorem segmentedMUSICGrowthConstant_pos
    {d n m r : ℕ} {Δ w : ℝ}
    (hd : 0 < d) (hn : 0 < n) (hΔ : 0 < Δ)
    (hw : w < 2 * Real.pi) :
    0 < segmentedMUSICGrowthConstant d n m r Δ w := by
  have hκ : 0 < 1 - w / (2 * Real.pi) := by
    apply sub_pos.mpr
    exact (div_lt_one (by positivity)).mpr hw
  have hL : (0 : ℝ) < segmentedLength m r := by
    exact_mod_cast (show 0 < segmentedLength m r by
      simp [segmentedLength])
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  unfold segmentedMUSICGrowthConstant
  positivity

private theorem segmented_growth_constant_algebra
    (n : ℕ) (κ δ p s M : ℝ)
    (hp : p ≠ 0) (hs : s ≠ 0) (hM : M ≠ 0) :
    (((2 / p) * κ / s) ^ n * δ) / ((2 : ℝ) ^ n * M) =
      (κ ^ n * δ) / (M * (p * s) ^ n) := by
  rw [div_pow, mul_pow, div_pow]
  field_simp
  ring

private theorem sqrt_natCast_pow_eq_rpow (L d : ℕ) :
    Real.sqrt ((L : ℝ) ^ d) = (L : ℝ) ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg L) d (1 / 2)]
  congr 1
  ring

/-- On a width-`w` field of view, the exact noiseless segmented MUSIC residual
grows at least linearly from the finite source set, with an explicit positive
constant. -/
theorem segmentedMUSIC_growth
    {d n m r D : ℕ} (μ : AtomicMeasure d n)
    (K : Set (Point d)) (Δ w : ℝ)
    (hd : 0 < d) (hn : 0 < n) (hm : n ≤ m) (hmD : m < D)
    (hΔ : 0 < Δ) (hw : w < 2 * Real.pi)
    (hnodeK : ∀ j, μ.node j ∈ K)
    (hwidth : ∀ u ∈ K, ∀ v ∈ K, ∀ k, |u k - v k| ≤ w)
    (hsep : ∀ i j, i ≠ j →
      Δ ≤ pointEuclideanDistance (μ.node i) (μ.node j)) :
    HasFullColumnRank (segmentedVandermonde m r D μ.node) ∧
    0 < segmentedMUSICGrowthConstant d n m r Δ w ∧
    ∀ y ∈ K,
      segmentedMUSICGrowthConstant d n m r Δ w *
          min (Δ / 4) (finiteEuclideanSourceDistance hn μ.node y) ≤
        rankNoiseSpaceCorrelation (segmentedFrequency d m r D)
          (segmentedNoiselessMatrix m r D μ) n y := by
  obtain ⟨hfull, hgrowth⟩ :=
    segmentedMUSIC_growth_factored μ K Δ w hd hn hm hmD hΔ hw
      hnodeK hwidth hsep
  refine ⟨hfull, segmentedMUSICGrowthConstant_pos hd hn hΔ hw, ?_⟩
  intro y hyK
  have hL : (0 : ℝ) < segmentedLength m r := by
    exact_mod_cast (show 0 < segmentedLength m r by
      simp [segmentedLength])
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hconstant :
      ((((2 / Real.pi) * (1 - w / (2 * Real.pi)) / Real.sqrt d) ^ n *
          (Δ / 2) ^ (n - 1)) /
          ((2 : ℝ) ^ n *
            Real.sqrt (Fintype.card (SegmentedIndex d m r) : ℝ))) =
        segmentedMUSICGrowthConstant d n m r Δ w := by
    rw [segmentedMUSICGrowthConstant, card_segmentedIndex]
    rw [Nat.cast_pow, sqrt_natCast_pow_eq_rpow]
    exact segmented_growth_constant_algebra n
      (1 - w / (2 * Real.pi)) ((Δ / 2) ^ (n - 1))
      Real.pi (Real.sqrt d)
      ((segmentedLength m r : ℝ) ^ ((d : ℝ) / 2))
      Real.pi_ne_zero
      (ne_of_gt (Real.sqrt_pos.2 hdreal))
      (ne_of_gt (Real.rpow_pos_of_pos hL _))
  rw [← hconstant]
  exact hgrowth y hyK

end
end NumDetect
end LeanNumDetect
