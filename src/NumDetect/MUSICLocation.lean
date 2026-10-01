import NumDetect.MUSIC

/-! Quantitative matching of separated MUSIC locations from a uniform residual bound. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open WithLp

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Distance from a point to a nonempty finite family of source locations. -/
def finiteSourceDistance {α : Type*} [PseudoMetricSpace α] {n : ℕ}
    (hn : 0 < n) (node : Fin n → α) (y : α) : ℝ :=
  Finset.univ.inf' (fin_univ_nonempty hn) fun j => dist y (node j)

/-- A separated low-residual `n`-tuple can be matched bijectively to the true
`n`-tuple when the exact residual grows linearly away from the support. -/
theorem separatedMUSIC_location_matching
    {α : Type*} [PseudoMetricSpace α] {n : ℕ}
    (hn : 0 < n) (node estimate : Fin n → α) (K : Set α)
    (R Rσ : α → ℝ) (Δ c ε : ℝ)
    (hc : 0 < c) (hsmall : ε < c * Δ / 8)
    (hnodeK : ∀ j, node j ∈ K)
    (hestimateK : ∀ i, estimate i ∈ K)
    (hzero : ∀ j, R (node j) = 0)
    (hpert : ∀ y ∈ K, |Rσ y - R y| ≤ ε)
    (hgrowth : ∀ y ∈ K,
      c * min (Δ / 4) (finiteSourceDistance hn node y) ≤ R y)
    (hestimateSeparated : ∀ i k, i ≠ k → Δ / 2 ≤ dist (estimate i) (estimate k))
    (hcomparison :
      (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
        (fun i => Rσ (estimate i)) ≤
      (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
        (fun j => Rσ (node j))) :
    ∃ e : Equiv.Perm (Fin n),
      ∀ i, dist (estimate i) (node (e i)) ≤ 2 * ε / c := by
  classical
  have htrue :
      (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
        (fun j => Rσ (node j)) ≤ ε := by
    apply (Finset.sup'_le_iff (fin_univ_nonempty hn) (fun j => Rσ (node j))).2
    intro j _
    have h := hpert (node j) (hnodeK j)
    rw [hzero j, sub_zero] at h
    exact (abs_le.mp h).2
  have hnear (i : Fin n) :
      ∃ j : Fin n, dist (estimate i) (node j) ≤ 2 * ε / c := by
    have hestimated : Rσ (estimate i) ≤ ε :=
      (Finset.le_sup' (fun k => Rσ (estimate k)) (Finset.mem_univ i)).trans
        (hcomparison.trans htrue)
    have h := hpert (estimate i) (hestimateK i)
    have hresidual : R (estimate i) ≤ 2 * ε := by
      have := (abs_le.mp h).1
      linarith
    have hbound := (hgrowth (estimate i) (hestimateK i)).trans hresidual
    have hcut : finiteSourceDistance hn node (estimate i) < Δ / 4 := by
      by_contra hnot
      have hge : Δ / 4 ≤ finiteSourceDistance hn node (estimate i) :=
        le_of_not_gt hnot
      rw [min_eq_left hge] at hbound
      linarith
    have hdistance : finiteSourceDistance hn node (estimate i) ≤ 2 * ε / c := by
      rw [min_eq_right hcut.le] at hbound
      apply (le_div_iff₀ hc).2
      simpa only [mul_comm] using hbound
    obtain ⟨j, _, hj⟩ := Finset.exists_min_image
      (Finset.univ : Finset (Fin n))
      (fun j => dist (estimate i) (node j)) (fin_univ_nonempty hn)
    have hmin : finiteSourceDistance hn node (estimate i) =
        dist (estimate i) (node j) := by
      apply le_antisymm
      · exact Finset.inf'_le _ (Finset.mem_univ j)
      · apply (Finset.le_inf'_iff (fin_univ_nonempty hn)
          (fun k => dist (estimate i) (node k))).2
        intro k hk
        exact hj k hk
    exact ⟨j, hmin ▸ hdistance⟩
  choose f hf using hnear
  have hinj : Function.Injective f := by
    intro i k hik
    by_contra hne
    have hsep := hestimateSeparated i k hne
    have htriangle := dist_triangle (estimate i) (node (f i)) (estimate k)
    have hsecond : dist (node (f i)) (estimate k) ≤ 2 * ε / c := by
      calc
        dist (node (f i)) (estimate k) = dist (estimate k) (node (f i)) := dist_comm _ _
        _ = dist (estimate k) (node (f k)) := by rw [hik]
        _ ≤ 2 * ε / c := hf k
    have hnearPair : dist (estimate i) (estimate k) ≤ 4 * ε / c := by
      calc
        dist (estimate i) (estimate k) ≤
            dist (estimate i) (node (f i)) + dist (node (f i)) (estimate k) :=
          htriangle
        _ ≤ 2 * ε / c + 2 * ε / c := add_le_add (hf i) hsecond
        _ = 4 * ε / c := by ring
    have hstrict : 4 * ε / c < Δ / 2 := by
      apply (div_lt_iff₀ hc).2
      nlinarith [hsmall]
    linarith
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective f hinj.bijective_of_finite
  exact ⟨e, hf⟩

/-- Euclidean distance on the real coordinate representation used by the manuscript. -/
def pointEuclideanDistance {d : ℕ} (u v : Point d) : ℝ :=
  dist (toLp 2 u) (toLp 2 v)

theorem pointEuclideanDistance_eq_norm {d : ℕ} (u v : Point d) :
    pointEuclideanDistance u v = ‖toLp 2 (u - v)‖ := by
  simp [pointEuclideanDistance, dist_eq_norm]

/-- Euclidean distance from a point to a nonempty finite source set. -/
def finiteEuclideanSourceDistance {d n : ℕ} (hn : 0 < n)
    (node : Fin n → Point d) (y : Point d) : ℝ :=
  Finset.univ.inf' (fin_univ_nonempty hn)
    fun j => pointEuclideanDistance y (node j)

/-- Euclidean-coordinate form of separated low-residual MUSIC matching. -/
theorem separatedMUSIC_location_matching_euclidean
    {d n : ℕ} (hn : 0 < n)
    (node estimate : Fin n → Point d) (K : Set (Point d))
    (R Rσ : Point d → ℝ) (Δ c ε : ℝ)
    (hc : 0 < c) (hsmall : ε < c * Δ / 8)
    (hnodeK : ∀ j, node j ∈ K)
    (hestimateK : ∀ i, estimate i ∈ K)
    (hzero : ∀ j, R (node j) = 0)
    (hpert : ∀ y ∈ K, |Rσ y - R y| ≤ ε)
    (hgrowth : ∀ y ∈ K,
      c * min (Δ / 4) (finiteEuclideanSourceDistance hn node y) ≤ R y)
    (hestimateSeparated : ∀ i k, i ≠ k →
      Δ / 2 ≤ pointEuclideanDistance (estimate i) (estimate k))
    (hcomparison :
      (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
        (fun i => Rσ (estimate i)) ≤
      (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
        (fun j => Rσ (node j))) :
    ∃ e : Equiv.Perm (Fin n),
      ∀ i, pointEuclideanDistance (estimate i) (node (e i)) ≤ 2 * ε / c := by
  let nodeE : Fin n → EuclideanSpace ℝ (Fin d) := fun j => toLp 2 (node j)
  let estimateE : Fin n → EuclideanSpace ℝ (Fin d) := fun i => toLp 2 (estimate i)
  let KE : Set (EuclideanSpace ℝ (Fin d)) := {z | ofLp z ∈ K}
  let RE : EuclideanSpace ℝ (Fin d) → ℝ := fun z => R (ofLp z)
  let RσE : EuclideanSpace ℝ (Fin d) → ℝ := fun z => Rσ (ofLp z)
  have hgrowthE : ∀ z ∈ KE,
      c * min (Δ / 4) (finiteSourceDistance hn nodeE z) ≤ RE z := by
    intro z hz
    have h := hgrowth (ofLp z) hz
    simpa [finiteSourceDistance, finiteEuclideanSourceDistance,
      pointEuclideanDistance, nodeE, RE] using h
  have hpertE : ∀ z ∈ KE, |RσE z - RE z| ≤ ε := by
    intro z hz
    exact hpert (ofLp z) hz
  have hsepE : ∀ i k, i ≠ k → Δ / 2 ≤ dist (estimateE i) (estimateE k) :=
    hestimateSeparated
  have hcompE :
      (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
        (fun i => RσE (estimateE i)) ≤
      (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
        (fun j => RσE (nodeE j)) := hcomparison
  exact separatedMUSIC_location_matching hn nodeE estimateE KE RE RσE Δ c ε
    hc hsmall hnodeK hestimateK hzero hpertE hgrowthE hsepE hcompE

/-- Pointwise control from the supremum of two bounded MUSIC correlations. -/
theorem correlationUniformDistance_pointwise_of_unitBounds
    {d : ℕ} (Rσ R : Point d → ℝ) (ε : ℝ)
    (hσ : ∀ y, 0 ≤ Rσ y ∧ Rσ y ≤ 1)
    (hR : ∀ y, 0 ≤ R y ∧ R y ≤ 1)
    (huniform : correlationUniformDistance Rσ R ≤ ε)
    (y : Point d) : |Rσ y - R y| ≤ ε := by
  have hbdd : BddAbove (Set.range fun z => |Rσ z - R z|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨z, rfl⟩
    apply abs_le.mpr
    constructor <;> have := hσ z <;> have := hR z <;> linarith
  exact (le_csSup hbdd (Set.mem_range_self y)).trans huniform

/-- A fixed-rank MUSIC correlation takes values in `[0,1]`. -/
theorem rankNoiseSpaceCorrelation_unitBounds
    {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [Nonempty ι]
    (frequency : ι → Point d) (A : Matrix ι κ ℂ)
    (n : ℕ) (y : Point d) :
    0 ≤ rankNoiseSpaceCorrelation frequency A n y ∧
      rankNoiseSpaceCorrelation frequency A n y ≤ 1 := by
  constructor
  · exact norm_nonneg _
  · unfold rankNoiseSpaceCorrelation
    calc
      ‖(trailingLeftSingularSubspace A n).starProjection
          (toLp 2 (normalizedSteering frequency y))‖ ≤
          ‖toLp 2 (normalizedSteering frequency y)‖ :=
        (trailingLeftSingularSubspace A n).norm_starProjection_apply_le _
      _ = 1 := norm_normalizedSteering frequency y

/-- The noiseless GHM signal space contains every normalized source steering
vector. The column factor gives rank `n`, so its range equals the row-factor
range. -/
theorem ghm_source_normalizedSteering_mem_signalRange
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rowFrequency : ι → Point d) (columnFrequency : κ → Point d)
    (node : Fin n → Point d) (a : Fin n → ℂ)
    (hfull₁ : HasFullColumnRank
      (generalizedVandermonde rowFrequency node))
    (hrank :
      (generalizedVandermonde rowFrequency node *
        Matrix.diagonal a *
        Matrix.transpose (generalizedVandermonde columnFrequency node)).rank = n)
    (j : Fin n) :
    toLp 2 (normalizedSteering rowFrequency (node j)) ∈
      (generalizedVandermonde rowFrequency node *
        Matrix.diagonal a *
        Matrix.transpose (generalizedVandermonde columnFrequency node)).toEuclideanLin.range := by
  let V₁ := generalizedVandermonde rowFrequency node
  let V₂ := generalizedVandermonde columnFrequency node
  let A₀ := V₁ * Matrix.diagonal a * Matrix.transpose V₂
  have hsubset : A₀.toEuclideanLin.range ≤ V₁.toEuclideanLin.range := by
    intro z hz
    obtain ⟨x, rfl⟩ := hz
    refine ⟨(Matrix.diagonal a * Matrix.transpose V₂).toEuclideanLin x, ?_⟩
    simp [A₀, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have hVdim : Module.finrank ℂ V₁.toEuclideanLin.range = n := by
    rw [LinearMap.finrank_range_of_inj
      (toEuclideanLin_injective_of_fullColumnRank V₁ hfull₁)]
    simp
  have hAdim : Module.finrank ℂ A₀.toEuclideanLin.range = n := by
    change Module.finrank ℂ (LinearMap.range
      ((Matrix.toLin (EuclideanSpace.basisFun κ ℂ).toBasis
        (EuclideanSpace.basisFun ι ℂ).toBasis) A₀)) = n
    rw [← A₀.rank_eq_finrank_range_toLin
      (EuclideanSpace.basisFun ι ℂ).toBasis
      (EuclideanSpace.basisFun κ ℂ).toBasis]
    exact hrank
  have hEq : A₀.toEuclideanLin.range = V₁.toEuclideanLin.range :=
    Submodule.eq_of_le_of_finrank_eq hsubset (hAdim.trans hVdim.symm)
  have hsteer :
      toLp 2 (steeringVector rowFrequency (node j)) ∈ V₁.toEuclideanLin.range := by
    refine ⟨toLp 2 (Pi.single j (1 : ℂ)), ?_⟩
    ext i
    simp [V₁, Matrix.toLpLin_apply, generalizedVandermonde]
  have hnormalized := V₁.toEuclideanLin.range.smul_mem
    ((‖toLp 2 (steeringVector rowFrequency (node j))‖ : ℂ)⁻¹) hsteer
  have hnormal : toLp 2 (normalizedSteering rowFrequency (node j)) ∈
      V₁.toEuclideanLin.range := by
    simpa [normalizedSteering] using hnormalized
  rw [hEq]
  exact hnormal

/-- Every true source is a zero of the exact GHM-MUSIC correlation. -/
theorem ghm_source_correlation_eq_zero
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rowFrequency : ι → Point d) (columnFrequency : κ → Point d)
    (μ : AtomicMeasure d n) (a : Fin n → ℂ)
    (hn : 0 < n) (hM₁ : n < Fintype.card ι)
    (ha : ∀ j, minAmplitude μ hn ≤ ‖a j‖)
    (hfull₁ : HasFullColumnRank
      (generalizedVandermonde rowFrequency μ.node))
    (hfull₂ : HasFullColumnRank
      (generalizedVandermonde columnFrequency μ.node))
    (j : Fin n) :
    rankNoiseSpaceCorrelation rowFrequency
      (generalizedVandermonde rowFrequency μ.node *
        Matrix.diagonal a *
        Matrix.transpose (generalizedVandermonde columnFrequency μ.node))
      n (μ.node j) = 0 := by
  let A₀ := generalizedVandermonde rowFrequency μ.node *
    Matrix.diagonal a *
    Matrix.transpose (generalizedVandermonde columnFrequency μ.node)
  have hrank : A₀.rank = n :=
    vandermondeFactor_rank rowFrequency columnFrequency μ.node a
      (minAmplitude μ hn) hn (minAmplitude_pos μ hn) ha hfull₁ hfull₂
  exact (rankNoiseSpaceCorrelation_eq_zero_iff_mem_signalSpace
    rowFrequency A₀ n hM₁ hrank (μ.node j)).2
    (ghm_source_normalizedSteering_mem_signalRange rowFrequency
      columnFrequency μ.node a hfull₁ hrank j)

/-- The manuscript's location estimate follows from the GHM residual bound,
quantitative growth, and a separated selection no worse than the true tuple. -/
theorem ghmMUSIC_location_stability
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rowFrequency : ι → Point d)
    (columnFrequency : κ → Point d)
    (μ : AtomicMeasure d n) (a : Fin n → ℂ)
    (E : Matrix ι κ ℂ) (K : Set (Point d))
    (estimate : Fin n → Point d) (Δ c : ℝ)
    (hn : 0 < n) (hM₁ : n < Fintype.card ι)
    (hM₂ : n ≤ Fintype.card κ)
    (ha : ∀ j, minAmplitude μ hn ≤ ‖a j‖)
    (hfull₁ : HasFullColumnRank
      (generalizedVandermonde rowFrequency μ.node))
    (hfull₂ : HasFullColumnRank
      (generalizedVandermonde columnFrequency μ.node))
    (hsmallMatrix :
      2 * matrixSpectralNorm E <
        musicSignalGap rowFrequency columnFrequency μ hn)
    (hc : 0 < c)
    (hsmallLocation :
      2 * matrixSpectralNorm E /
          musicSignalGap rowFrequency columnFrequency μ hn < c * Δ / 8)
    (hnodeK : ∀ j, μ.node j ∈ K)
    (hestimateK : ∀ i, estimate i ∈ K)
    (hgrowth : ∀ y ∈ K,
      c * min (Δ / 4) (finiteEuclideanSourceDistance hn μ.node y) ≤
        rankNoiseSpaceCorrelation rowFrequency
          (generalizedVandermonde rowFrequency μ.node *
            Matrix.diagonal a *
            Matrix.transpose (generalizedVandermonde columnFrequency μ.node))
          n y)
    (hestimateSeparated : ∀ i k, i ≠ k →
      Δ / 2 ≤ pointEuclideanDistance (estimate i) (estimate k))
    (hcomparison :
      (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
        (fun i => rankNoiseSpaceCorrelation rowFrequency
          (generalizedVandermonde rowFrequency μ.node *
            Matrix.diagonal a *
            Matrix.transpose (generalizedVandermonde columnFrequency μ.node) + E)
          n (estimate i)) ≤
      (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
        (fun j => rankNoiseSpaceCorrelation rowFrequency
          (generalizedVandermonde rowFrequency μ.node *
            Matrix.diagonal a *
            Matrix.transpose (generalizedVandermonde columnFrequency μ.node) + E)
          n (μ.node j))) :
    ∃ e : Equiv.Perm (Fin n), ∀ i,
      pointEuclideanDistance (estimate i) (μ.node (e i)) ≤
        4 * matrixSpectralNorm E /
          (c * musicSignalGap rowFrequency columnFrequency μ hn) := by
  let A₀ :=
    generalizedVandermonde rowFrequency μ.node *
      Matrix.diagonal a *
      Matrix.transpose (generalizedVandermonde columnFrequency μ.node)
  let ε := 2 * matrixSpectralNorm E /
    musicSignalGap rowFrequency columnFrequency μ hn
  have hcard : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  letI : Nonempty ι := hcard
  have huniform := ghmMUSIC_correlation_stability rowFrequency columnFrequency
    μ a E hn hM₁ hM₂ ha hfull₁ hfull₂ hsmallMatrix
  have hpert : ∀ y ∈ K,
      |rankNoiseSpaceCorrelation rowFrequency (A₀ + E) n y -
        rankNoiseSpaceCorrelation rowFrequency A₀ n y| ≤ ε := by
    intro y _
    exact correlationUniformDistance_pointwise_of_unitBounds
      _ _ ε
      (rankNoiseSpaceCorrelation_unitBounds rowFrequency (A₀ + E) n)
      (rankNoiseSpaceCorrelation_unitBounds rowFrequency A₀ n)
      huniform y
  have hzero : ∀ j,
      rankNoiseSpaceCorrelation rowFrequency A₀ n (μ.node j) = 0 := by
    intro j
    exact ghm_source_correlation_eq_zero rowFrequency columnFrequency
      μ a hn hM₁ ha hfull₁ hfull₂ j
  obtain ⟨e, he⟩ := separatedMUSIC_location_matching_euclidean hn μ.node estimate K
    (rankNoiseSpaceCorrelation rowFrequency A₀ n)
    (rankNoiseSpaceCorrelation rowFrequency (A₀ + E) n)
    Δ c ε hc hsmallLocation hnodeK hestimateK hzero hpert
    hgrowth hestimateSeparated hcomparison
  have hgapPos : 0 < musicSignalGap rowFrequency columnFrequency μ hn := by
    unfold musicSignalGap
    exact mul_pos
      (mul_pos (minAmplitude_pos μ hn)
        (lastSingularValue_pos_of_fullColumnRank _ hn hfull₁))
      (lastSingularValue_pos_of_fullColumnRank _ hn hfull₂)
  refine ⟨e, fun i => ?_⟩
  convert he i using 1
  dsimp [ε]
  field_simp [hc.ne', hgapPos.ne']; ring

end
end NumDetect
end LeanNumDetect
