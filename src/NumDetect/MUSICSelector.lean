import NumDetect.MUSICLocation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open WithLp

namespace LeanNumDetect
namespace NumDetect

noncomputable section

/-- Compactness and continuity provide a minimax selection among separated
finite tuples. -/
theorem exists_separatedMinimaxSelector
    {α : Type*} [PseudoMetricSpace α] {n : ℕ}
    (hn : 0 < n) (node : Fin n → α) (K : Set α) (Rσ : α → ℝ)
    (Δ : ℝ) (hK : IsCompact K)
    (hnodeK : ∀ j, node j ∈ K)
    (hnodeSeparated : ∀ i k, i ≠ k → Δ / 2 ≤ dist (node i) (node k))
    (hRσ : ContinuousOn Rσ K) :
    ∃ estimate : Fin n → α,
      (∀ i, estimate i ∈ K) ∧
      (∀ i k, i ≠ k → Δ / 2 ≤ dist (estimate i) (estimate k)) ∧
      ∀ z : Fin n → α,
        (∀ i, z i ∈ K) →
        (∀ i k, i ≠ k → Δ / 2 ≤ dist (z i) (z k)) →
        (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
          (fun i => Rσ (estimate i)) ≤
        (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
          (fun j => Rσ (z j)) := by
  let Sep : Set (Fin n → α) :=
    {z | ∀ i k, i ≠ k → Δ / 2 ≤ dist (z i) (z k)}
  let Feasible : Set (Fin n → α) :=
    {z | (∀ i, z i ∈ K) ∧ z ∈ Sep}
  let objective : (Fin n → α) → ℝ := fun z =>
    (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
      (fun i => Rσ (z i))
  have hsepClosed : IsClosed Sep := by
    dsimp [Sep]
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro k
    by_cases hik : i = k
    · simp [hik]
    · simpa [hik] using
        (isClosed_le continuous_const
          (by fun_prop : Continuous fun z : Fin n → α => dist (z i) (z k)))
  have hpi : IsCompact {z : Fin n → α | ∀ i, z i ∈ K} :=
    isCompact_pi_infinite (fun _ => hK)
  have hfeasible : IsCompact Feasible := by
    have heq : Feasible = {z : Fin n → α | ∀ i, z i ∈ K} ∩ Sep := by
      ext z
      rfl
    rw [heq]
    exact hpi.inter_right hsepClosed
  have hnode : node ∈ Feasible := by
    exact ⟨hnodeK, hnodeSeparated⟩
  have hobj : ContinuousOn objective Feasible := by
    apply ContinuousOn.finset_sup'_apply (fin_univ_nonempty hn)
    intro i _
    exact hRσ.comp (continuous_apply i).continuousOn
      (fun z hz => hz.1 i)
  obtain ⟨estimate, hest, hmin⟩ :=
    hfeasible.exists_isMinOn ⟨node, hnode⟩ hobj
  exact ⟨estimate, hest.1, hest.2,
    fun z hzK hzSep => hmin ⟨hzK, hzSep⟩⟩

/-- The same minimax selector in the manuscript's Euclidean coordinate norm. -/
theorem exists_separatedMinimaxSelector_euclidean
    {d n : ℕ} (hn : 0 < n) (node : Fin n → Point d)
    (K : Set (Point d)) (Rσ : Point d → ℝ) (Δ : ℝ)
    (hK : IsCompact K) (hnodeK : ∀ j, node j ∈ K)
    (hnodeSeparated : ∀ i k, i ≠ k →
      Δ / 2 ≤ pointEuclideanDistance (node i) (node k))
    (hRσ : ContinuousOn Rσ K) :
    ∃ estimate : Fin n → Point d,
      (∀ i, estimate i ∈ K) ∧
      (∀ i k, i ≠ k →
        Δ / 2 ≤ pointEuclideanDistance (estimate i) (estimate k)) ∧
      ∀ z : Fin n → Point d,
        (∀ i, z i ∈ K) →
        (∀ i k, i ≠ k →
          Δ / 2 ≤ pointEuclideanDistance (z i) (z k)) →
        (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
          (fun i => Rσ (estimate i)) ≤
        (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
          (fun j => Rσ (z j)) := by
  let nodeE : Fin n → EuclideanSpace ℝ (Fin d) := fun j => toLp 2 (node j)
  let KE : Set (EuclideanSpace ℝ (Fin d)) := (toLp 2) '' K
  let RσE : EuclideanSpace ℝ (Fin d) → ℝ := fun z => Rσ (ofLp z)
  have hKE : IsCompact KE := hK.image (PiLp.continuous_toLp 2 _)
  have hnodeKE : ∀ j, nodeE j ∈ KE := by
    intro j
    exact ⟨node j, hnodeK j, rfl⟩
  have hsepE : ∀ i k, i ≠ k → Δ / 2 ≤ dist (nodeE i) (nodeE k) :=
    hnodeSeparated
  have hRσE : ContinuousOn RσE KE := by
    apply hRσ.comp (PiLp.continuous_ofLp 2 _).continuousOn
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    simpa using hy
  obtain ⟨estimateE, hestK, hsep, hmin⟩ :=
    exists_separatedMinimaxSelector hn nodeE KE RσE Δ hKE
      hnodeKE hsepE hRσE
  let estimate : Fin n → Point d := fun i => ofLp (estimateE i)
  refine ⟨estimate, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨y, hy, heq⟩ := hestK i
    change ofLp (estimateE i) ∈ K
    rw [← heq]
    simpa using hy
  · exact hsep
  · intro z hzK hzSep
    let zE : Fin n → EuclideanSpace ℝ (Fin d) := fun j => toLp 2 (z j)
    have hzKE : ∀ j, zE j ∈ KE := by
      intro j
      exact ⟨z j, hzK j, rfl⟩
    have hzSepE : ∀ i k, i ≠ k → Δ / 2 ≤ dist (zE i) (zE k) :=
      hzSep
    exact hmin zE hzKE hzSepE

/-- The finite Fourier steering vector is continuous in the location. -/
theorem steeringVector_continuous
    {d : ℕ} {ι : Type*} (frequency : ι → Point d) :
    Continuous (steeringVector frequency) := by
  apply continuous_pi
  intro i
  simp only [steeringVector, dot]
  fun_prop

/-- The MUSIC correlation is continuous for every fixed data matrix and
frequency family. -/
theorem rankNoiseSpaceCorrelation_continuous
    {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [Nonempty ι]
    (frequency : ι → Point d) (A : Matrix ι κ ℂ) (n : ℕ) :
    Continuous (rankNoiseSpaceCorrelation frequency A n) := by
  have hsteer : Continuous (steeringVector frequency) :=
    steeringVector_continuous frequency
  have hsteerLp : Continuous
      (fun y => toLp 2 (steeringVector frequency y)) :=
    (PiLp.continuous_toLp 2 _).comp hsteer
  have hnorm : Continuous
      (fun y => (‖toLp 2 (steeringVector frequency y)‖ : ℂ)) := by
    fun_prop
  have hnonzero (y : Point d) :
      (‖toLp 2 (steeringVector frequency y)‖ : ℂ) ≠ 0 := by
    have hs : ‖toLp 2 (steeringVector frequency y)‖ ≠ 0 := by
      intro hz
      have hv := norm_eq_zero.mp hz
      let i : ι := Classical.choice inferInstance
      have hi := congrArg (fun v => (ofLp v) i) hv
      simp [steeringVector] at hi
    exact_mod_cast hs
  have hscalar : Continuous
      (fun y => ((‖toLp 2 (steeringVector frequency y)‖ : ℂ)⁻¹)) :=
    hnorm.inv₀ hnonzero
  have hnormalized : Continuous (normalizedSteering frequency) := by
    exact hscalar.smul hsteer
  have hnormalizedLp : Continuous
      (fun y => toLp 2 (normalizedSteering frequency y)) :=
    (PiLp.continuous_toLp 2 _).comp hnormalized
  unfold rankNoiseSpaceCorrelation
  exact continuous_norm.comp
    ((trailingLeftSingularSubspace A n).starProjection.continuous.comp hnormalizedLp)

/-- On a compact search region, the separated minimax selector exists and
obeys the GHM-MUSIC location bound. -/
theorem exists_ghmMUSIC_location_stability
    {d n : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rowFrequency : ι → Point d)
    (columnFrequency : κ → Point d)
    (μ : AtomicMeasure d n) (a : Fin n → ℂ)
    (E : Matrix ι κ ℂ) (K : Set (Point d)) (Δ c : ℝ)
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
    (hc : 0 < c) (hΔ : 0 < Δ)
    (hsmallLocation :
      2 * matrixSpectralNorm E /
          musicSignalGap rowFrequency columnFrequency μ hn < c * Δ / 8)
    (hK : IsCompact K) (hnodeK : ∀ j, μ.node j ∈ K)
    (hnodeSeparated : ∀ i k, i ≠ k →
      Δ ≤ pointEuclideanDistance (μ.node i) (μ.node k))
    (hgrowth : ∀ y ∈ K,
      c * min (Δ / 4) (finiteEuclideanSourceDistance hn μ.node y) ≤
        rankNoiseSpaceCorrelation rowFrequency
          (generalizedVandermonde rowFrequency μ.node *
            Matrix.diagonal a *
            Matrix.transpose (generalizedVandermonde columnFrequency μ.node))
          n y) :
    ∃ estimate : Fin n → Point d,
      (∀ i, estimate i ∈ K) ∧
      (∀ i k, i ≠ k →
        Δ / 2 ≤ pointEuclideanDistance (estimate i) (estimate k)) ∧
      (∀ z : Fin n → Point d,
        (∀ i, z i ∈ K) →
        (∀ i k, i ≠ k →
          Δ / 2 ≤ pointEuclideanDistance (z i) (z k)) →
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
            n (z j))) ∧
      ∃ e : Equiv.Perm (Fin n), ∀ i,
        pointEuclideanDistance (estimate i) (μ.node (e i)) ≤
          4 * matrixSpectralNorm E /
            (c * musicSignalGap rowFrequency columnFrequency μ hn) := by
  have hsepHalf : ∀ i k, i ≠ k →
      Δ / 2 ≤ pointEuclideanDistance (μ.node i) (μ.node k) := by
    intro i k hik
    exact (by linarith [hΔ] : Δ / 2 ≤ Δ).trans (hnodeSeparated i k hik)
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hRσ : ContinuousOn
      (rankNoiseSpaceCorrelation rowFrequency
        (generalizedVandermonde rowFrequency μ.node *
          Matrix.diagonal a *
          Matrix.transpose (generalizedVandermonde columnFrequency μ.node) + E)
        n) K :=
    (rankNoiseSpaceCorrelation_continuous rowFrequency _ n).continuousOn
  obtain ⟨estimate, hestK, hsep, hmin⟩ :=
    exists_separatedMinimaxSelector_euclidean hn μ.node K
      (rankNoiseSpaceCorrelation rowFrequency
        (generalizedVandermonde rowFrequency μ.node *
          Matrix.diagonal a *
          Matrix.transpose (generalizedVandermonde columnFrequency μ.node) + E) n)
      Δ hK hnodeK hsepHalf hRσ
  have hcomparison := hmin μ.node hnodeK hsepHalf
  obtain ⟨e, he⟩ := ghmMUSIC_location_stability
    rowFrequency columnFrequency μ a E K estimate Δ c
    hn hM₁ hM₂ ha hfull₁ hfull₂ hsmallMatrix hc hsmallLocation
    hnodeK hestK hgrowth hsep hcomparison
  exact ⟨estimate, hestK, hsep, hmin, e, he⟩

end
end NumDetect
end LeanNumDetect
