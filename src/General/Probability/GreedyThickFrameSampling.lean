import General.Probability.GreedyFrameProcess
import General.MatrixAnalysis.GreedyCycleTraceBounds

/-!
Uniform sampling of a finite frame with codimension-sensitive subspace
thickness. The accepted-prefix process, its Gram energy, scalar potential,
trace-exponential moment, and transfer to sampling without replacement are
assembled here. The public sampling theorem has only geometric and sample
budget hypotheses; no moment or algorithmic invariant is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder

namespace LeanNumDetect.FiniteMatrixSampling

open GreedyBasisBounds GreedyFrameProcess TranslatedBasisThickness TraceExponential
  FrameMatrixBounds

noncomputable section

/-- The actual greedy accepted-prefix process gives the iid trace moment from
subspace thickness. Its auxiliary choices are deterministic functions of the
sampled rows and do not modify their uniform law. -/
theorem greedy_thick_frame_iid_trace_moment {N n : ℕ} {τ M : ℝ}
    (hN : 0 < N) (hn : 0 < n) (hτ : 0 < τ) (hτM : τ ≤ M)
    (f : Fin N → EuclideanSpace ℂ (Fin n)) (hNorm : ∀ k, ‖f k‖ ≤ M)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      ((n : ℝ) - Module.finrank ℂ U) / (2 * n) ≤
        probability (fun k => FarFromSubspace (f k) U τ)) (m : ℕ) :
    finiteAverage (fun ω : Fin m → Fin N =>
      traceExp ((-greedyLaplaceParameter n (greedyBasisEnergy n τ M)) •
        ∑ i, framePopulation f (ω i))) ≤
      (n : ℝ) * greedyCycleDecay n ^ m := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let η := greedyBasisEnergy n τ M
  have hη : 0 < η := greedyBasisEnergy_pos hn hτ (hτ.trans_le hτM)
  let t := greedyLaplaceParameter n η
  have ht : 0 < t := greedyLaplaceParameter_pos hn hη
  let full : ∀ {r : ℕ} (v : Fin r → Vector n), r = n →
      GreedySeparated v τ → (∀ i, ‖v i‖ ≤ M) →
      ∀ x : Vector n, η * ‖x‖ ^ 2 ≤ quadratic (gramFamily v) x := by
    intro r v hr hv hnorm x
    subst r
    exact greedy_full_energy_lower hn hτ hτM v hv hnorm x
  let s0 : State n τ M η := initial hn τ M η
  let transition : State n τ M η → Fin N → State n τ M η :=
    fun s k => next full s (f k) (hNorm k)
  let potential : State n τ M η → ℝ :=
    fun s => greedyCyclePotential n s.completed s.r
  have hstep (s : State n τ M η) :
      finiteAverage (fun k => potential (transition s k)) ≤ greedyCycleDecay n * potential s := by
    exact finiteAverage_greedyCycle_step hn
      (fun s : State n τ M η => s.completed) (fun s => s.r) (fun s => s.r_lt)
      (fun s k => accept s (f k)) transition
      (acceptance_probability hτ f hthick)
      (fun s k => next_potential full s (f k) (hNorm k)) s
  have hinitial : potential s0 = 1 := greedyCyclePotential_initial n
  apply traceExp_iid_sum_le_of_greedyPotential hn (framePopulation f) transition potential s0
    hstep hinitial
  intro ω
  let s : State n τ M η := greedyRun transition m ω s0
  let S : Square n := ∑ i, framePopulation f (ω i)
  let U := Submodule.span ℂ (Set.range s.current)
  have hS : S.PosSemidef :=
    Matrix.posSemidef_sum _ (fun i _ => framePopulation_posSemidef f (ω i))
  have hdim : Module.finrank ℂ U = s.r := finrank_span_of_greedySeparated hτ s.separated
  have hstored (x : Vector n) : quadratic (storedGram s) x ≤ quadratic S x := by
    have h := quadratic_storedGram_run_le full f hNorm m ω s0 x
    have h0 : quadratic (0 : Square n) x = 0 := by simp [quadratic]
    simpa only [s0, storedGram_initial, h0, zero_add] using h
  have hfloor (x : Vector n) : (s.completed : ℝ) * η * ‖x‖ ^ 2 ≤ quadratic S x := by
    apply le_trans _ (hstored x)
    rw [storedGram, quadratic_add]
    exact (s.completed_lower x).trans
      (le_add_of_nonneg_right (quadratic_nonneg (gramFamily_posSemidef s.current) x))
  have hsub (x : Vector n) (hx : x ∈ U) :
      ((s.completed : ℝ) + 1) * η * ‖x‖ ^ 2 ≤ quadratic S x := by
    apply le_trans _ (hstored x)
    rw [storedGram, quadratic_add]
    have hcurrent := greedy_on_span_energy_lower hn hτ hτM s.r_lt.le s.current
      s.separated s.norm_le x hx
    change η * ‖x‖ ^ 2 ≤ quadratic (gramFamily s.current) x at hcurrent
    have hcomplete := s.completed_lower x
    nlinarith
  calc
    _ ≤ Real.exp (-t * (s.completed : ℝ) * η) *
        ((n : ℝ) - s.r + s.r * Real.exp (-t * η)) :=
      traceExp_neg_smul_le_cycle_factor hS.isHermitian U hdim ht.le hη.le hfloor hsub
    _ = (n : ℝ) * greedyCyclePotential n s.completed s.r :=
      greedy_spectral_factor_eq_potential hη

/-- The unconditional lower tail for the sampled mean, stated directly in
unit-vector Rayleigh values. This is the generic frame tail in the manuscript. -/
theorem sampleMean_greedy_thick_frame_lower_tail {N n m : ℕ} {τ M : ℝ}
    (hN : 0 < N) (hn : 0 < n) (hτ : 0 < τ) (hτM : τ ≤ M)
    (f : Fin N → EuclideanSpace ℂ (Fin n)) (hNorm : ∀ k, ‖f k‖ ≤ M)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      ((n : ℝ) - Module.finrank ℂ U) / (2 * n) ≤
        probability (fun k => FarFromSubspace (f k) U τ))
    (hm : 1 ≤ m) (hmN : m ≤ N) :
    probability (fun Ω : Sample N m => ∃ x : EuclideanSpace ℂ (Fin n),
      ‖x‖ = 1 ∧ quadratic (sampleMean (framePopulation f) Ω) x ≤
        greedySamplingThreshold n (greedyBasisEnergy n τ M)) ≤
      (n : ℝ) * Real.exp (-(m : ℝ) / (3 * n)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  apply le_trans (probability_mono (P := fun Ω : Sample N m =>
    ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧
      quadratic (sampleMean (framePopulation f) Ω) x ≤
        greedySamplingThreshold n (greedyBasisEnergy n τ M))
    (Q := fun Ω : Sample N m => ∃ x : EuclideanSpace ℂ (Fin n),
      ‖x‖ = 1 ∧ quadratic (sampleSum (framePopulation f) Ω) x ≤
        (m : ℝ) * greedySamplingThreshold n (greedyBasisEnergy n τ M)) (by
      intro Ω hΩ
      obtain ⟨x, hx, hq⟩ := hΩ
      refine ⟨x, hx, ?_⟩
      have he : quadratic (sampleMean (framePopulation f) Ω) x =
          (m : ℝ)⁻¹ * quadratic (sampleSum (framePopulation f) Ω) x := by
        simpa only [sampleMean, Complex.ofReal_inv, Complex.ofReal_natCast] using
          quadratic_smul_matrix (sampleSum (framePopulation f) Ω) (m : ℝ)⁻¹ x
      rw [he] at hq
      exact (inv_mul_le_iff₀ hmpos).mp hq))
  exact sampleSum_greedy_lower_tail hn hmN (framePopulation f)
    (framePopulation_posSemidef f) (greedyBasisEnergy_pos hn hτ (hτ.trans_le hτM))
    (greedy_thick_frame_iid_trace_moment hN hn hτ hτM f hNorm hthick m)

/-- Uniform sampling without replacement preserves a fixed positive amount
of frame energy with sample budget `3 n log(n / epsilon)`. -/
theorem sampleMean_greedy_thick_frame_probability {N n m : ℕ} {τ M ε : ℝ}
    (hN : 0 < N) (hn : 0 < n) (hτ : 0 < τ) (hτM : τ ≤ M)
    (f : Fin N → EuclideanSpace ℂ (Fin n)) (hNorm : ∀ k, ‖f k‖ ≤ M)
    (hthick : ∀ U : Submodule ℂ (EuclideanSpace ℂ (Fin n)),
      ((n : ℝ) - Module.finrank ℂ U) / (2 * n) ≤
        probability (fun k => FarFromSubspace (f k) U τ))
    (hm : 1 ≤ m) (hmN : m ≤ N) (hε : 0 < ε)
    (hsample : 3 * (n : ℝ) * Real.log ((n : ℝ) / ε) ≤ (m : ℝ)) :
    1 - ε ≤ probability (fun Ω : Sample N m => ∀ x : EuclideanSpace ℂ (Fin n),
      greedySamplingThreshold n (greedyBasisEnergy n τ M) * ‖x‖ ^ 2 ≤
        quadratic (sampleMean (framePopulation f) Ω) x) := by
  exact sampleMean_greedy_lower_bound_probability_of_sample_budget hn hm hmN
    (framePopulation f) (framePopulation_posSemidef f)
    (greedyBasisEnergy_pos hn hτ (hτ.trans_le hτM)) hε
    (greedy_thick_frame_iid_trace_moment hN hn hτ hτM f hNorm hthick m) hsample

end

end LeanNumDetect.FiniteMatrixSampling
