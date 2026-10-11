import General.MatrixAnalysis.GreedyBasisBounds
import General.Probability.GreedyCyclePotential
import General.Probability.GreedyFrameSampling

/-! The actual greedy accepted-prefix process for a finite thick frame.
Completed bases and the current prefix are retained as matrix energy, so every
transition is a deterministic function of the sampled row. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Matrix WithLp
open scoped BigOperators InnerProductSpace ComplexOrder

namespace LeanNumDetect.GreedyFrameProcess

open FiniteMatrixSampling GreedyBasisBounds TranslatedBasisThickness TraceExponential
  FrameMatrixBounds

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Vector (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- A partial accepted basis and the energy of the completed bases. -/
structure State (n : ℕ) (τ M b : ℝ) where
  r : ℕ
  r_lt : r < n
  current : Fin r → Vector n
  separated : GreedySeparated current τ
  norm_le : ∀ i, ‖current i‖ ≤ M
  completed : ℕ
  completedGram : Square n
  completed_posSemidef : completedGram.PosSemidef
  completed_lower : ∀ x : Vector n,
    (completed : ℝ) * b * ‖x‖ ^ 2 ≤ quadratic completedGram x

def storedGram {n : ℕ} {τ M b : ℝ} (s : State n τ M b) : Square n :=
  s.completedGram + gramFamily s.current

def accept {n : ℕ} {τ M b : ℝ} (s : State n τ M b) (v : Vector n) : Prop :=
  FarFromSubspace v (Submodule.span ℂ (Set.range s.current)) τ

def initial {n : ℕ} (hn : 0 < n) (τ M b : ℝ) : State n τ M b where
  r := 0
  r_lt := hn
  current := Fin.elim0
  separated := by intro i; exact Fin.elim0 i
  norm_le := by intro i; exact Fin.elim0 i
  completed := 0
  completedGram := 0
  completed_posSemidef := Matrix.PosSemidef.zero
  completed_lower := by intro x; simp [quadratic]

theorem storedGram_initial {n : ℕ} (hn : 0 < n) (τ M b : ℝ) :
    storedGram (initial hn τ M b) = 0 := by
  simp [storedGram, initial, gramFamily]

/-- Acceptance extends the current basis or completes it and starts an empty prefix. -/
def next {n : ℕ} {τ M b : ℝ}
    (hfull : ∀ {r : ℕ} (v : Fin r → Vector n), r = n →
      GreedySeparated v τ → (∀ i, ‖v i‖ ≤ M) →
      ∀ x : Vector n, b * ‖x‖ ^ 2 ≤ quadratic (gramFamily v) x)
    (s : State n τ M b) (v : Vector n) (hv : ‖v‖ ≤ M) : State n τ M b := by
  classical
  by_cases ha : accept s v
  · let w : Fin (s.r + 1) → Vector n := Fin.snoc s.current v
    have hw : GreedySeparated w τ := s.separated.snoc ha
    have hnorm : ∀ i, ‖w i‖ ≤ M := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [w] using hv
      · simpa [w] using s.norm_le j
    by_cases hr : s.r + 1 < n
    · exact {
        r := s.r + 1
        r_lt := hr
        current := w
        separated := hw
        norm_le := hnorm
        completed := s.completed
        completedGram := s.completedGram
        completed_posSemidef := s.completed_posSemidef
        completed_lower := s.completed_lower }
    · have heq : s.r + 1 = n := by have h := s.r_lt; omega
      exact {
        r := 0
        r_lt := by omega
        current := Fin.elim0
        separated := by intro i; exact Fin.elim0 i
        norm_le := by intro i; exact Fin.elim0 i
        completed := s.completed + 1
        completedGram := s.completedGram + gramFamily w
        completed_posSemidef := s.completed_posSemidef.add (gramFamily_posSemidef w)
        completed_lower := by
          intro x
          rw [quadratic_add]
          have h₁ := s.completed_lower x
          have h₂ := hfull w heq hw hnorm x
          push_cast
          nlinarith }
  · exact s

theorem next_potential {n : ℕ} {τ M b : ℝ}
    (hfull : ∀ {r : ℕ} (v : Fin r → Vector n), r = n →
      GreedySeparated v τ → (∀ i, ‖v i‖ ≤ M) →
      ∀ x : Vector n, b * ‖x‖ ^ 2 ≤ quadratic (gramFamily v) x)
    (s : State n τ M b) (v : Vector n) (hv : ‖v‖ ≤ M) :
    greedyCyclePotential n (next hfull s v hv).completed (next hfull s v hv).r =
      if accept s v then
        greedyCyclePotential n s.completed s.r - greedyCycleDrop n s.completed
      else greedyCyclePotential n s.completed s.r := by
  classical
  by_cases ha : accept s v
  · by_cases hr : s.r + 1 < n
    · simpa [next, ha, hr] using greedyCyclePotential_accept n s.completed s.r
    · have heq : s.r + 1 = n := by have h := s.r_lt; omega
      simpa [next, ha, hr] using greedyCyclePotential_reset (J := s.completed) heq
  · simp [next, ha]

theorem storedGram_next_of_accept {n : ℕ} {τ M b : ℝ}
    (hfull : ∀ {r : ℕ} (v : Fin r → Vector n), r = n →
      GreedySeparated v τ → (∀ i, ‖v i‖ ≤ M) →
      ∀ x : Vector n, b * ‖x‖ ^ 2 ≤ quadratic (gramFamily v) x)
    (s : State n τ M b) (v : Vector n) (hv : ‖v‖ ≤ M) (ha : accept s v) :
    storedGram (next hfull s v hv) =
      storedGram s + framePopulation (fun _ : Fin 1 => v) 0 := by
  classical
  by_cases hr : s.r + 1 < n
  · simp only [next, dif_pos ha, dif_pos hr]
    simp only [storedGram, gramFamily_snoc, add_assoc]
  · simp only [next, dif_pos ha, dif_neg hr]
    simp only [storedGram, gramFamily_snoc]
    simp [gramFamily, add_assoc]

theorem quadratic_storedGram_next_le {n : ℕ} {τ M b : ℝ}
    (hfull : ∀ {r : ℕ} (v : Fin r → Vector n), r = n →
      GreedySeparated v τ → (∀ i, ‖v i‖ ≤ M) →
      ∀ x : Vector n, b * ‖x‖ ^ 2 ≤ quadratic (gramFamily v) x)
    (s : State n τ M b) (v : Vector n) (hv : ‖v‖ ≤ M) (x : Vector n) :
    quadratic (storedGram (next hfull s v hv)) x ≤
      quadratic (storedGram s) x + quadratic (framePopulation (fun _ : Fin 1 => v) 0) x := by
  classical
  by_cases ha : accept s v
  · rw [storedGram_next_of_accept hfull s v hv ha, quadratic_add]
  · simp only [next, ha, dite_false]
    exact le_add_of_nonneg_right (quadratic_nonneg
      (framePopulation_posSemidef (fun _ : Fin 1 => v) 0) x)

theorem acceptance_probability {N n : ℕ} {τ M b : ℝ}
    (hτ : 0 < τ) (f : Fin N → Vector n)
    (hthick : ∀ U : Submodule ℂ (Vector n),
      ((n : ℝ) - Module.finrank ℂ U) / (2 * n) ≤
        probability (fun k => FarFromSubspace (f k) U τ))
    (s : State n τ M b) :
    ((n : ℝ) - s.r) / (2 * n) ≤ probability (fun k => accept s (f k)) := by
  simpa only [accept, finrank_span_of_greedySeparated hτ s.separated] using
    hthick (Submodule.span ℂ (Set.range s.current))

theorem quadratic_storedGram_run_le {N n : ℕ} {τ M b : ℝ}
    (hfull : ∀ {r : ℕ} (v : Fin r → Vector n), r = n →
      GreedySeparated v τ → (∀ i, ‖v i‖ ≤ M) →
      ∀ x : Vector n, b * ‖x‖ ^ 2 ≤ quadratic (gramFamily v) x)
    (f : Fin N → Vector n) (hf : ∀ k, ‖f k‖ ≤ M)
    (m : ℕ) (ω : Fin m → Fin N) (s : State n τ M b) (x : Vector n) :
    quadratic (storedGram (greedyRun (fun s k => next hfull s (f k) (hf k)) m ω s)) x ≤
      quadratic (storedGram s) x + quadratic (∑ i, framePopulation f (ω i)) x := by
  induction m generalizing s with
  | zero => simp [greedyRun, quadratic]
  | succ m ih =>
    have hrun := ih (fun i => ω i.succ) (next hfull s (f (ω 0)) (hf (ω 0)))
    have hnext := quadratic_storedGram_next_le hfull s (f (ω 0)) (hf (ω 0)) x
    have hrow : framePopulation (fun _ : Fin 1 => f (ω 0)) 0 = framePopulation f (ω 0) := by
      ext a b
      rfl
    rw [hrow] at hnext
    change quadratic (storedGram (greedyRun (fun s k => next hfull s (f k) (hf k)) m
      (fun i => ω i.succ) (next hfull s (f (ω 0)) (hf (ω 0))))) x ≤ _
    rw [Fin.sum_univ_succ, quadratic_add]
    linarith

end
end LeanNumDetect.GreedyFrameProcess
